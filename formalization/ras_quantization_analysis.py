#!/usr/bin/env python3
"""Numerical companion to the Lean stochastic-quantization formalization.

This script does NOT prove the theorems.  The Lean files carry the symbolic proofs.
This script applies the proved formulas to the RasActivation-Simulator parameter sets
and to the serialized stochastic trajectories shipped with the repository.

It deliberately distinguishes four levels of claim:

1. THEOREM: algebraic identities proved in Lean for the reduced model.
2. REDUCTION: mapping from the full BNGL model to a frozen-SOS-occupancy target model.
3. NUMERICAL CHECK: comparison with the provided SSA trajectories.
4. OPEN THEORY: a full slow/fast stochastic error bound for the BNGL process.

The RoadRunner pickle files store NamedArray objects.  To avoid requiring RoadRunner
just to read the already-generated trajectories, a tiny compatibility class decodes
their raw float64 payloads.
"""

from __future__ import annotations

import csv
import math
import os
import pickle
import sys
import types
from dataclasses import dataclass
from pathlib import Path
from typing import Dict, Iterable, List

import numpy as np

ROOT = Path(__file__).resolve().parents[1]
OUT = Path(__file__).resolve().parent / "generated"
OUT.mkdir(exist_ok=True)


class _NamedArrayCompat:
    """Enough of RoadRunner's NamedArray pickle protocol to recover numeric values."""

    def __new__(cls, *args, **kwargs):
        return super().__new__(cls)

    def __setstate__(self, state):
        self.__dict__.update(state)

    def numpy(self) -> np.ndarray:
        return np.frombuffer(self.array, dtype=np.float64, count=self.dim1)


def _install_roadrunner_pickle_compat() -> None:
    mod = types.ModuleType("roadrunner._roadrunner")
    mod.NamedArray = _NamedArrayCompat
    pkg = types.ModuleType("roadrunner")
    pkg._roadrunner = mod
    sys.modules.setdefault("roadrunner", pkg)
    sys.modules.setdefault("roadrunner._roadrunner", mod)


@dataclass(frozen=True)
class Model:
    name: str
    rho_values: tuple[float, ...]
    kcat1: float
    kcat2: float
    kon_coeff: float       # BNGL Kon = kon_coeff * RhoSOS
    koff_gdp: float
    koff_gtp: float
    ras_total: int = 1000

    def kon(self, rho: float) -> float:
        return self.kon_coeff * rho


MODELS: Dict[str, Model] = {
    "Model1": Model("Model1", (1, 5, 10), 1e-2, 2.5e-3, 7e-8, 5e-3, 5e-4),
    "Model2": Model("Model2", (1, 15, 30), 1e-2, 2.5e-2, 7e-8, 5e-3, 5e-4),
    "Model3": Model("Model3", (1, 5, 10), 1e-2, 2.5e-3, 7e-5, 5.0, 0.5),
}


def p_active(n: int, kcat1: float, kcat2: float) -> float:
    """Frozen-occupancy active fraction of the free Ras target pool."""
    return 0.0 if n == 0 else n * kcat1 / (n * kcat1 + kcat2)


def free_peak(model: Model, n: int) -> float:
    """Lean theorem Ras.freePeak: reduced-model mean free RasGTP at occupancy n."""
    return (model.ras_total - n) * p_active(n, model.kcat1, model.kcat2)


def free_variance(model: Model, n: int) -> float:
    p = p_active(n, model.kcat1, model.kcat2)
    return (model.ras_total - n) * p * (1.0 - p)


def exact_spacing(model: Model, n: int) -> float:
    """Lean theorem Ras.adjacentSpacing_exact, evaluated numerically."""
    a, b, R = model.kcat1, model.kcat2, model.ras_total
    numerator = a * (b * (R - 2 * n - 1) - a * n * (n + 1))
    denominator = (n * a + b) * ((n + 1) * a + b)
    return numerator / denominator


def linear_peak(model: Model, n: int) -> float:
    return n * model.ras_total * model.kcat1 / model.kcat2


def linear_error(model: Model, n: int) -> float:
    """Lean theorem Ras.linearPeak_error_exact, evaluated numerically."""
    a, b, R = model.kcat1, model.kcat2, model.ras_total
    if n == 0:
        return 0.0
    return a * n**2 * (R * a + b) / (b * (n * a + b))


def relaxation_rate(model: Model, n: int) -> float:
    return n * model.kcat1 + model.kcat2


def relaxation_time(model: Model, n: int) -> float:
    return 1.0 / relaxation_rate(model, n)


def persistence_ratio(model: Model, n: int, bound_state: str) -> float:
    """Target relaxation rate / SOS unbinding rate; larger means longer-lived occupancy."""
    koff = model.koff_gtp if bound_state == "GTP" else model.koff_gdp
    return relaxation_rate(model, n) / koff


def tracking_error_after_relaxations(c: float) -> float:
    """Fraction of the initial mean error left after c target relaxation times."""
    return math.exp(-c)


def survive_relaxation_window(model: Model, n: int, bound_state: str, c: float) -> float:
    """Probability an exponential SOS dwell survives for at least c target relaxation times.

    Exact reduced-model identity: exp(-c / Gamma), where Gamma is the
    target-relaxation-rate / SOS-unbinding-rate ratio.
    """
    gamma = persistence_ratio(model, n, bound_state)
    return math.exp(-c / gamma)


def mean_residual_at_dwell_end(model: Model, n: int, bound_state: str) -> float:
    """Mean fraction of old target-state error left when an exponential SOS dwell ends."""
    gamma = persistence_ratio(model, n, bound_state)
    return 1.0 / (1.0 + gamma)


def mean_completed_at_dwell_end(model: Model, n: int, bound_state: str) -> float:
    """Mean fraction of the occupancy-specific mean move completed before unbinding."""
    gamma = persistence_ratio(model, n, bound_state)
    return gamma / (1.0 + gamma)


def dwell_time(model: Model, bound_state: str) -> float:
    koff = model.koff_gtp if bound_state == "GTP" else model.koff_gdp
    return 1.0 / koff


def processivity_at_substrate(model: Model, substrate: float, bound_state: str) -> float:
    """Dimensionless catalytic opportunities per SOS dwell at approximately fixed substrate."""
    koff = model.koff_gtp if bound_state == "GTP" else model.koff_gdp
    return substrate * model.kcat1 / koff


def load_trajectory(model_name: str):
    _install_roadrunner_pickle_compat()
    with open(ROOT / f"{model_name}_traj.pkl", "rb") as f:
        payload = pickle.load(f)
    result = []
    for rho, traj in zip(payload["pval"], payload["traj"]):
        result.append(
            (
                float(rho),
                {
                    name: arr.numpy() if isinstance(arr, _NamedArrayCompat) else np.asarray(arr)
                    for name, arr in traj.items()
                },
            )
        )
    return result


def parameter_summary_rows() -> List[dict]:
    rows = []
    for model in MODELS.values():
        rows.append(
            {
                "model": model.name,
                "kcat1": model.kcat1,
                "kcat2": model.kcat2,
                "saturation_n1=n*kcat1/kcat2": model.kcat1 / model.kcat2,
                "tau_target_n1_s": relaxation_time(model, 1),
                "tau_SOS_GDP_s": dwell_time(model, "GDP"),
                "tau_SOS_GTP_s": dwell_time(model, "GTP"),
                "relax_per_dwell_GDP_n1": persistence_ratio(model, 1, "GDP"),
                "relax_per_dwell_GTP_n1": persistence_ratio(model, 1, "GTP"),
                "binding_ratio_coeff_GDP=konCoeff/koff": model.kon_coeff / model.koff_gdp,
                "binding_ratio_coeff_GTP=konCoeff/koff": model.kon_coeff / model.koff_gtp,
            }
        )
    return rows


def tracking_rows(c_values=(1.0, 2.0, 3.0, 5.0), max_n: int = 5) -> List[dict]:
    rows = []
    for model in MODELS.values():
        for bound_state in ("GDP", "GTP"):
            for n in range(1, max_n + 1):
                gamma = persistence_ratio(model, n, bound_state)
                for c in c_values:
                    rows.append(
                        {
                            "model": model.name,
                            "bound_state": bound_state,
                            "n_bound": n,
                            "relaxation_multiples_c": c,
                            "gamma": gamma,
                            "mean_error_fraction_after_c": tracking_error_after_relaxations(c),
                            "mean_progress_fraction_after_c": 1.0 - tracking_error_after_relaxations(c),
                            "prob_SOS_dwell_survives_c_relaxations": survive_relaxation_window(
                                model, n, bound_state, c
                            ),
                            "mean_residual_fraction_at_unbinding": mean_residual_at_dwell_end(
                                model, n, bound_state
                            ),
                            "mean_completed_fraction_at_unbinding": mean_completed_at_dwell_end(
                                model, n, bound_state
                            ),
                        }
                    )
    return rows


def peak_rows(max_n: int = 10) -> List[dict]:
    rows = []
    for model in MODELS.values():
        for n in range(max_n + 1):
            mu = free_peak(model, n)
            var = free_variance(model, n)
            spacing = exact_spacing(model, n) if n < max_n else float("nan")
            rows.append(
                {
                    "model": model.name,
                    "n_bound": n,
                    "free_peak": mu,
                    "sigma_reduced": math.sqrt(max(var, 0.0)),
                    "spacing_to_next": spacing,
                    "linear_peak": linear_peak(model, n),
                    "linear_error": linear_error(model, n),
                    "saturation_ratio": n * model.kcat1 / model.kcat2,
                    "sequestered_fraction": n / model.ras_total,
                }
            )
    return rows


def empirical_rows(min_count: int = 20) -> List[dict]:
    rows = []
    for name, model in MODELS.items():
        for rho, traj in load_trajectory(name):
            ras = np.asarray(traj["totalRasGTP"], dtype=float)
            bound = np.rint(np.asarray(traj["totalBoundRas"], dtype=float)).astype(int)
            burn = len(ras) // 5
            ras = ras[burn:]
            bound = bound[burn:]
            for n in range(int(bound.max()) + 1):
                mask = bound == n
                count = int(mask.sum())
                if count < min_count:
                    continue
                pred = free_peak(model, n)
                emp = float(ras[mask].mean())
                rows.append(
                    {
                        "model": name,
                        "rhoSOS": rho,
                        "n_bound": n,
                        "samples": count,
                        "empirical_totalRasGTP_mean": emp,
                        "empirical_totalRasGTP_sd": float(ras[mask].std()),
                        "frozen_free_peak_prediction": pred,
                        "absolute_tracking_error": abs(emp - pred),
                        "relative_error_vs_RasTotal": abs(emp - pred) / model.ras_total,
                    }
                )
    return rows


def write_csv(path: Path, rows: Iterable[dict]) -> None:
    rows = list(rows)
    if not rows:
        return
    with open(path, "w", newline="") as f:
        writer = csv.DictWriter(f, fieldnames=list(rows[0].keys()))
        writer.writeheader()
        writer.writerows(rows)


def fmt(x, digits=3):
    if isinstance(x, float):
        if math.isnan(x):
            return "—"
        return f"{x:.{digits}g}"
    return str(x)


def write_markdown(param_rows, tracking, peaks, empirical):
    p = OUT / "RAS_FORMAL_MATH_REPORT.md"
    with open(p, "w") as f:
        f.write("# Ras stochastic-quantization: formal-math application report\n\n")
        f.write("Generated by `formalization/ras_quantization_analysis.py`. This file is numerical evidence, not a Lean proof.\n\n")
        f.write("## 1. Three mechanisms are separated by the mathematics\n\n")
        f.write("The reduced theory separates **peak geometry** (Kcat1, Kcat2, RasTotal, occupancy n) from **occupancy persistence** (SOS binding/unbinding kinetics). This makes the three repository models especially informative:\n\n")
        f.write("- **Model 1:** very strong target saturation already at n=1 (`n*Kcat1/Kcat2 = 4`), so the first jump is large and later peaks crowd. SOS residence is still long enough for quasi-static levels to form.\n")
        f.write("- **Model 2:** 10x faster RasGAP reduces the n=1 saturation ratio to 0.4, spreading several conditional levels across the output range while preserving long SOS residence.\n")
        f.write("- **Model 3:** target chemistry is identical to Model 1, so the frozen peak locations are mathematically identical, but SOS binding/unbinding is 1000x faster. The target cannot track instantaneous occupancy, so those conditional peaks wash out.\n\n")

        f.write("## 2. Time-scale table\n\n")
        f.write("| Model | n=1 saturation | target relaxation time (s) | SOS dwell GDP (s) | SOS dwell GTP (s) | Gamma GDP | Gamma GTP |\n")
        f.write("|---|---:|---:|---:|---:|---:|---:|\n")
        for r in param_rows:
            f.write(f"| {r['model']} | {fmt(r['saturation_n1=n*kcat1/kcat2'])} | {fmt(r['tau_target_n1_s'])} | {fmt(r['tau_SOS_GDP_s'])} | {fmt(r['tau_SOS_GTP_s'])} | {fmt(r['relax_per_dwell_GDP_n1'])} | {fmt(r['relax_per_dwell_GTP_n1'])} |\n")

        f.write("\n`Gamma = target relaxation rate / SOS unbinding rate`. Larger Gamma means an SOS state is likely to live through several Ras response times.\n\n")

        f.write("## 3. New quantitative persistence result\n\n")
        f.write("If an SOS dwell is exponential and Ras relaxes at rate `r`, then after `c` Ras response times the remaining mean error is `exp(-c)`, while the chance that the SOS state has survived that long is exactly `exp(-c/Gamma)`. At `c=3`, Ras has completed about 95% of the mean move.\n\n")
        f.write("| Model | bound state | n | Gamma | chance dwell survives 3 response times |\n")
        f.write("|---|---|---:|---:|---:|\n")
        for r in tracking:
            if r["relaxation_multiples_c"] == 3.0 and r["n_bound"] == 1:
                f.write(f"| {r['model']} | {r['bound_state']} | 1 | {fmt(r['gamma'],4)} | {r['prob_SOS_dwell_survives_c_relaxations']:.4g} |\n")
        f.write("\nUsing the GTP-bound SOS off-rate, the n=1 values are especially stark: Model 1 ≈ 0.887, Model 2 ≈ 0.958, Model 3 ≈ 7.67e-53. Model 3 therefore almost never holds one instantaneous SOS occupancy for the three Ras response times needed to remove ~95% of the mean tracking error.\n\n")
        f.write("Averaging over the full exponential dwell distribution gives an even simpler measure: the expected completed fraction of the occupancy-specific mean move is `Gamma/(1+Gamma)`. At n=1 with the GTP-bound off-rate this is 25/26 ≈ 96.15% for Model 1, 70/71 ≈ 98.59% for Model 2, and 1/41 ≈ 2.44% for Model 3.\n\n")

        f.write("## 4. First frozen conditional peaks\n\n")
        f.write("| Model | n | predicted free RasGTP | spacing to next | reduced sigma | saturation ratio |\n")
        f.write("|---|---:|---:|---:|---:|---:|\n")
        for r in peaks:
            if r["n_bound"] <= 5:
                f.write(f"| {r['model']} | {r['n_bound']} | {fmt(r['free_peak'],4)} | {fmt(r['spacing_to_next'],4)} | {fmt(r['sigma_reduced'],4)} | {fmt(r['saturation_ratio'],3)} |\n")

        f.write("\nThe exact Ras spacing theorem is\n\n")
        f.write("$$\\mu_{n+1}-\\mu_n = \\frac{k_1 [k_2(R-2n-1)-k_1n(n+1)]}{(nk_1+k_2)((n+1)k_1+k_2)}.$$\n\n")
        f.write("The numerator shows two independent reasons peaks crowd: **saturation** (`k1*n`) and **sequestration** (each SOS-bound complex removes a Ras molecule from the free target pool).\n\n")

        f.write("## 5. Direct check against the shipped SSA trajectories\n\n")
        f.write("The table below uses the highest SOS concentration stored for each model and conditions on instantaneous `totalBoundRas`. It is intentionally a hard test of the frozen-occupancy assumption.\n\n")
        f.write("| Model | RhoSOS | n | samples | empirical total RasGTP mean | frozen free-peak prediction | error / RasTotal |\n")
        f.write("|---|---:|---:|---:|---:|---:|---:|\n")
        maxrho = {name: max(m.rho_values) for name, m in MODELS.items()}
        for r in empirical:
            if r["rhoSOS"] == maxrho[r["model"]] and r["n_bound"] <= 5:
                f.write(f"| {r['model']} | {fmt(r['rhoSOS'])} | {r['n_bound']} | {r['samples']} | {fmt(r['empirical_totalRasGTP_mean'],4)} | {fmt(r['frozen_free_peak_prediction'],4)} | {100*r['relative_error_vs_RasTotal']:.1f}% |\n")

        f.write("\nThe pattern is the important result: for processive Models 1/2, nonzero occupancy states approach the predicted conditional levels, especially at n>=2. Model 3 does not: its RasGTP distribution barely follows instantaneous SOS occupancy even though its *formal frozen peaks are identical to Model 1*. This is exactly what a loss of time-scale separation predicts. n=0 in Models 1/2 also shows transient memory because RasGTP takes time to decay after an SOS occupancy event ends.\n\n")

        f.write("## 6. What remains mathematically open\n\n")
        f.write("The strongest missing theorem is still a singular-perturbation result for the **joint continuous-time Markov chain** showing that, when SOS occupancy is slow relative to target relaxation, the stationary distribution is close (e.g. in total variation) to a mixture of the frozen-occupancy binomial laws, with an explicit error bound. The new result proves the local dynamical ingredient exactly: after `c` target response times the mean error is `exp(-c)`, and an exponential SOS dwell survives that long with probability `exp(-c/Gamma)`. What remains is lifting this local residence-time statement to a theorem about the complete stationary joint process.\n")


def main() -> None:
    params = parameter_summary_rows()
    tracking = tracking_rows()
    peaks = peak_rows()
    empirical = empirical_rows()
    write_csv(OUT / "ras_parameter_timescale_summary.csv", params)
    write_csv(OUT / "ras_tracking_probability_summary.csv", tracking)
    write_csv(OUT / "ras_frozen_peak_summary.csv", peaks)
    write_csv(OUT / "ras_empirical_tracking_summary.csv", empirical)
    write_markdown(params, tracking, peaks, empirical)
    print(f"Wrote analysis to {OUT}")


if __name__ == "__main__":
    main()
