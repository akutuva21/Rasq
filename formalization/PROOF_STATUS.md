# Formalization status

This file is deliberately conservative about what has and has not been verified.

## Implemented as Lean theorem source

| Component | File(s) |
|---|---|
| Frozen activator-target flux balance, mean, spacing, low-saturation error | `Core.lean` |
| Finite birth/death detailed balance | `BirthDeath.lean` |
| Constructive O(F) birth/death Poisson solve and centering | `BirthDeathPoisson.lean` |
| Binding-ratio, dwell-time, and processivity scaling | `Processivity.lean` |
| One-dwell slow/fast tracking and exponential-dwell averages | `SlowFast.lean` |
| Exact finite-history fading-memory identities | `HistoryFilter.lean` |
| Ras frozen peak/error/spacing and Model 1→3 rescaling | `Ras.lean` |
| Reduced deterministic positive-equilibrium uniqueness | `RasEquilibrium.lean` |
| Six count-level BNGL reaction propensities | `RasGenerator.lean` |
| Exact frozen Ras birth/death block and binomial weights/mean | `RasFastBlock.lean` |
| Full finite fixed-Ras block state space and frozen projector | `RasStateSpace.lean` |
| Compact Ras block Poisson corrector | `RasBlockPoisson.lean` |
| Global blockwise corrector | `RasGlobalCorrector.lean` |
| Componentwise `Q_fast R = I-P`, including the one-state block | `RasGlobalPoisson.lean` |
| Exact SOS binding/unbinding forward operator | `RasSlowForward.lean` |
| Fast/slow/projector/corrector operators on one state space | `RasFiniteOperators.lean` |
| Finite L1 / total-variation definitions | `FiniteTV.lean` |
| Generic exact stationary-defect theorem | `StationaryMixture.lean` |
| Finite-dimensional derivation of `R Q_fast = I-P` | `RasReversePoisson.lean` |
| End-to-end Ras stationary defect, TV identity, and conditional O(epsilon) bound | `RasFullStationary.lean` |

The intended main theorem is

```text
pi - P*pi = -epsilon * R * Q_SOS * pi
```

for a stationary distribution of the exact finite fixed-total Ras count process.

## Executed numerical verification

The following were run successfully in this environment:

- `python test_math_identities.py`
  - 20,000 randomized algebra / slow-fast / history / detailed-balance checks.
- `python ras_quantization_analysis.py`
  - formula application and checks against the supplied SSA trajectories.
- `python full_ras_ctmc_analysis.py`
  - 1000-Ras sparse CTMC stationary solves;
  - 65,626-state native high-SOS analyses at bound-SOS cap 10;
  - cap convergence through 90,363 states at cap 12;
  - stable O(F) block Poisson certificate;
  - exact stationary-defect numerical identity;
  - slow-clock scaling;
  - Model 1/Model 3 1000x clock equivalence;
  - history-filter reconstruction.

Representative exact-identity relative L1 errors at native high-SOS conditions are
all below `1e-9` in the current generated report (roughly `1e-12` for Models 1–2 and
`7.5e-10` for the numerically stiff fast-switching Model 3 calculation).

## Important limitation: Lean kernel build not run here

The container used for this work does not have Lean installed and cannot resolve
the Lean/GitHub download hosts needed to install the pinned toolchain.  Therefore
`lake build` has **not** been run in this environment.

There are no intentional `sorry` or `admit` placeholders in the claimed theorem
source.  Nevertheless, until the project is compiled by Lean, describe the result
as:

> **Lean theorem source, awaiting kernel compilation.**

Do not describe it as machine-checked or kernel-verified yet.

The repository includes `.github/workflows/formalization.yml`, which is intended
to run:

1. a proof-placeholder gate;
2. the pinned Lean/Mathlib build;
3. Lean's independent checker;
4. the numerical regression/certificate suite.

## What is not formalized

- The BNGL parser/language semantics themselves are not formalized.
- The biological truth of the Ras/SOS mechanism is not a theorem.
- The large numerical CTMC uses a bound-SOS cap for computation; the symbolic
  Lean state-space definitions themselves do not impose that cap.
