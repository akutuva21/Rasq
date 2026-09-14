# RasActivation-Simulator

Repository for **"Mathematical modeling of processive Ras activation by SOS reveals a general mechanism for digital signaling"**  
Katherine A. Yonosh & James R. Faeder  
Department of Computational and Systems Biology, University of Pittsburgh

---

## Overview

This repository contains BioNetGen models and Python/Jupyter notebooks used to simulate and analyze stochastic Ras–SOS activation. Three parameter regimes (Models 1–3) explore varying SOS processivity and resulting signaling quantization. A general activator–target framework provides analytical predictions for conditional peak positions that are validated across all models.

---

## Repository Structure

```
RasActivation-Simulator/
├── Model1.bngl                  # Baseline Lee et al. parameters (processive, bimodal)
├── Model2.bngl                  # 10× higher kcat2, higher SOS (processive, multimodal)
├── Model3-1.bngl                # 1000× faster kon/koff (non-processive, unimodal)
├── 01_run_simulation.ipynb      # Run SSA trajectories and save to .pkl
├── 02_plot_simulation.ipynb     # Plot time courses and distributions 
├── 03_quantized_analysis.ipynb  # Box 1 framework validation, manuscript figure generation, and peak analysis
├───04_supplemental_analysis.ipynb  # figure generation, positive feedback and bifurcation analysis
├── activator-target.ipynb             # Minimal model demonstration with analytical predictions (Fig. S5)
└── README.md
```

---

## Models

| Model | Description | Key change from Model 1 | Expected output |
|-------|-------------|--------------------------|-----------------|
| Model 1 | Lee et al. baseline | — | Apparent bimodal |
| Model 2 | Faster RasGAP, higher SOS | `Kcat2` × 10, `[SOS]` up to 30 nM | Resolved multimodal |
| Model 3 | Non-processive SOS | `Kon`/`Koff` × 1000 | Unimodal |

All models share the same reaction rules: reversible SOS binding to RasGDP or RasGTP, catalytic exchange (RasGDP → RasGTP) by membrane-bound SOS, and RasGAP-mediated hydrolysis (RasGTP → RasGDP).

---

## Notebooks

### `01_run_simulation.ipynb`
Runs Gillespie SSA trajectories for a chosen model across a range of SOS concentrations and saves results to `<MODEL>_traj.pkl`.

- Set `MODEL = "Model1"`, `"Model2"`, or `"Model3"` at the top
- Outputs: `Model1_traj.pkl`, `Model2_traj.pkl`, `Model3_traj.pkl`
- Default: `t_end = 100,000 s`, `n_steps = 10,000` output points

### `02_plot_simulation.ipynb`
Loads a `.pkl` trajectory file and generates four plots:

- **A** — Time-course trajectories (RasGTP + Bound SOS)  
- **B** — RasGTP count distributions  
- **C** — SOS occupancy distributions  
- **D** — RasGTP distributions conditioned on SOS occupancy state  

### `03_quantized_analysis.ipynb`
Validates the activator–target framework against simulation results:

- Computes predicted conditional peak positions ⟨T\*⟩ₙ from kinetic parameters
- Generates the 4-panel manuscript figure (2-4) 
- Compares SSA peak modes to analytical predictions 
- Simulates conditional RasGTP distributions at fixed n 

### `04_supplemental_analysis.ipynb`
Explores  role of positive feedback and confirms the absence of bistability.

- Supplemental Figures S1–S3 — Full time-course and distribution panels across all SOS concentrations for each model
- Bifurcation Analysis (Fig. S4) — Forward and backward steady-state scans using CVODE for all three models, confirming no bistability
- Eliminating Positive Feedback — Simulations with Koff1 = Koff2 (no feedback) for Models 1, 2, and 3. 
- Mean-Field Analysis for Model 3 — Compares the mean-field prediction computed without positive feedback to the simulation-derived mean
- Increasing Positive Feedback (Model 2) — varies Koff2 to show that stronger feedback increases the weight of higher SOS occupancy states without changing the quantized peak positions themselves 

### 'activator_target.ipynb'

A self-contained demonstration of the Box 1 activator–target framework, completely independent of the Ras/SOS models (no BioNetGen required). Implements the minimal two-layer cascade using a direct Gillespie SSA and validates it against the analytical Poisson-binomial mixture prediction. Produces Fig. S5 in the manuscript.


---

## Quickstart

### 1. Install dependencies

```bash
pip install -r requirements.txt
```

BioNetGen must also be installed separately (see below).

### 2. Run a simulation

Open `01_run_simulation.ipynb`, set `MODEL = "Model1"` (or 2/3), and run all cells. This produces `Model1_traj.pkl`.

### 3. Plot results

Open `02_plot_simulation.ipynb`, set `MODEL = "Model1"`, and run all cells.

### 4. Framework analysis

Open `03_quantized_analysis.ipynb`, set `MODEL` and matching `RhoSOS` concentration, and run all cells to reproduce the manuscript figures and peak-position comparison table.

### 4. Positive feedback and bifurcation analysis

Open 04_positive_feedback_analysis.ipynb. Each section is self-contained and documents which model and parameter modifications it applies.



## Dependencies

See `requirements.txt` for the full Python package list. Key dependencies:

- **[BioNetGen](https://bionetgen.org/)** —  install separately and ensure `bionetgen` is on your PATH  
- **bionetgen** (Python package) — Python interface to BioNetGen  
- **numpy**, **matplotlib**, **pickle** — simulation and plotting  

### Installing BioNetGen

```bash
# Via conda (recommended)
conda install -c conda-forge bionetgen

# Or download directly from https://bionetgen.org/
```

---

## Parameter Reference

| Parameter | Model 1 | Model 2 | Model 3 | Description |
|-----------|---------|---------|---------|-------------|
| `RhoSOS` | 1–10 nM | 1–30 nM | 1–10 nM | Initial SOS concentration |
| `Kon1` | 7×10⁻⁸ × RhoSOS | same | 7×10⁻⁵ × RhoSOS | SOS binding RasGDP |
| `Kon2` | 7×10⁻⁸ × RhoSOS | same | 7×10⁻⁵ × RhoSOS | SOS binding RasGTP |
| `Koff1` | 5×10⁻³ s⁻¹ | same | 5 s⁻¹ | SOS unbinding RasGDP |
| `Koff2` | 5×10⁻⁴ s⁻¹ | same | 0.5 s⁻¹ | SOS unbinding RasGTP |
| `Kcat1` | 1×10⁻² μm²s⁻¹/A | same | same | RasGDP → RasGTP |
| `Kcat2` | 2.5×10⁻³ s⁻¹ | 2.5×10⁻² s⁻¹ | same as M1 | RasGTP → RasGDP |
| `A` | 1 μm² | same | same | Corral area |
| `RasTotal` | 1000 | same | same | Total Ras molecules |

---

## Output Files

| File | Generated by | Contents |
|------|-------------|----------|
| `Model1_traj.pkl` | `01_run_simulation` | Dict with model name, SOS concentrations, and trajectory arrays |
| `Model2_traj.pkl` | `01_run_simulation` | Same, Model 2 parameters |
| `Model3_traj.pkl` | `01_run_simulation` | Same, Model 3 parameters |
| `Model1figure.png` | `03_quantized_analysis` | 4-panel manuscript figure |
| `Model2figure.png` | `03_quantized_analysis` | 4-panel manuscript figure |
| `Model3figure.png` | `03_quantized_analysis` | 4-panel manuscript figure |

---

## Citation

If you use this code, please cite:

> Yonosh, K.A. & Faeder, J.R. Mathematical modeling of processive Ras activation by SOS reveals a general mechanism for digital signaling

---

## Contact

Katherine A. Yonosh - kay89@pitt.edu
James R. Faeder — faeder@pitt.edu  
Department of Computational and Systems Biology, University of Pittsburgh


---

## Formal stochastic-quantization analysis (Lean 4)

A standalone Lean formalization is available in [`formalization/`](formalization/README.md). The self-contained Lean core derives exact conditional peak formulas, peak-crowding effects, a quantitative slow/fast tracking rule connecting SOS dwell time to Ras relaxation, and a deterministic positive-steady-state uniqueness result for the reduced Ras equations. See [`formalization/ARCHIVE_INTEGRITY.md`](formalization/ARCHIVE_INTEGRITY.md): the ZIP does not include the later finite-state stationary-theorem modules described by some older documentation.

The key mechanistic decomposition is: **Model 1 is strongly saturation-crowded; Model 2 opens the dynamic range via faster RasGAP; Model 3 preserves Model-1 frozen peak locations but destroys the residence-time separation needed for the system to occupy them.** See [`formalization/generated/RAS_FORMAL_MATH_REPORT.md`](formalization/generated/RAS_FORMAL_MATH_REPORT.md) for the numerical application and [`formalization/PROOF_STATUS.md`](formalization/PROOF_STATUS.md) for exact proof/build status.
