# Formalization status

This file is deliberately conservative about what has and has not been verified.
For the provenance and completeness boundary of this ZIP, see
[`ARCHIVE_INTEGRITY.md`](ARCHIVE_INTEGRITY.md).  The table below describes only
the source that is present and compiled in this checkout; older claims about a
larger stationary-theorem extension are not claims about this archive.

## Included and kernel-checked by `lake build`

| Component | File(s) |
|---|---|
| Frozen activator-target flux balance, mean, spacing, low-saturation error | `Core.lean` |
| Finite birth/death detailed balance | `BirthDeath.lean` |
| Constructive O(F) birth/death Poisson solve and centering | `BirthDeathPoisson.lean` |
| Binding-ratio, dwell-time, and processivity scaling | `Processivity.lean` |
| One-dwell slow/fast tracking and exponential-dwell averages | `SlowFast.lean` |
| Ras frozen peak/error/spacing and Model 1→3 rescaling | `Ras.lean` |
| Reduced deterministic positive-equilibrium uniqueness | `RasEquilibrium.lean` |

The verified library target is the explicit module list in `lakefile.toml`.

## Source referenced by older documentation but absent here

The ZIP does not contain `HistoryFilter.lean`, `RasGenerator.lean`,
`RasFastBlock.lean`, `RasStateSpace.lean`, `RasBlockPoisson.lean`,
`RasGlobalCorrector.lean`, `RasFiniteOperators.lean`, `FiniteTV.lean`, or
`StationaryMixture.lean`.  The four advanced files that import these modules are
preserved but excluded from the default target.  In particular, the exact
finite-state stationary-defect theorem is not machine-checked by this checkout.

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

## Kernel build status

The included target was compiled successfully with the pinned Lean 4.31.0
toolchain using the isolated temporary `elan` installation described in
`ARCHIVE_INTEGRITY.md`.  The retained source contains no `sorry`, `admit`, or
`axiom` declarations.

This does not certify the absent advanced modules or the generated numerical
reports.  It also does not formalize BNGL parser semantics or biological truth.

## What is not formalized

- The BNGL parser/language semantics themselves are not formalized.
- The biological truth of the Ras/SOS mechanism is not a theorem.
- The large numerical CTMC uses a bound-SOS cap for computation; the symbolic
  Lean state-space definitions themselves do not impose that cap.
