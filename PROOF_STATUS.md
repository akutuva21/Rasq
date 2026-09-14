# Proof status

This repository is centered on the Lean library and its kernel-checked
stationary theorem.  The dependency path is summarized in
[`PROOF-PATH.md`](PROOF-PATH.md).

## Build verification

The default target is the umbrella module `StochasticQuantization.lean`.
Running `lake build` from the repository root completed successfully with the
pinned Lean 4.31.0 toolchain and checked 8,579 Lake jobs.

The Lean source contains no `sorry`, `admit`, or added `axiom` declarations.
The build result establishes the formal statements in the source; it does not
establish the truth of the biological mechanism.

## Kernel-checked theorem areas

| Area | Main modules |
|---|---|
| Activator-target equilibrium algebra | `Core.lean` |
| Finite birth/death balance and Poisson recurrence | `BirthDeath.lean`, `BirthDeathPoisson.lean` |
| Processivity, dwell-time, and slow/fast scaling | `Processivity.lean`, `SlowFast.lean`, `HistoryFilter.lean` |
| Finite Ras state space and generator | `RasStateSpace.lean`, `RasGenerator.lean` |
| Frozen block equilibrium and compact corrector | `RasFastBlock.lean`, `RasBlockPoisson.lean`, `RasGlobalCorrector.lean` |
| Global fast/slow operator decomposition | `RasGlobalPoisson.lean`, `RasSlowForward.lean`, `RasFiniteOperators.lean` |
| Reverse Poisson and stationary-defect identities | `RasReversePoisson.lean`, `StationaryMixture.lean`, `RasFullStationary.lean` |
| Finite total-variation equality and bound | `FiniteTV.lean`, `RasFullStationary.lean` |
| Ras peak geometry and reduced equilibrium uniqueness | `Ras.lean`, `RasEquilibrium.lean` |

## Provenance boundary

Four bridge modules in the advanced layer were reconstructed to the interfaces
and mathematical semantics required by the surrounding proofs.  The successful
build verifies the implementations currently present here; it does not assert
that those files are byte-for-byte identical to unpreserved source.

## Not formalized

- BNGL parser and language semantics;
- experimental or biological truth of the Ras/SOS mechanism;
- fresh reproduction of large numerical CTMC calculations;
- an uncapped numerical stationary solve (the symbolic state space itself is
  finite, while numerical approximations may use a computational cap).
