# Proof status

This document records the kernel-build status and formalization boundary for the
RasQ stationary core and its theory extension.

## Baseline verification

The supplied repository records a successful build of the pre-extension default
target with the pinned Lean 4.31.0 / Mathlib v4.31.0 toolchain (8,579 Lake jobs).
That baseline includes the finite conserved Ras state space, frozen-binomial
blocks, constructive Poisson corrector, forward/reverse Poisson identities, the
fast/slow generator decomposition, and the exact stationary-defect/TV theorem.

The current source contains no `sorry`, `admit`, or added `axiom` declarations.

## Current verification

The complete current source tree, including all six generic theory modules and
the Ras-specific bridge, has now been built with the pinned Lean 4.31.0 /
Mathlib v4.31.0 toolchain:

```text
Build completed successfully (8588 jobs).
```

The structural pre-lint and independent numerical checks also pass.  The build
reports only non-fatal Lean linter warnings.

## New source implemented in this pass

| Theory component | Main source |
|---|---|
| Shared dependent/ordinary finite L1/TV and deterministic data processing | `Theory/FiniteMetric.lean` |
| Decoder error / frozen overlap / tracking decomposition | `Theory/Decoder.lean` |
| History-filter averaging and generator-level fast-switching dual theorem | `Theory/FastSwitching.lean` |
| Finite dwell laws, activation latency, and `E[exp(-rW)]` processivity | `Theory/DwellDistribution.lean` |
| Inverse-area state resolution and finite mesoscopic window | `Theory/Mesoscopic.lean` |
| Catalytic equivalence classes and mixture invariance | `Theory/CatalyticLumping.lean` |
| Minimal reaction/mixing accessibility and target depletion | `Theory/Accessibility.lean` |
| Ras-specific codeword, lumping, TV, and decoder bridges | `RasTheory.lean` |

`FiniteTV.lean` was refactored into a compatibility wrapper over the new generic
finite metric layer, so the old stationary theorem and the new decoder theory use
the same L1/TV implementation.

## New headline source statements

The current source includes:

- exact stationary Ras tracking defect
  `π - Pπ = -ε R Q_SOS π` (baseline theorem);
- Ras decoder bound
  `decodeError π ≤ decodeError (Pπ) + |ε| * ||R Q_SOS π||₁`;
- generic fast-switching/averaging defect obtained by swapping the fast and slow
  roles in the same stationary corrector theorem;
- exact two-codeword periodic averaging in the existing fading-memory filter;
- effective dwell processivity `1 - E[exp(-rW)]` for finite dwell laws;
- a proof that nonnegative activation latency cannot improve completed tracking;
- equal-mean dwell laws with provably different processivity;
- exact inverse-area squared resolution and a finite mesoscopic window;
- catalytic-class mixture invariance and Ras codeword invariance under
  `speedBinding` / Model-1→Model-3 binding-speed rescaling;
- exact `1/(1+Da)` accessibility and finite fast-mixing depletion bounds.

## Reproducible checks

The following checks have been run successfully after integration:

```text
PRELINT: PASS
- every local import resolves;
- the local import graph is acyclic;
- every Lean module is reachable from the umbrella target;
- every module is included in the Lake globs;
- lakefile.toml parses as TOML;
- no sorry/admit/axiom token occurs in Lean source.

THEORY IDENTITIES: PASS
- 68,785 independent algebraic checks for the new averaging, dwell,
  mesoscopic-scaling, and accessibility identities.
```

The included `.github/workflows/lean.yml` runs these checks and then invokes
`leanprover/lean-action@v1` with the pinned Mathlib cache.  The local build above
is the current kernel-checking evidence; CI provides an independent reproduction
of the same gate.

## Provenance boundary

Some advanced bridge modules in the baseline Ras stationary layer were
reconstructed in an earlier recovery pass to the interfaces and mathematical
semantics required by the surrounding proofs.  The recorded baseline build
checks the implementations present in the supplied repository; it does not
claim byte-for-byte identity with unpreserved historical source.

## Not formalized

- biological truth of the SOS/Ras mechanism;
- parameter-estimation or experimental uncertainty;
- BNGL, NFsim, or Smoldyn parser/runtime semantics;
- a detailed reaction-diffusion simulator;
- a path-space stochastic-process limit theorem when a finite-state stationary
  theorem suffices;
- an SOS-specific switching corrector/projector for a closed-form full Model-3
  averaged stationary distribution (the generic fast-switching theorem is in
  place, and the exact Model-1/Model-3 clock rescaling is already formalized).
