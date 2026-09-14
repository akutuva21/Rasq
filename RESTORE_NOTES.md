# Rasq advanced-formalization restoration bundle

This bundle restores the nine Lean modules that are missing from the current
`akutuva21/Rasq` checkout and makes the complete advanced dependency chain part
of the default Lake target.

## Missing modules restored

- `formalization/StochasticQuantization/HistoryFilter.lean`
- `formalization/StochasticQuantization/RasGenerator.lean`
- `formalization/StochasticQuantization/RasFastBlock.lean`
- `formalization/StochasticQuantization/RasStateSpace.lean`
- `formalization/StochasticQuantization/RasBlockPoisson.lean`
- `formalization/StochasticQuantization/RasGlobalCorrector.lean`
- `formalization/StochasticQuantization/RasFiniteOperators.lean`
- `formalization/StochasticQuantization/FiniteTV.lean`
- `formalization/StochasticQuantization/StationaryMixture.lean`

The bundle also supplies replacement integration files:

- `formalization/StochasticQuantization.lean`
- `formalization/lakefile.toml`

These imports/globs include the existing advanced files already present in the
repository: `RasGlobalPoisson.lean`, `RasSlowForward.lean`,
`RasReversePoisson.lean`, and `RasFullStationary.lean`.

## Provenance

Five bridge modules were recovered from the pre-packaging formalization source:
`RasFastBlock`, `RasGlobalCorrector`, `RasFiniteOperators`, `FiniteTV`, and
`StationaryMixture` (with the later `abs_neg` TV-proof fix retained).

The raw pre-packaging bytes of `HistoryFilter`, `RasGenerator`, `RasStateSpace`,
and `RasBlockPoisson` were not preserved in the conversation artifacts.  Those
four modules have therefore been reconstructed to the APIs and mathematical
semantics required by the surviving advanced theorem files.  In particular,
`RasStateSpace` defines the full conserved dependent count state space and
frozen-binomial projector, while `RasBlockPoisson` supplies the O(F) blockwise
Poisson corrector API used by `RasGlobalPoisson`.

## Verification at restoration

The smaller Rasq target was independently reported to build under Lean 4.31.0.
The restored advanced target has now also been kernel-compiled in the checkout
with the pinned Lean 4.31.0 toolchain:

```text
Build completed successfully (8579 jobs).
```

The original bundle was produced before that local build and therefore described
the advanced target as uncompiled.  That historical statement is superseded by
the result above.  To reproduce it with a normal `elan` installation, run:

```bash
cd formalization
lake build
```

Then confirm no placeholders:

```bash
rg -n '\\b(sorry|admit|axiom)\\b' StochasticQuantization*.lean StochasticQuantization || true
```

If Lean reports any compile error in the restored bridge layer, preserve the
first error and its surrounding lines; it should be patched against the pinned
4.31.0 API rather than removing the advanced module from the target.
