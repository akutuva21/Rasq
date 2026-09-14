# Archive integrity and Lean build status

This checkout was imported from
`RasActivation-Simulator-stochastic-quantization-final-complete.zip`.
The ZIP is not a complete copy of the larger formalization described by some of
its documentation.

## Verified in this checkout

The default Lake target contains the self-contained modules that are actually
present:

- `StochasticQuantization.lean`
- `Core.lean`
- `BirthDeath.lean`
- `BirthDeathPoisson.lean`
- `Processivity.lean`
- `SlowFast.lean`
- `Ras.lean`
- `RasEquilibrium.lean`

They compile successfully with the pinned Lean 4.31.0 toolchain:

```text
Build completed successfully (8566 jobs).
```

The build was run through the isolated temporary installation at
`/private/tmp/bng3-elan-home`; no global Lean installation was required.  The
retained source contains no `sorry`, `admit`, or `axiom` declarations.

## Not included in the ZIP

These files are referenced by the remaining advanced `.lean` files and by the
older proof-status documentation, but are absent from the archive:

`HistoryFilter.lean`, `RasGenerator.lean`, `RasFastBlock.lean`,
`RasStateSpace.lean`, `RasBlockPoisson.lean`, `RasGlobalCorrector.lean`,
`RasFiniteOperators.lean`, `FiniteTV.lean`, and `StationaryMixture.lean`.

Consequently, `RasSlowForward.lean`, `RasReversePoisson.lean`,
`RasGlobalPoisson.lean`, and `RasFullStationary.lean` are preserved as archive
content but are not part of the default compiled target.  The full stationary
defect theorem advertised in those files cannot be claimed as machine-checked
from this ZIP alone.

The generated numerical reports are retained as data, but the scripts that
produced some of the larger CTMC reports are also absent.  They should not be
described as freshly reproduced by this checkout without restoring those
scripts.
