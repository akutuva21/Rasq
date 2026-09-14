# Archive integrity and Lean build status

This checkout was imported from
`RasActivation-Simulator-stochastic-quantization-final-complete.zip` and then
overlaid with `Rasq-missing-advanced-lean-files.zip`.  The second bundle restores
the later finite-state stationary-theorem dependency chain.

## Verified in this checkout

The default Lake target now includes the core library, the restored bridge
modules, and the advanced stationary chain through `RasFullStationary.lean`:

- finite activator-target and birth/death identities;
- constructive O(F) block Poisson solves and the global corrector;
- the finite Ras state space, generator, history filter, and slow/fast operator;
- reverse Poisson and total-variation identities;
- the exact finite-state stationary-defect theorem and its explicit TV bound.

They compile successfully with the pinned Lean 4.31.0 toolchain:

```text
Build completed successfully (8579 jobs).
```

The build was run through the isolated temporary installation at
`/private/tmp/bng3-elan-home`; no global Lean installation was required.  The
retained source contains no `sorry`, `admit`, or `axiom` declarations.

## Provenance boundary

The restoration bundle records that five bridge modules were recovered from
pre-packaging source, while `HistoryFilter`, `RasGenerator`, `RasStateSpace`, and
`RasBlockPoisson` were reconstructed to the APIs and mathematical semantics
required by the surviving advanced files.  The successful Lean build verifies
the source currently in this checkout, including those reconstructions; it does
not establish that every reconstructed file is byte-for-byte identical to an
unpreserved original.

The generated numerical reports remain supplied data.  This Lean build does not
freshly reproduce their CTMC calculations, does not formalize BNGL parser
semantics, and does not establish biological truth.
