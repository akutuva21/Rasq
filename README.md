# Ras stochastic quantization in Lean

This repository uses Lean 4 to develop the mathematical theory behind
processivity-driven Ras/SOS stochastic quantization.  It is based on the RasQ
model from Katherine A. Yonosh and James R. Faeder, *Mathematical modeling of
processive Ras activation by SOS reveals a general mechanism for digital
signaling*.

The goal is **not** to formalize a simulator.  The goal is to separate the
mechanistic claims that follow exactly from the stochastic model from the claims
that depend on parameter choices, approximation regimes, or biology.

## Existing Ras stationary theorem

For the finite conserved Ras count model, the generator is split into fast Ras
chemistry and SOS switching,

\[
Q_\varepsilon = Q_{fast} + \varepsilon Q_{SOS}.
\]

`P` preserves each frozen SOS block's mass while replacing its free-RasGTP
conditional distribution by the exact frozen binomial equilibrium.  A
constructive blockwise Poisson corrector `R` gives the exact identity

\[
\boxed{\pi-P\pi=-\varepsilon RQ_{SOS}\pi}
\]

for every stationary law `π`.  The finite total-variation layer gives

\[
TV(\pi,P\pi)
=\frac{|\varepsilon|}{2}\|RQ_{SOS}\pi\|_1.
\]

Biologically, this identifies failure to track the current SOS-conditioned Ras
state as **SOS switching filtered through finite Ras biochemical memory**.

## Theory extension

The new `StochasticQuantization/Theory/` layer asks what broader biological
principles follow from that mechanism.  It develops six connected pieces:

1. **Decoding.**  Quantization is treated as the ability of a biochemical
   readout to decode a discrete molecular state, rather than merely as visible
   multimodality.  Decoder error is bounded by frozen-state overlap plus a TV
   tracking defect.
2. **Fast switching / averaging.**  The existing stationary Poisson-corrector
   theorem is reused with the biological roles reversed.  Slow switching yields
   state tracking; fast switching yields approach to the switching-equilibrium
   / averaged manifold.  The same history filter also gives an exact minimal
   two-codeword averaging result.
3. **Mesoscopic scaling.**  Squared neighboring-state resolution is formalized
   and shown to scale inversely with system area under the stated variance
   scaling, producing a finite size window between target amplification and
   macroscopic averaging.
4. **General dwell-time processivity.**  Effective processivity is controlled by
   the residual `E[exp(-r W)]` for active window `W`, not by mean residence time
   alone.  The finite-law theory includes activation latency and an exact
   equal-mean/different-processivity counterexample.
5. **Feedback / catalytic lumping.**  Slow microstates are separated from their
   catalytic equivalence classes.  Redistribution within a class cannot move
   the frozen downstream codeword.  In Ras, speeding SOS binding/unbinding leaves
   the complete frozen codeword unchanged.
6. **Spatial accessibility.**  The conceptual lesson of detailed spatial
   modeling is reduced to a minimal reaction-versus-mixing theorem: finite
   mixing produces an
   accessible target fraction `1/(1+Da)` and a controlled depletion error.

The resulting theory is organized around a general statement:

> A biochemical system can transmit a discrete molecular state without
> bistability when the frozen states are distinguishable, the readout can track
> the discrete driver, and the assumed target pool is physically accessible.

Ras/SOS is the experimentally grounded motivating instance, not the boundary of
the mathematical abstraction.

See [`PROOF-PATH.md`](PROOF-PATH.md) for the theorem architecture.

## Build

The project is pinned to Lean 4.31.0 and Mathlib v4.31.0.

```bash
lake build
```

For cheap checks before invoking Lean:

```bash
python3 tools/prelint.py
python3 tools/check_theory_identities.py
```

The pre-lint verifies local imports, import acyclicity, Lake globs/TOML, umbrella
reachability, and absence of `sorry`, `admit`, or added `axiom` tokens in source.
The numerical smoke test independently checks 68,785 independent instances of
several new algebraic identities.  Neither replaces `lake build`.

### Verification status

The complete current target, including the theory extension and Ras-specific
bridge, has been kernel-checked locally with the pinned Lean 4.31.0 / Mathlib
v4.31.0 toolchain:

```text
Build completed successfully (8588 jobs).
```

The build emits only non-fatal Lean linter warnings.  The source contains no
`sorry`, `admit`, or added `axiom` declarations.

The included GitHub Actions workflow runs the pre-lint, numerical smoke tests,
and the pinned Lean/Mathlib build.  See [`PROOF_STATUS.md`](PROOF_STATUS.md) for
the exact verification boundary.

## Proof maps

- [`PROOF-PATH.md`](PROOF-PATH.md): dependency path for the exact stationary Ras
  theorem and the new theory bridge.
- [`PROOF_STATUS.md`](PROOF_STATUS.md): kernel-build evidence, provenance, and
  the remaining formalization boundary.
- [`ELI15.md`](ELI15.md): plain-language interpretation.

## Repository layout

```text
.
├── StochasticQuantization.lean          # umbrella/default Lean target
├── StochasticQuantization/
│   ├── Core.lean                        # activator-target equilibrium algebra
│   ├── BirthDeath.lean                  # finite detailed balance
│   ├── BirthDeathPoisson.lean           # O(F) pathwise Poisson solver
│   ├── HistoryFilter.lean               # reusable fading-memory primitive
│   ├── RasStateSpace.lean               # conserved dependent Ras state space
│   ├── RasFastBlock.lean                # exact frozen binomial block
│   ├── RasGlobalCorrector.lean           # global Ras corrector
│   ├── RasFullStationary.lean            # end-to-end stationary defect theorem
│   ├── FiniteTV.lean                    # Ras wrapper over generic finite metric
│   ├── RasTheory.lean                   # Ras instantiation of theory extensions
│   ├── Theory.lean                      # generic theory umbrella
│   └── Theory/
│       ├── FiniteMetric.lean            # shared L1/TV + data processing
│       ├── Decoder.lean                 # decoding/error decomposition
│       ├── FastSwitching.lean           # temporal/generator averaging
│       ├── DwellDistribution.lean       # general processive dwell laws
│       ├── Mesoscopic.lean              # finite-size resolution window
│       ├── CatalyticLumping.lean        # feedback/catalytic classes
│       └── Accessibility.lean           # reaction-vs-mixing target access
├── tools/prelint.py
├── tools/check_theory_identities.py
├── .github/workflows/lean.yml
├── PROOF-PATH.md
├── PROOF_STATUS.md
├── lakefile.toml
├── lake-manifest.json
└── lean-toolchain
```

## Scope

Lean proves implications of the formal assumptions.  It does not establish that
those assumptions are biologically true, prove parameter values, formalize BNGL
or Smoldyn semantics, or replace experiment.  Detailed numerical simulation
remains outside the theorem layer by design.

## Citation

If you use this formalization, please cite the RasQ work and the original
processive-Ras paper appropriately.
