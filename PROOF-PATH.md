# Proof path

The default target is `StochasticQuantization.lean`.

## A. Exact finite Ras stationary theorem

The baseline end-to-end statement is `Ras.FullStationary.stationary_defect` in
`StochasticQuantization/RasFullStationary.lean`.

1. `Core.lean` proves the exact frozen activator-target equilibrium algebra.
2. `BirthDeath.lean` proves finite birth/death detailed balance.
3. `RasStateSpace.lean` defines the full conserved finite Ras state space and
   frozen-equilibrium projector `P`.
4. `RasFastBlock.lean` identifies the frozen free-RasGTP equilibrium as a
   binomial distribution.
5. `BirthDeathPoisson.lean` constructs a linear-time pathwise Poisson solve.
6. `RasBlockPoisson.lean` specializes the solve to one frozen Ras block and
   centers out the stationary null mode.
7. `RasGlobalCorrector.lean` assembles block solves into the global corrector
   `R`.
8. `RasGlobalPoisson.lean` proves `Q_fast R = I - P`.
9. `RasReversePoisson.lean` proves `R Q_fast = I - P`.
10. `RasGenerator.lean`, `RasSlowForward.lean`, and `RasFiniteOperators.lean`
    define the common fast/slow linear-operator representation.
11. `StationaryMixture.lean` proves the generic stationary-defect identity.
12. `RasFullStationary.lean` instantiates it and adds finite TV identities.

For stationary `π`,

\[
(Q_{fast}+\varepsilon Q_{SOS})\pi=0
\quad\Longrightarrow\quad
\boxed{\pi-P\pi=-\varepsilon RQ_{SOS}\pi}.
\]

The corresponding exact finite-state TV identity is

\[
TV(\pi,P\pi)=\frac{|\varepsilon|}{2}\|RQ_{SOS}\pi\|_1.
\]

## B. Shared theory abstractions

`Theory/FiniteMetric.lean` generalizes the finite metric implementation so the
new theory and the old dependent Ras state space share one definition.  It also
proves deterministic coarse-graining contracts L1/TV.

`HistoryFilter.lean` supplies the common fading-memory map used by the temporal
extensions.

`StationaryMixture.lean` supplies one Poisson-corrector theorem that is reused in
both directions: Ras-fast/SOS-slow for tracking, and switching-fast/readout-slow
for averaging.

## C. Decoder → Ras stationary decoder theorem

1. `Theory/Decoder.lean` proves
   `error(live) ≤ error(reference) + 2 TV(live,reference)` and a two-reference
   chain bound.
2. Deterministic data processing lifts this from the microscopic finite state to
   any observable coarse-graining.
3. `RasTheory.lean` encodes the dependent Ras state as a sigma state, proves this
   flattening preserves TV, and observes `(total bound SOS, free RasGTP)`.
4. Composing with the exact Ras stationary TV theorem gives source theorem

\[
E_{decode}(\pi)
\le E_{decode}(P\pi)
 + |\varepsilon|\,\|RQ_{SOS}\pi\|_1.
\]

## D. Fast-switching / mean-field direction

`Theory/FastSwitching.lean` has two layers.

- The existing history runner gives an exact two-codeword periodic fixed point
  whose continuous zero-dwell extension is the arithmetic mean.
- The generic stationary theorem is reused with the switching operator as the
  fast operator:

\[
(Q_{switch}+\delta Q_{read})\pi=0
\Longrightarrow
\pi-P_{switch}\pi=-\delta R_{switch}Q_{read}\pi.
\]

Thus slow-state tracking and fast-state averaging are the same finite-state
Poisson-corrector mechanism viewed from opposite timescale orientations.

## E. Remaining theory modules

- `Theory/DwellDistribution.lean`: active-window laws, `E[e^{-rW}]`, completion,
  activation-latency monotonicity, exponential `Gamma/(1+Gamma)` bridge, and
  equal-mean/different-processivity counterexample.
- `Theory/Mesoscopic.lean`: exact inverse-area resolution, finite resolution
  threshold, amplification threshold, and nonempty mesoscopic window.
- `Theory/CatalyticLumping.lean`: microscopic slow-state regrouping by catalytic
  equivalence class; same class masses imply same downstream mixture.
- `RasTheory.lean`: total bound SOS as the Ras catalytic class; complete frozen
  codeword invariance under SOS binding-speed rescaling.
- `Theory/Accessibility.lean`: unique reaction/mixing steady state,
  `f_access=1/(1+Da)`, target-loss identities, and finite fast-mixing bounds.

See [`ELI15.md`](ELI15.md) for the plain-language biological interpretation.

## Verification

From the repository root:

```bash
python3 tools/prelint.py
python3 tools/check_theory_identities.py
lake build
```

Only the final command is a Lean kernel check.  See `PROOF_STATUS.md` for the
current execution boundary.
