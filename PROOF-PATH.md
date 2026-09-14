# Proof path

The default target is `StochasticQuantization.lean`.  The main end-to-end
statement is `Ras.FullStationary.stationary_defect` in
`StochasticQuantization/RasFullStationary.lean`.

## Main dependency chain

1. `Core.lean` proves the exact equilibrium mean of an activator-target chain.
2. `BirthDeath.lean` proves finite birth/death detailed balance.
3. `RasStateSpace.lean` defines the conserved finite Ras state space and the
   frozen-equilibrium projector `P`.
4. `RasFastBlock.lean` identifies the frozen free-RasGTP equilibrium as a
   binomial distribution.
5. `BirthDeathPoisson.lean` constructs a linear-time pathwise Poisson solve.
6. `RasBlockPoisson.lean` specializes that solve to one frozen Ras block and
   removes its stationary null mode.
7. `RasGlobalCorrector.lean` assembles the block solves into the global
   corrector `R`.
8. `RasGlobalPoisson.lean` proves the forward identity
   `Q_fast R = I - P`.
9. `RasReversePoisson.lean` proves the reverse identity
   `R Q_fast = I - P` using finite-dimensional linear algebra.
10. `RasGenerator.lean`, `RasSlowForward.lean`, and `RasFiniteOperators.lean`
    define the full fast/slow operator decomposition.
11. `StationaryMixture.lean` turns the operator identities into a general
    stationary-defect theorem.
12. `RasFullStationary.lean` specializes that theorem to the Ras state space and
    adds the total-variation identity and bound from `FiniteTV.lean`.

## Formal endpoint

For `pi` satisfying

$$
(Q_{fast} + \varepsilon Q_{SOS})\pi = 0,
$$

the endpoint is

$$
\pi - P\pi = -\varepsilon RQ_{SOS}\pi.
$$

The theorem is exact: the frozen-mixture approximation is not assumed to be
accurate.  Its error is identified as SOS switching forcing filtered through the
fast Ras corrector.

The total-variation layer proves

$$
TV(\pi,P\pi)=\frac{|\varepsilon|}{2}\|RQ_{SOS}\pi\|_1,
$$

and derives the corresponding bound when separate L1 operator bounds are
available.

## Verification

From the repository root:

```bash
lake build
```

This target checks the full module graph with the pinned toolchain in
`lean-toolchain`.
