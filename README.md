# Ras stochastic quantization in Lean

This repository is a Lean 4 formalization of the mathematics behind
“Mathematical modeling of processive Ras activation by SOS reveals a general
mechanism for digital signaling” by Katherine A. Yonosh and James R. Faeder.

The central result is an exact finite-state stationary identity.  For a stationary
distribution `π`, the full generator splits into fast Ras dynamics and an SOS
switching operator:

$$
Q_\varepsilon = Q_{fast} + \varepsilon Q_{SOS}.
$$

The projector `P` preserves each frozen SOS block's mass and replaces its
free-RasGTP distribution by the exact binomial equilibrium.  The formalization
proves

$$
\boxed{\pi - P\pi = -\varepsilon RQ_{SOS}\pi},
$$

where `R` is a constructive fast Poisson corrector.  It also proves the exact
total-variation identity and an explicit first-order bound.

## Build

Install `elan`, then build from the repository root.  `elan` reads the pinned
Lean version from [`lean-toolchain`](lean-toolchain).

```bash
lake build
```

The verified build checks the complete dependency graph through
`RasFullStationary`.  The current build completed successfully with 8,579 Lake
jobs.  The Lean source contains no `sorry`, `admit`, or added `axiom`
declarations.

## Proof path

[`PROOF-PATH.md`](PROOF-PATH.md) maps the main theorem to the definitions and
lemmas that establish it.  [`PROOF_STATUS.md`](PROOF_STATUS.md) records the
verification boundary and the mathematical statements covered by the build.
For a plain-language overview, see [`ELI15.md`](ELI15.md).

## Repository layout

```text
.
├── StochasticQuantization.lean       # umbrella import and default target
├── StochasticQuantization/           # Lean definitions and proofs
│   ├── Core.lean                     # activator-target equilibrium algebra
│   ├── BirthDeath.lean               # finite detailed balance
│   ├── BirthDeathPoisson.lean        # pathwise Poisson solver
│   ├── HistoryFilter.lean            # fading SOS-history representation
│   ├── RasGenerator.lean             # finite Ras count generator
│   ├── RasFastBlock.lean              # frozen binomial block equilibrium
│   ├── RasStateSpace.lean             # conserved dependent state space
│   ├── RasBlockPoisson.lean           # compact block corrector
│   ├── RasGlobalCorrector.lean        # global corrector assembly
│   ├── RasGlobalPoisson.lean          # forward Poisson identity
│   ├── RasSlowForward.lean            # SOS switching operator
│   ├── RasFiniteOperators.lean        # linear-operator layer
│   ├── RasReversePoisson.lean         # reverse Poisson identity
│   ├── FiniteTV.lean                  # finite total variation
│   ├── StationaryMixture.lean         # abstract stationary identity
│   └── RasFullStationary.lean         # end-to-end theorem
├── PROOF-PATH.md                      # theorem dependency guide
├── PROOF_STATUS.md                    # verification status and limits
├── lakefile.toml                      # Lake project configuration
├── lake-manifest.json                 # pinned dependencies
└── lean-toolchain                     # pinned Lean toolchain
```

## Scope and limits

Lean checks that the formal statements follow from their assumptions.  It does
not establish that the biological mechanism is true, formalize BNGL parser
semantics, or replace experimental validation.  The model's large numerical
stationary calculations are outside this Lean target.

## Citation

If you use this formalization, please cite:

> K. A. Yonosh and J. R. Faeder, *Mathematical modeling of processive Ras
> activation by SOS reveals a general mechanism for digital signaling*.
