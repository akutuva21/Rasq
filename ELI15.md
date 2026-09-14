# Ras stochastic quantization — ELI15

## The one-sentence version

This project asks why a noisy molecular switch can produce a small number of
reliable-looking output levels, and uses Lean to prove an exact statement about
how the fast Ras reaction and the slower SOS reaction fit together.

## What the project is trying to explain

Ras is a small molecular signal carrier. SOS helps turn Ras on. Inside a cell,
the individual molecules do not behave like clockwork: they bind, unbind, and
change state at random times.

The surprising observation is that random microscopic behavior can still make
the overall signal look “quantized”—more like a few distinct settings than a
perfectly smooth dial. The project studies one explanation:

- SOS can occupy a small number of discrete binding states.
- Each SOS state gives Ras a different amount of activation pressure.
- Ras changes state relatively quickly, while SOS switching can be slower.
- Therefore the Ras output depends not only on the SOS state right now, but also
  on the recent history of SOS switching.

An analogy is a room with a fast thermometer and a slow-moving thermostat. The
thermometer reacts quickly, but its reading can still lag behind if the
thermostat keeps changing. Here, Ras is the fast part and SOS is the slower
driver.

The goal is not to claim that every cell uses exactly this mechanism. The goal
is to make the proposed mechanism precise enough that its assumptions and
consequences can be checked.

## What is being modeled

The Lean development uses a finite state space. In plain language, it keeps
track of:

- how many SOS molecules are bound in the relevant ways;
- how many Ras molecules are in the free Ras-GTP state; and
- the conservation rule that prevents impossible combinations of those counts.

The dynamics are split into two pieces:

1. `Q_fast` describes the quick Ras activation/deactivation dynamics while SOS
   is held fixed.
2. `Q_SOS` describes SOS binding and switching, which supplies the slower
   forcing of the Ras system.

The formalization also includes a history-filter representation. It captures
the idea that recent SOS states can still matter after the system has moved to
a new state.

## What Lean allows us to show

Lean is a proof checker. It is not being used here as a cell simulator, a
parameter-fitting program, or a substitute for experiments. The useful thing
it provides is a machine-checked chain of definitions and deductions.

In this project, Lean checks that:

- the basic activator-target equilibrium formulas are correct;
- finite birth/death chains satisfy the claimed detailed-balance relations;
- the Ras state space respects the conserved total counts;
- the frozen-SOS Ras equilibrium is exactly a binomial distribution;
- a constructive Poisson-equation solver exists for each finite Ras block;
- the block solvers can be assembled into one global fast-response corrector;
- both directions of the key fast-operator identity hold; and
- the operator statements imply the final stationary-distribution theorem.

The central theorem says that if `π` is stationary for the combined dynamics,

$$
(Q_{fast} + \varepsilon Q_{SOS})\pi = 0,
$$

then

$$
\pi - P\pi = -\varepsilon RQ_{SOS}\pi.
$$

Here is the plain-English translation:

- `Pπ` is the idealized distribution obtained by freezing SOS in each of its
  states and giving Ras its exact conditional equilibrium there.
- `π - Pπ` is the actual departure from that frozen-mixture picture.
- `Q_SOS π` is the disturbance caused by SOS switching.
- `R` describes how the fast Ras dynamics filter that disturbance.
- `ε` controls the relative speed of SOS switching.

So the error is not merely said to be “small.” It is identified exactly as a
specific switching disturbance passed through a specific fast-response
operator. The development also proves an exact total-variation formula and a
corresponding bound when the required operator estimates are supplied.

Compiling the project means Lean checks every term in this proof chain against
the pinned Lean toolchain. The source contains no `sorry`, `admit`, or added
`axiom` declarations. That does not mean the project has no assumptions: the
definitions, finite-state model, and theorem hypotheses are still assumptions
about the mathematical setup.

## What this does not show

The formalization does not, by itself:

- prove that the proposed biological mechanism is true in real cells;
- prove that the publication’s parameter choices are biologically correct;
- formalize the semantics of a BNGL parser or every detail of a simulator;
- create a new experimental observation; or
- replace numerical stationary calculations or experimental validation for
  larger and more realistic models.

Lean proves the implications of the formal assumptions. Whether those
assumptions are the right description of biology remains an empirical and
modeling question.

## What this adds beyond the manuscript

The manuscript develops the scientific model and its biological interpretation.
This formalization adds a different kind of result: an independently checkable
mathematical certificate for the finite-state stationary argument.

### Direct consequences of the formal structure

1. **It separates two possible sources of quantization.** Discrete SOS
   occupancy can create distinct preferred output levels, while finite Ras/SOS
   timescales and recent history determine how closely the live system follows
   those levels. These are related but not identical explanations.

2. **It gives an exact error decomposition.** The gap between the real
   stationary distribution and the frozen-SOS approximation is tied to a
   concrete operator expression. In principle, this can become a reusable
   certificate for deciding when the approximation is trustworthy.

3. **It turns a qualitative timescale story into a testable calculation.** The
   factor `ε` and the corrector `R` show where switching speed and fast Ras
   relaxation enter. This gives a principled way to ask how much lag or
   distortion should appear when SOS switching is sped up or slowed down.

4. **It avoids treating a giant matrix inverse as a black box.** The proof
   constructs the corrector from finite birth/death pieces and proves the
   needed forward and reverse identities. That makes the argument easier to
   inspect and potentially easier to reuse.

5. **It makes the approximation’s failure mode explicit.** If SOS switching
   creates a large forcing term, or if the fast Ras system filters it weakly,
   the frozen-mixture approximation can be poor even though each frozen block
   is understood exactly.

### Forward-looking implications — not new theorems yet

The formalization suggests several research directions, but these should be
treated as hypotheses until separately tested:

- Vary SOS dwell times or switching rates while keeping average occupancy
  similar. A change in the output would support a history/timescale effect,
  not just a static occupancy explanation.
- Use the exact decomposition to prioritize which rates or transitions need
  better experimental measurement.
- Apply the same proof pattern to other finite stochastic signaling systems
  with a fast internal response and a slower discrete driver.
- Use the proof boundary to make stronger claims easier to audit: each claim
  can be tied to explicit state-space, generator, and stationarity assumptions.

These implications extend the manuscript’s reach as a mathematical and
computational framework. They do not, without new simulations or experiments,
establish that the mechanism is universal or that it operates in a particular
biological context.

## Bottom line

The project says: “Here is a precise finite stochastic model for how discrete
SOS states and fast Ras dynamics can produce quantized-looking signaling, and
here is a machine-checked proof of exactly how the stationary distribution
differs from the frozen-SOS approximation.”

That is stronger than an informal derivation and more auditable than a result
that only appears as a numerical pattern. It is still a mathematical result
about a model—not the final word about what living cells do.
