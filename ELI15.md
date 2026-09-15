# Ras stochastic quantization — ELI15

## The one-sentence version

This project asks why a noisy molecular switch can produce a small number of
reliable-looking output levels, and uses Lean to prove an exact statement about
how the fast Ras reaction and its slower molecular driver fit together.

## What the project is trying to explain

Ras is a small molecular signal carrier. Son of Sevenless (SOS) helps turn Ras
on. Inside a cell, the individual molecules do not behave like clockwork: they
bind, unbind, and change state at random times.

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

1. `Q_fast` describes the quick Ras activation and deactivation dynamics while
   the SOS state is held fixed.
2. `Q_SOS` describes SOS binding and switching, which supplies the slower
   forcing of the Ras system.

The symbols are just compact names for these two kinds of change. They do not
mean that the cell has two separate machines. They are a way of separating the
fast reaction from the slower change in its molecular driver.

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
- the frozen SOS Ras equilibrium is exactly a binomial distribution;
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

1. **It separates two possible sources of quantization.** Discrete occupancy of
   SOS can create distinct preferred output levels, while the relative timing
   between Ras and SOS determines how closely the
   live system follows those levels. These are related but not identical
   explanations.

2. **It gives an exact error decomposition.** The gap between the real
   stationary distribution and the frozen-driver approximation is tied to a
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

### New theory layer now kernel-checked

The formalization now goes beyond the stationary defect and develops the
mechanism as a general theory of transmitting a discrete molecular state through
a biochemical readout.  These additions are integrated into the Lean target and
are checked by the pinned Lean 4.31.0 / Mathlib v4.31.0 build.

1. **Decoding instead of histogram inspection.**  A generic decoder theorem
   bounds live molecular-state decoding error by frozen/reference decoder error
   plus the total-variation mismatch between the live and reference laws.  For
   Ras, this
   composes directly with the exact stationary tracking defect.

2. **The opposite timescale limit.**  The same stationary corrector theorem is
   reused with switching as the fast operator.  This makes slow-switch tracking
   and fast-switch averaging two orientations of one finite-state theorem.  The
   existing fading-memory filter also proves an exact minimal averaging formula.

3. **Mesoscopic signaling.**  The source proves an exact inverse-area law for a
   standardized level-resolution quantity and combines it with a minimum-target
   requirement to define a finite mesoscopic window.

4. **Processivity depends on the dwell distribution.**  For active window `W`
   and readout relaxation rate `r`, the residual quantity is `E[exp(-r W)]`.
   The source proves that two dwell laws can have the same mean residence time
   but different effective processivity, and that activation latency can only
   reduce the completed biochemical move under physical rates.

5. **Feedback and catalytic classes are separated.**  Slow microstates can be
   grouped by the catalytic capacity seen by the fast readout.  Redistribution
   inside a catalytic class cannot change the downstream codeword mixture.  In
   Ras, changing only SOS binding/unbinding speed leaves the full frozen Ras
   codeword unchanged.

6. **Spatial detail is reduced to target accessibility.**  A minimal
   reaction-versus-mixing theorem gives the accessible target fraction
   `1/(1+Da)`, where `Da` is the Damköhler number comparing local reaction speed
   with mixing speed, and explicit depletion bounds.  This captures the simple
   idea that a target must be reachable before it can be used.

## What the bigger message means

Together these pieces support a more careful interpretation of quantized-looking
signaling. The project is not fundamentally about seeing multiple histogram
peaks. A histogram is only the final pile of measurements; it does not tell us
why the measurements separated.

The deeper question is:

> When can a biochemical system preserve and transmit a **discrete molecular
> state without bistability**?

“Without bistability” is important. Bistability means that a system has two
self-maintaining modes and can stay in either one. This project studies a
different possibility: a changing molecular input can create distinct output
levels even when the reaction network does not contain two self-sustaining
switches.

There are at least three different ways this kind of message can fail:

1. **The frozen states may overlap.** If two molecular states produce nearly
   the same Ras output even when the system has plenty of time to settle, then
   no observer can reliably tell them apart. The problem is with the output
   patterns themselves.

2. **The Ras readout may not keep up.** The frozen outputs may be very
   different, but SOS may switch before Ras has time to respond.
   Then the cell is being asked to read a message that keeps changing before
   the readout finishes. The problem is timing, not lack of distinct states.

3. **The targets may not be reachable.** A model may count a large pool of
   possible targets, while local crowding, reaction, or slow mixing makes only
   part of that pool available. The problem is physical access, not the
   information encoded by the molecular state.

These failure modes can look similar if we only inspect a histogram. The formal
decomposition keeps them separate. That matters because each one calls for a
different remedy: change the molecular states, change the timing, or improve
access to the targets.

## Why this matters to cell biologists and everyone else

For cell biologists, this gives a short list of experimentally meaningful
questions:

- If two conditions have the same average SOS occupancy, do they
  still produce the same Ras signal when their dwell times are different?
- If SOS switching is slowed down, does Ras become more faithful to
  the current molecular state?
- If switching is sped up, does Ras report an average over many states instead
  of one state at a time?
- Are the targets counted by the model actually accessible where the reaction
  takes place?
- Can the same output distribution come from different hidden molecular states?

These questions help design experiments that change one feature at a time. They
also warn against treating a good-looking collection of peaks as proof of a
particular mechanism. A peak can come from discrete occupancy, delayed
tracking, or limited access, and those explanations make different predictions
when timing or location is changed.

The broader community can use the same idea in other noisy systems. A cell is
not the only place where a changing discrete input must pass through a slower,
imperfect readout. Similar questions arise in immune-cell decisions,
developmental signals, synthetic biology circuits, and engineered sensors.

The Lean proofs add another practical benefit: they make the assumptions
visible. Someone reusing the framework can see exactly which conclusions require
a finite state space, a conserved quantity, a timescale separation, or an
accessible target pool. This makes it harder to accidentally turn a useful model
result into an unsupported claim about all cells.

So the larger lesson is not “Ras always makes digital signals.” It is:

> Discrete information can survive noisy chemistry without a permanent
> on/off switch, but only when the molecular states are distinguishable, the
> readout can keep up, and the relevant targets are physically available.

The complete repository build currently succeeds across 8,588 Lake jobs.  That
means Lean has checked the formal statements and proofs in this branch; it does
not turn the model assumptions into experimental facts.

## Bottom line

The project now has two levels. The first is the exact finite Ras and Son of
Sevenless stationary identity. The second extracts a reusable theory of
discrete-state biochemical transmission from that example. Lean is being used
to expose which assumptions actually imply those statements; it is not being
used as a simulator or as a substitute for experiments.
