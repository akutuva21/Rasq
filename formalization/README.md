# Stochastic quantization in Ras/SOS — ELI15 guide

This folder adds a standalone Lean 4 formalization and numerical certificate suite
to the original Ras activation repository.

> **Archive boundary.** This ZIP contains and builds the core formalization, but
> it does not contain the later finite-state stationary-theorem modules described
> in Sections 11–15 below. Those sections are retained as provenance for the
> larger development, not as claims that this checkout can currently verify. See
> [`ARCHIVE_INTEGRITY.md`](ARCHIVE_INTEGRITY.md) for the exact boundary.

You do **not** need to know Lean or advanced probability to understand the point.
The biological question is:

> **How can Ras signaling form discrete-looking activity levels when the chemistry
> is stochastic and the deterministic model does not need two stable states?**

The shortest answer is:

> **A small integer number of SOS-bound complexes creates discrete activation
> drives, while Ras responds with finite speed and therefore remembers recent SOS
> binding history.**

That gives two complementary mathematical pictures:

```text
slow SOS switching                     native Ras dynamics
------------------                     -------------------
current SOS block                      recent SOS history
      |                                      |
      v                                      v
exact binomial Ras equilibrium         fading biochemical memory
      |                                      |
      v                                      v
mixture of discrete peaks              filtered processive bursts
```

The first picture becomes exact as the SOS clock is made slow.  The second picture
is more useful for the native Model 1/2 trajectories, where current SOS occupancy
alone does not tell the whole story.

---

## 1. What Lean is doing

Lean is a very strict proof checker.  It can check that a conclusion follows from
specified equations without silently accepting an algebra mistake.

It **cannot** prove that the biological model is true.  Experiments decide that.

So the workflow is:

```text
biology -> mathematical model -> Lean checks the math -> experiments judge biology
```

The scientifically interesting part is the mathematical mechanism.  Lean is
quality control for that mechanism.

---

## 2. Start with the simplest activator-target model

Suppose exactly `n` activators are active for a while.  Each target switches
between inactive and active:

```text
inactive -- n*kAct --> active
inactive <-- kOff ---- active
```

The equilibrium chance that one target is active is

$$
p_n=\frac{n k_{Act}}{n k_{Act}+k_{Off}}.
$$

For `T` targets, the mean number active is

$$
\boxed{
\mu_n=T\frac{n k_{Act}}{n k_{Act}+k_{Off}}
}.
$$

This is not just a fitted peak location.  It follows from balancing activation and
deactivation flux.

`Core.lean` proves the basic algebra.

---

## 3. The frozen stochastic distribution is binomial

At fixed `n`, let `m` be the number of active targets.  Then

```text
m -> m+1  at rate (T-m)*n*kAct
m -> m-1  at rate m*kOff
```

This is a finite birth/death chain.  Its stationary probabilities are binomial.
In unnormalized form,

$$
w_m={T\choose m}(n k_{Act})^m k_{Off}^{T-m}.
$$

After normalization,

$$
P(M=m)={T\choose m}p_n^m(1-p_n)^{T-m}.
$$

`BirthDeath.lean` proves detailed balance.  `RasFastBlock.lean` writes the closed
binomial weights, normalization, detailed balance, and mean for the Ras
specialization.

---

## 4. Why discrete peaks can appear

In the weak-activation limit,

$$
\mu_n\approx n\Delta,
\qquad
\Delta=\frac{T k_{Act}}{k_{Off}}.
$$

So the levels are approximately

$$
0,\Delta,2\Delta,3\Delta,\ldots
$$

But they are **not exactly equally spaced**.  The exact neighboring spacing is

$$
\boxed{
\mu_{n+1}-\mu_n=
\frac{T k_{Act}k_{Off}}
{(n k_{Act}+k_{Off})((n+1)k_{Act}+k_{Off})}
}.
$$

As activation saturates, those levels crowd together.

This already tells us that “integer catalyst count” is not enough for visible
quantization.  The peaks also need to be far enough apart relative to their
stochastic widths.

---

## 5. Map that idea onto the actual Ras/SOS BNGL model

The Ras model has four Ras pools:

```text
free RasGDP
free RasGTP
GDP-Ras:SOS
GTP-Ras:SOS
```

The BNGL rules give six one-way count transitions after the two reversible
binding rules are split into forward and reverse directions:

```text
FAST, inside one frozen SOS block
1. free RasGDP -> free RasGTP      processive SOS catalysis
2. free RasGTP -> free RasGDP      RasGAP deactivation

SLOW/BLOCK-CHANGING
3. free RasGDP -> GDP-Ras:SOS      SOS binding
4. free RasGTP -> GTP-Ras:SOS      SOS binding
5. GDP-Ras:SOS -> free RasGDP      SOS unbinding
6. GTP-Ras:SOS -> free RasGTP      SOS unbinding
```

A semantic detail matters: the BNGL rule

```text
RasDephos: Ras(sos,a~p) -> Ras(sos,a~0)
```

has an **unbound** `sos` site.  Therefore bound GTP-Ras:SOS does not directly
undergo this deactivation reaction.  It must unbind first.

`RasGenerator.lean` encodes the exact count-level propensities.  `RasSlowForward.lean`
encodes the probability-flow form of reactions 3–6.

---

## 6. What exactly must be frozen?

Freezing only the total number of bound SOS molecules is not quite enough.
The correct frozen block is

```text
(boundGDP, boundGTP)
```

because GDP-bound and GTP-bound Ras:SOS have different unbinding rates and bound
GTP cannot directly deactivate.

Inside one fixed block, define

$$
B=boundGDP+boundGTP,
\qquad
F=RasTotal-B.
$$

The only moving coordinate is free RasGTP `m`:

$$
m\to m+1
\quad\text{at rate}\quad
(F-m)B k_{cat1},
$$

$$
m\to m-1
\quad\text{at rate}\quad
m k_{cat2}.
$$

So every frozen Ras block is exactly a finite birth/death chain with a binomial
equilibrium.

---

## 7. Frozen Ras peak geometry

For total bound SOS count `B`, the mean free RasGTP in that frozen block is

$$
\boxed{
\mu_B=(R_T-B)
\frac{B k_{cat1}}{B k_{cat1}+k_{cat2}}
}.
$$

The factor `R_T-B` appears because every Ras:SOS complex removes one Ras molecule
from the free target pool.

The exact spacing is

$$
\boxed{
\mu_{B+1}-\mu_B=
\frac{k_{cat1}[k_{cat2}(R_T-2B-1)-k_{cat1}B(B+1)]}
{(Bk_{cat1}+k_{cat2})((B+1)k_{cat1}+k_{cat2})}
}.
$$

The numerator shows two separate ways peaks crowd:

1. **saturation** from large `B*kcat1`;
2. **sequestration** because more bound SOS leaves fewer free Ras targets.

For the repository parameters, the first few predicted free-RasGTP means are:

| bound SOS | Model 1 | Model 2 | Model 3 |
|---:|---:|---:|---:|
| 0 | 0 | 0 | 0 |
| 1 | 799 | 285 | 799 |
| 2 | 887 | 444 | 887 |
| 3 | 920 | 544 | 920 |
| 4 | 937 | 613 | 937 |
| 5 | 948 | 663 | 948 |

Model 2's faster RasGAP opens the dynamic range.  Model 3 has exactly the same
frozen peak geometry as Model 1 because its Ras activation/deactivation chemistry
is unchanged.

`Ras.lean` proves these identities.

---

## 8. Model 3 changes the clock, not the frozen geometry

Model 3 multiplies both SOS association and dissociation rates by 1000 while
leaving `kcat1` and `kcat2` unchanged.

Therefore:

$$
\frac{k_{on}'}{k_{off}'}=\frac{k_{on}}{k_{off}},
$$

so the simple binding ratio is preserved, but

$$
\tau_{dwell}'=\frac{\tau_{dwell}}{1000}.
$$

At the operator level the same fact is

$$
\boxed{
Q_{Model3,\epsilon}=Q_{Model1,1000\epsilon}
}
$$

for the same SOS concentration.

This is why Model 3 can preserve the *possible frozen levels* while destroying the
time needed to occupy them.

---

## 9. One SOS dwell: does Ras have time to follow it?

If a temporary SOS state pushes Ras toward target `mu`, the mean relaxes as

$$
x(t)=\mu+(x_0-\mu)e^{-rt},
$$

with

$$
r=B k_{cat1}+k_{cat2}.
$$

Define

$$
\Gamma=\frac{r}{k_{off}^{SOS}}.
$$

Then an exponential SOS dwell survives for `c` Ras response times with probability

$$
\boxed{e^{-c/\Gamma}}.
$$

Averaging over all possible dwell lengths gives an intuitive quantity:

$$
\boxed{
\text{mean fraction of the Ras move completed before unbinding}
=\frac{\Gamma}{1+\Gamma}
}.
$$

At one bound SOS:

| model / SOS state | mean move completed |
|---|---:|
| Model 1, GDP-bound | 71.4% |
| Model 1, GTP-bound | 96.2% |
| Model 2, GDP-bound | 87.5% |
| Model 2, GTP-bound | 98.6% |
| Model 3, GDP-bound | 0.249% |
| Model 3, GTP-bound | 2.44% |

So a typical Model 3 dwell is far too short for Ras to approach that dwell's
frozen target.

`SlowFast.lean` proves the identities.

---

## 10. A sequence of dwells: Ras is a fading-memory filter

For one dwell write

$$
a=e^{-r\Delta t}.
$$

Then

$$
\boxed{x_{after}=a x_{before}+(1-a)\mu}.
$$

For two dwells,

$$
\boxed{
x_{final}=a_1a_0x_{initial}
+(1-a_1)\mu_1+a_1(1-a_0)\mu_0.
}
$$

The older target `mu_0` is multiplied by the newer factor `a_1`, so newer events
progressively erase older information.

For any finite shared history, two initial conditions satisfy

$$
\boxed{
x_{final}^{(1)}-x_{final}^{(2)}
=\left(\prod_i a_i\right)
(x_{initial}^{(1)}-x_{initial}^{(2)}).
}
$$

That is a precise mathematical meaning of **fading biochemical memory**.

`HistoryFilter.lean` proves these finite-history identities.

### Does it describe the stored SSA trajectories?

Using only the stored sampled SOS occupancy sequence after initialization:

| Model | SOS | history RMSE | instantaneous frozen RMSE | correlation |
|---|---:|---:|---:|---:|
| Model 1 | 10 nM | 11.54 | 176.01 | 0.9996 |
| Model 2 | 30 nM | 15.80 | 43.10 | 0.9980 |
| Model 3 | 10 nM | 32.50 | 458.53 | 0.5459 |

Models 1 and 2 are reconstructed extremely well by the simple fading-memory
recurrence.  Model 3 switches much faster than the stored ~10 s sampling interval,
so many SOS events occur between recorded points and cannot be reconstructed from
the saved occupancy samples.

---

## 11. The later exact stationary extension (not included in this ZIP)

The following sections describe a later extension whose prerequisite Lean source
files are absent from this archive. They are not part of the default `lake build`
target and are not machine-checked here.

Now consider the whole finite stochastic Ras count process.

Write its forward generator as

$$
Q_\epsilon=Q_{fast}+\epsilon Q_{SOS}.
$$

`Q_fast` contains reactions 1–2.  `Q_SOS` contains reactions 3–6.  Changing
`epsilon` speeds or slows **only** SOS block switching.

Define `P` as follows:

> Keep the total probability mass assigned to every `(boundGDP,boundGTP)` block,
> but replace the free-RasGTP distribution inside that block by its exact frozen
> binomial equilibrium.

Define `R` as the fast Poisson corrector.  It measures how strongly a within-block
distribution responds to a forcing away from equilibrium.

In the larger development, the intended result for any stationary distribution
`pi` was the exact identity

$$
\boxed{
\pi-P\pi=-\epsilon RQ_{SOS}\pi.
}
$$

This is the key result.

It says:

> **The difference between the real stationary Ras distribution and the ideal
> frozen-SOS mixture is exactly the SOS switching forcing passed through Ras's
> biochemical memory operator.**

This identity remains true even when the frozen-mixture approximation is bad.

---

## 12. Why no giant matrix inverse was intended

A naive proof might imagine inverting an enormous generator matrix.
That is unnecessary.

Inside one frozen block the free-RasGTP states form a line:

```text
0 <-> 1 <-> 2 <-> ... <-> F
```

The Poisson equation can be solved using cumulative probability flux through
neighboring edges.  The implementation uses an O(F) path recurrence and then
removes the stationary null mode by forcing the correction to have zero block
mass.

`BirthDeathPoisson.lean`, `RasBlockPoisson.lean`, and
`RasGlobalCorrector.lean` contain this construction.

The numerical certificate uses a numerically stable version of the same edge-flux
idea: it anchors near the binomial mode and sweeps outward rather than always
starting at state 0.

---

## 13. Why the reverse Poisson identity was intended to be legitimate

The constructive block solve directly gives

$$
Q_{fast}R=I-P.
$$

The stationary theorem needs

$$
RQ_{fast}=I-P.
$$

`RasReversePoisson.lean` derives the reverse order using finite-dimensional linear
algebra.  The key trick is to define

$$
A=Q_{fast}+P,
\qquad
B=R+P.
$$

The already-proved block properties give `AB=I`.  On a finite-dimensional vector
space, a one-sided inverse is also a two-sided inverse, so `BA=I`.  Expanding that
identity gives the desired reverse Poisson equation.

This is the step that turns the local hallway-like birth/death solves into the
full stationary theorem.

---

## 14. Total variation: the intended extension

For two finite probability distributions,

$$
TV(p,q)=\frac12\sum_s|p(s)-q(s)|.
$$

`FiniteTV.lean` defines this directly on the finite Ras state space.
The stationary theorem becomes

$$
\boxed{
TV(\pi,P\pi)
=\frac{|\epsilon|}{2}\|RQ_{SOS}\pi\|_1.
}
$$

If `R` and `Q_SOS` have L1 bounds `C_R` and `C_S`, then

$$
\boxed{
TV(\pi,P\pi)\le
\frac{|\epsilon|}{2}C_RC_S.
}
$$

So the frozen-mixture approximation becomes first-order accurate as SOS switching
is slowed:

$$
TV=O(\epsilon).
$$

---

## 15. Recorded numerical certificate on the real 1000-Ras count model

The tables in this section are retained generated data from the larger
development. The corresponding CTMC script is not included in this ZIP, so these
results have not been freshly reproduced by the current checkout.

The symbolic Lean state space is **untruncated** for any fixed total Ras count.
For numerical stationary solves only, `full_ras_ctmc_analysis.py` caps total bound
SOS at 10 while retaining all 1000 Ras molecules and every free-RasGTP count inside
each retained block.  That gives 65,626 states.

At the native high-SOS conditions:

| model | TV to frozen mixture | exact-identity relative L1 error | cap mass |
|---|---:|---:|---:|
| Model 1, 10 nM | 0.59656 | 2.7e-12 | 5.0e-7 |
| Model 2, 30 nM | 0.23570 | 4.9e-12 | 3.0e-4 |
| Model 3, 10 nM | 0.80793 | 7.5e-10 | 4.6e-7 |

The frozen-mixture approximation is therefore **not** especially good at the
native speeds, particularly for Models 1 and 3.  That is not a failure of the
theorem.  The exact identity explains *why* they are far away.

The numerical cap is also controlled.  For Model 2 at 30 nM:

| bound-SOS cap | states | probability on cap | TV |
|---:|---:|---:|---:|
| 8 | 44,805 | 2.54e-3 | 0.235982 |
| 10 | 65,626 | 2.97e-4 | 0.235701 |
| 12 | 90,363 | 2.56e-5 | 0.235673 |

So the conclusion is not being manufactured by the numerical boundary.

### Slow the SOS clock

For Model 1:

| epsilon | TV |
|---:|---:|
| 1 | 0.596559 |
| 0.3 | 0.335110 |
| 0.1 | 0.141807 |
| 0.03 | 0.046673 |
| 0.01 | 0.015991 |

For Model 2:

| epsilon | TV |
|---:|---:|
| 1 | 0.235701 |
| 0.3 | 0.085231 |
| 0.1 | 0.030123 |
| 0.03 | 0.009230 |
| 0.01 | 0.003095 |

Small-`epsilon` log-log slopes are approximately **0.947** and **0.988**,
respectively.  The theorem predicts the limiting slope 1.

Model 3 at `epsilon=0.001` has the exact Model 1 SOS clock and numerically returns
the same TV value, `0.596559`.

See `generated/FULL_RAS_CTMC_REPORT.md` for the full certificate.

---

## 16. Deterministic bistability is a separate question

The stochastic mechanism above does not require deterministic bistability.
For the reduced positive steady-state equations, define

$$
x=\frac{free\ RasGTP}{free\ RasGDP}.
$$

The steady-state relations reduce to

$$
A x^2+B x-C=0,
\qquad A>0,\ C>0.
$$

Because the constant term is negative, such a quadratic has at most one positive
root.  `RasEquilibrium.lean` proves this algebraically.

So the model can have stochastic digital/quantized structure without requiring
two deterministic positive steady states.

---

## 17. What is actually proved, and what is not?

### Lean theorem source included and checked

The current checkout machine-checks the core modules listed in
[`ARCHIVE_INTEGRITY.md`](ARCHIVE_INTEGRITY.md): frozen activator-target algebra,
finite birth/death balance and path Poisson identities, processivity and dwell-time
rescaling, slow/fast tracking and dwell averages, Ras peak geometry and Model 1/3
rescaling, and reduced deterministic positive-equilibrium uniqueness.

The build contains no `sorry`, `admit`, or `axiom` declarations in the retained
source. It does **not** certify the absent stationary extension, the generated
numerical reports, BNGL parser semantics, or biological truth.

---

## 18. How to verify it

Locally, using the isolated Lean installation described in
[`ARCHIVE_INTEGRITY.md`](ARCHIVE_INTEGRITY.md):

```bash
cd formalization
ELAN_HOME=/private/tmp/bng3-elan-home \
  /private/tmp/bng3-elan-home/bin/lake build
python test_math_identities.py
python ras_quantization_analysis.py
```

---

## 19. File map

```text
formalization/
├── README.md
├── ARCHIVE_INTEGRITY.md
├── PROOF_STATUS.md
├── lakefile.toml
├── lean-toolchain
├── StochasticQuantization.lean
├── test_math_identities.py
├── ras_quantization_analysis.py
│
├── StochasticQuantization/
│   ├── Core.lean
│   ├── BirthDeath.lean
│   ├── BirthDeathPoisson.lean
│   ├── Processivity.lean
│   ├── SlowFast.lean
│   ├── Ras.lean
│   ├── RasEquilibrium.lean
│   ├── RasGlobalPoisson.lean        # preserved, unavailable dependency
│   ├── RasSlowForward.lean          # preserved, unavailable dependency
│   ├── RasReversePoisson.lean       # preserved, unavailable dependency
│   └── RasFullStationary.lean       # preserved, unavailable dependency
│
└── generated/
    ├── RAS_FORMAL_MATH_REPORT.md
    ├── FULL_RAS_CTMC_REPORT.md
    ├── ras_full_ctmc_summary.csv
    ├── ras_ctmc_cap_convergence.csv
    ├── ras_full_ctmc_stationary_scaling.csv
    ├── ras_history_filter_reconstruction.csv
    └── other formula/trajectory CSVs
```

If you only want the scientific story, read sections **5–16** and then
`generated/FULL_RAS_CTMC_REPORT.md`.
