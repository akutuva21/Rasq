import Mathlib
import StochasticQuantization.Core
import StochasticQuantization.Processivity

noncomputable section

/-!
# A quantitative slow/fast tracking rule

This file formalizes the next step beyond the frozen-occupancy peak formulas.

The biological question is simple:

> If SOS stays in one occupancy state for a while, does Ras have enough time to
> move close to the RasGTP level associated with that occupancy?

There are two clocks:

* the **Ras relaxation clock**, with rate `r`;
* the **SOS unbinding clock**, with rate `koff`.

If the SOS occupancy is fixed, the distance of the conditional Ras mean from its
new equilibrium shrinks like

    exp (-r * t).

If an SOS dwell time is exponentially distributed with unbinding rate `koff`, the
probability that the dwell lasts at least time `t` is

    exp (-koff * t).

Now ask for the SOS state to survive for `c` Ras relaxation times.  That means

    t = c / r.

At that time the remaining mean error is exactly

    exp (-c),

while the probability that the SOS state is still present is exactly

    exp (-c / Gamma),

where

    Gamma = r / koff.

This gives `Gamma` a direct interpretation:

* large `Gamma`: an SOS state usually lasts for many Ras response times;
* small `Gamma`: SOS changes before Ras can follow it.

For the Ras models in this repository at `n = 1` using the GTP-bound SOS off-rate:

* Model 1: `Gamma = 25`;
* Model 2: `Gamma = 70`;
* Model 3: `Gamma = 1/40 = 0.025`.

So Model 3 is not merely "less processive".  It lives on the opposite side of the
slow/fast regime: its SOS occupancy changes much faster than Ras can relax.

What this file DOES prove
-------------------------

The identities connecting relaxation time, exponential dwell survival, and
`Gamma` are checked algebraically in Lean.

What this file DOES NOT prove
-----------------------------

It does not yet construct the entire joint continuous-time Markov process for
SOS occupancy plus RasGTP and prove a stationary total-variation approximation.
That larger singular-perturbation theorem remains the next major mathematical
step.  The results here isolate and quantify the key local ingredient that such a
theorem must use.
-/

namespace StochasticQuantization

/-- A generic relaxation-rate / unbinding-rate ratio.

Biological reading: how many Ras relaxation rates fit inside one SOS unbinding
rate.  This is the same dimensionless idea as `persistenceRatio`, written directly
in terms of an already-computed target relaxation rate `r`. -/
def gamma (r koff : ℝ) : ℝ := r / koff

/-- Time corresponding to `c` target relaxation times. -/
def relaxationWindow (r c : ℝ) : ℝ := c / r

/-- Fraction of an initial mean displacement remaining after time `t` for a
first-order relaxation process with rate `r`. -/
def trackingErrorFraction (r t : ℝ) : ℝ := Real.exp (-r * t)

/-- Survival function for an exponential catalyst dwell time with unbinding rate
`koff`.  In the Ras interpretation, this is the probability that the current SOS
binding event lasts at least `t`. -/
def exponentialDwellSurvival (koff t : ℝ) : ℝ := Real.exp (-koff * t)

/-- Probability, under the exponential dwell-time model, that a catalyst remains
bound for at least `c` target relaxation times. -/
def surviveRelaxationWindow (r koff c : ℝ) : ℝ :=
  exponentialDwellSurvival koff (relaxationWindow r c)

/-- After exactly `c` relaxation times, a first-order target has reduced its mean
error by the universal factor `exp(-c)`, independent of the absolute rate scale. -/
theorem trackingError_after_relaxationWindow
    (r c : ℝ) (hr : r ≠ 0) :
    trackingErrorFraction r (relaxationWindow r c) = Real.exp (-c) := by
  unfold trackingErrorFraction relaxationWindow
  congr 1
  field_simp [hr]

/-- The probability that an exponential dwell survives `c` target relaxation
periods depends only on `c` and the dimensionless ratio `Gamma = r/koff`.

    P(dwell >= c/r) = exp(-c/Gamma).

This is the central quantitative slow/fast identity used in the README. -/
theorem surviveRelaxationWindow_eq_exp_neg_c_div_gamma
    (r koff c : ℝ) (hr : r ≠ 0) (hkoff : koff ≠ 0) :
    surviveRelaxationWindow r koff c = Real.exp (-c / gamma r koff) := by
  unfold surviveRelaxationWindow exponentialDwellSurvival relaxationWindow gamma
  congr 1
  field_simp [hr, hkoff]

/-- The same physical ratio can be read as mean dwell time divided by target
relaxation time. -/
theorem gamma_eq_dwell_div_relaxationTime
    (r koff : ℝ) (hr : r ≠ 0) (hkoff : koff ≠ 0) :
    gamma r koff = dwellTime koff / (1 / r) := by
  unfold gamma dwellTime
  field_simp [hr, hkoff]

/-- Speeding only the catalyst unbinding clock by `scale` divides `Gamma` by the
same factor.  This captures the Model 1 -> Model 3 loss of persistence when target
chemistry is unchanged. -/
theorem scaling_unbinding_divides_gamma
    (scale r koff : ℝ) (hscale : scale ≠ 0) (hkoff : koff ≠ 0) :
    gamma r (scale * koff) = gamma r koff / scale := by
  unfold gamma
  field_simp [hscale, hkoff]

/-- For the frozen activator-target model, the direct `gamma` definition agrees
with the existing occupancy-specific `persistenceRatio`. -/
theorem gamma_relaxationRate_eq_persistenceRatio
    (n : ℕ) (kAct kTargetOff kCatalystOff : ℝ) :
    gamma (relaxationRate n kAct kTargetOff) kCatalystOff =
      persistenceRatio n kAct kTargetOff kCatalystOff := by
  rfl

/-- Model 1 at n=1 using the GTP-bound SOS off-rate has Gamma = 25. -/
example : gamma ((1 / 100 : ℝ) + 1 / 400) (1 / 2000) = 25 := by
  norm_num [gamma]

/-- Model 2 at n=1 has Gamma = 70 because RasGAP makes Ras relax faster while the
SOS dwell time is unchanged. -/
example : gamma ((1 / 100 : ℝ) + 1 / 40) (1 / 2000) = 70 := by
  norm_num [gamma]

/-- Model 3 has Gamma = 1/40: the target chemistry is Model 1-like, but SOS leaves
1000 times faster. -/
example : gamma ((1 / 100 : ℝ) + 1 / 400) (1 / 2) = 1 / 40 := by
  norm_num [gamma]

/-- After three Ras relaxation times, Model 1's probability of still being in the
same GTP-bound SOS dwell is `exp(-3/25)`.  Three relaxation times leave only
`exp(-3)` of the initial mean displacement. -/
example :
    surviveRelaxationWindow ((1 / 100 : ℝ) + 1 / 400) (1 / 2000) 3 =
      Real.exp (-(3 : ℝ) / 25) := by
  norm_num [surviveRelaxationWindow, exponentialDwellSurvival, relaxationWindow]

/-- Model 2 is even more persistent: three relaxation times survive with
probability `exp(-3/70)`. -/
example :
    surviveRelaxationWindow ((1 / 100 : ℝ) + 1 / 40) (1 / 2000) 3 =
      Real.exp (-(3 : ℝ) / 70) := by
  norm_num [surviveRelaxationWindow, exponentialDwellSurvival, relaxationWindow]

/-- Model 3 is on the opposite time-scale regime: lasting three Ras relaxation
periods has probability `exp(-120)`. -/
example :
    surviveRelaxationWindow ((1 / 100 : ℝ) + 1 / 400) (1 / 2) 3 =
      Real.exp (-(120 : ℝ)) := by
  norm_num [surviveRelaxationWindow, exponentialDwellSurvival, relaxationWindow]


/-!
## Averaging over the random dwell duration

The previous theorem asks whether a dwell survives a chosen number of target
response times.  We can also average over *all possible* exponentially distributed
dwell durations.

If the target's remaining mean error after time `t` is `exp(-r*t)` and dwell
durations have density `koff * exp(-koff*t)`, then the average remaining error at
the instant of unbinding is

    koff / (koff + r) = 1 / (1 + Gamma).

Therefore the average fraction of the move toward the current conditional level
that is completed before unbinding is

    r / (koff + r) = Gamma / (1 + Gamma).

This is especially intuitive for the Ras models:

* Model 1: 25/26  ≈ 96.2% of the conditional mean move completed per GTP-bound dwell;
* Model 2: 70/71  ≈ 98.6%;
* Model 3:  1/41  ≈  2.44%.

Unlike a heuristic ratio, the integral below directly averages the exponential
relaxation law over the exponential dwell-time density.
-/

open Set MeasureTheory

/-- Standard exponential dwell-time density on positive times. -/
def exponentialDwellDensity (koff t : ℝ) : ℝ :=
  koff * Real.exp (-koff * t)

/-- Density-weighted mean fraction of the old target-state displacement that
remains when the catalyst dwell ends. -/
def meanResidualAtDwellEnd (r koff : ℝ) : ℝ :=
  ∫ t : ℝ in Set.Ioi 0,
    trackingErrorFraction r t * exponentialDwellDensity koff t

/-- Averaging exponential target relaxation over an exponential catalyst dwell
gives the exact residual fraction `koff/(koff+r)`. -/
theorem meanResidualAtDwellEnd_eq
    (r koff : ℝ) (hr : 0 < r) (hkoff : 0 < koff) :
    meanResidualAtDwellEnd r koff = koff / (koff + r) := by
  unfold meanResidualAtDwellEnd trackingErrorFraction exponentialDwellDensity
  have hfun :
      (fun t : ℝ => Real.exp (-r * t) * (koff * Real.exp (-koff * t))) =
        (fun t : ℝ => koff * Real.exp (-(r + koff) * t)) := by
    funext t
    calc
      Real.exp (-r * t) * (koff * Real.exp (-koff * t)) =
          koff * (Real.exp (-r * t) * Real.exp (-koff * t)) := by ring
      _ = koff * Real.exp ((-r * t) + (-koff * t)) := by
          rw [Real.exp_add]
      _ = koff * Real.exp (-(r + koff) * t) := by ring_nf
  rw [hfun, integral_const_mul]
  rw [integral_exp_mul_Ioi (a := -(r + koff)) (by linarith) 0]
  simp
  have hsum : koff + r ≠ 0 := ne_of_gt (add_pos hkoff hr)
  have hden : -koff + -r = -(koff + r) := by ring
  rw [hden]
  field_simp [hsum]

/-- The average fraction of the conditional mean move completed before unbinding. -/
def meanCompletedAtDwellEnd (r koff : ℝ) : ℝ :=
  1 - meanResidualAtDwellEnd r koff

/-- The average completed fraction is `Gamma/(1+Gamma)`.  This gives Gamma a very
direct biological meaning: it predicts how much of the occupancy-specific Ras move
is typically completed during one exponentially distributed SOS dwell. -/
theorem meanCompletedAtDwellEnd_eq_gamma_fraction
    (r koff : ℝ) (hr : 0 < r) (hkoff : 0 < koff) :
    meanCompletedAtDwellEnd r koff = gamma r koff / (1 + gamma r koff) := by
  unfold meanCompletedAtDwellEnd
  rw [meanResidualAtDwellEnd_eq r koff hr hkoff]
  unfold gamma
  have hk0 : koff ≠ 0 := ne_of_gt hkoff
  have hsum : koff + r ≠ 0 := ne_of_gt (add_pos hkoff hr)
  field_simp [hk0, hsum]
  ring

/-- Model 1 using the GDP-bound SOS off-rate: 5/7 of the move is completed on
average.  The slower GTP-bound off-rate below gives a stronger 25/26 value. -/
example :
    meanCompletedAtDwellEnd ((1 / 100 : ℝ) + 1 / 400) (1 / 200) = 5 / 7 := by
  rw [meanCompletedAtDwellEnd_eq_gamma_fraction]
  · norm_num [gamma]
  · norm_num
  · norm_num

/-- Model 1: averaged over a GTP-bound SOS dwell, 25/26 of the conditional mean
move is completed. -/
example :
    meanCompletedAtDwellEnd ((1 / 100 : ℝ) + 1 / 400) (1 / 2000) = 25 / 26 := by
  rw [meanCompletedAtDwellEnd_eq_gamma_fraction]
  · norm_num [gamma]
  · norm_num
  · norm_num

/-- Model 2 using the GDP-bound SOS off-rate: 7/8 of the move is completed on
average. -/
example :
    meanCompletedAtDwellEnd ((1 / 100 : ℝ) + 1 / 40) (1 / 200) = 7 / 8 := by
  rw [meanCompletedAtDwellEnd_eq_gamma_fraction]
  · norm_num [gamma]
  · norm_num
  · norm_num

/-- Model 2: 70/71 of the conditional mean move is completed on average for a
GTP-bound SOS dwell. -/
example :
    meanCompletedAtDwellEnd ((1 / 100 : ℝ) + 1 / 40) (1 / 2000) = 70 / 71 := by
  rw [meanCompletedAtDwellEnd_eq_gamma_fraction]
  · norm_num [gamma]
  · norm_num
  · norm_num

/-- Model 3 using the GDP-bound SOS off-rate: only 1/401 of the conditional
mean move is completed on average. -/
example :
    meanCompletedAtDwellEnd ((1 / 100 : ℝ) + 1 / 400) 5 = 1 / 401 := by
  rw [meanCompletedAtDwellEnd_eq_gamma_fraction]
  · norm_num [gamma]
  · norm_num
  · norm_num

/-- Model 3: even with the slower GTP-bound SOS off-rate, only 1/41 of the
conditional mean move is completed on average. -/
example :
    meanCompletedAtDwellEnd ((1 / 100 : ℝ) + 1 / 400) (1 / 2) = 1 / 41 := by
  rw [meanCompletedAtDwellEnd_eq_gamma_fraction]
  · norm_num [gamma]
  · norm_num
  · norm_num

end StochasticQuantization
