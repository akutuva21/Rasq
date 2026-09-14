import Mathlib

noncomputable section

/-!
# Core mathematics of a frozen-occupancy activator-target module

Biological picture
------------------
Hold the number `n` of active/processive catalysts fixed for long enough that a
large pool of target molecules can relax.  Each inactive target is activated at
rate `n * kAct`, and each active target deactivates at rate `kOff`.

For one target molecule the equilibrium active fraction is

    p_n = n*kAct / (n*kAct + kOff).

For `targetTotal` independent targets, the conditional mean is

    mu_n = targetTotal * p_n.

The finite stochastic model has a binomial conditional distribution.  The file
`BirthDeath.lean` verifies the detailed-balance recurrence underlying that claim;
this file focuses on the exact algebra of the peak locations.
-/

namespace StochasticQuantization

/-- Effective activation rate of one target when exactly `n` catalysts are active. -/
def effectiveActivationRate (n : ℕ) (kAct : ℝ) : ℝ := (n : ℝ) * kAct

/-- Conditional equilibrium active fraction of a target at frozen catalyst count `n`. -/
def activationFraction (n : ℕ) (kAct kOff : ℝ) : ℝ :=
  effectiveActivationRate n kAct / (effectiveActivationRate n kAct + kOff)

/-- Conditional mean number of active targets. -/
def conditionalMean (targetTotal : ℝ) (n : ℕ) (kAct kOff : ℝ) : ℝ :=
  targetTotal * activationFraction n kAct kOff

/-- Conditional binomial variance for an independent target pool. -/
def conditionalVariance (targetTotal : ℝ) (n : ℕ) (kAct kOff : ℝ) : ℝ :=
  let p := activationFraction n kAct kOff
  targetTotal * p * (1 - p)

/-- Low-saturation, equally-spaced approximation: `n * Delta`, where
`Delta = targetTotal * kAct / kOff`. -/
def linearQuantumMean (targetTotal : ℝ) (n : ℕ) (kAct kOff : ℝ) : ℝ :=
  (n : ℝ) * targetTotal * kAct / kOff

/-- The nominal one-catalyst quantum in the unsaturated regime. -/
def nominalQuantum (targetTotal kAct kOff : ℝ) : ℝ :=
  targetTotal * kAct / kOff

/-- The target relaxation rate at frozen catalyst count `n`.
The deterministic conditional mean relaxes at this rate. -/
def relaxationRate (n : ℕ) (kAct kOff : ℝ) : ℝ :=
  effectiveActivationRate n kAct + kOff

/-- The exact conditional fraction is the unique solution of activation/deactivation
flux balance.  This is the one-target version of the stationary calculation. -/
theorem activationFraction_flux_balance
    (n : ℕ) (kAct kOff : ℝ)
    (hden : effectiveActivationRate n kAct + kOff ≠ 0) :
    effectiveActivationRate n kAct * (1 - activationFraction n kAct kOff) =
      kOff * activationFraction n kAct kOff := by
  unfold activationFraction
  field_simp [hden]
  ring

/-- Conversely, any fraction satisfying the same balance equation must equal the
formula above, provided the total switching rate is nonzero. -/
theorem activationFraction_unique
    (n : ℕ) (kAct kOff p : ℝ)
    (hden : effectiveActivationRate n kAct + kOff ≠ 0)
    (hbal : effectiveActivationRate n kAct * (1 - p) = kOff * p) :
    p = activationFraction n kAct kOff := by
  unfold activationFraction
  field_simp [hden]
  nlinarith

/-- With positive deactivation and nonnegative activation, the conditional fraction
is nonnegative. -/
theorem activationFraction_nonneg
    (n : ℕ) (kAct kOff : ℝ) (hkAct : 0 ≤ kAct) (hkOff : 0 < kOff) :
    0 ≤ activationFraction n kAct kOff := by
  unfold activationFraction effectiveActivationRate
  positivity

/-- Under the same physical assumptions, the conditional fraction never exceeds 1. -/
theorem activationFraction_le_one
    (n : ℕ) (kAct kOff : ℝ) (hkAct : 0 ≤ kAct) (hkOff : 0 < kOff) :
    activationFraction n kAct kOff ≤ 1 := by
  unfold activationFraction effectiveActivationRate
  have hden : 0 < (n : ℝ) * kAct + kOff := by positivity
  apply (div_le_one hden).2
  linarith

/-- Exact spacing between neighboring frozen-occupancy peaks.

This is a central result: the peaks are *not* exactly equally spaced once target
activation begins to saturate.  Equal spacing is the low-saturation limit. -/
theorem adjacentSpacing_exact
    (targetTotal : ℝ) (n : ℕ) (kAct kOff : ℝ)
    (hkAct : 0 ≤ kAct) (hkOff : 0 < kOff) :
    conditionalMean targetTotal (n + 1) kAct kOff -
        conditionalMean targetTotal n kAct kOff =
      targetTotal * kAct * kOff /
        (((n : ℝ) * kAct + kOff) * (((n : ℝ) + 1) * kAct + kOff)) := by
  have h0 : (n : ℝ) * kAct + kOff ≠ 0 := by positivity
  have h1 : ((n : ℝ) + 1) * kAct + kOff ≠ 0 := by positivity
  simp [conditionalMean, activationFraction, effectiveActivationRate,
    Nat.cast_add, Nat.cast_one]
  field_simp [h0, h1]
  ring

/-- Exact amount by which the equally-spaced approximation `n*Delta` overshoots
an actual conditional mean.

The error is zero only in the strict zero-saturation limit. -/
theorem lowSaturationError_exact
    (targetTotal : ℝ) (n : ℕ) (kAct kOff : ℝ)
    (hkOff : kOff ≠ 0)
    (hden : (n : ℝ) * kAct + kOff ≠ 0) :
    linearQuantumMean targetTotal n kAct kOff -
        conditionalMean targetTotal n kAct kOff =
      targetTotal * (((n : ℝ) * kAct) ^ 2) /
        (kOff * ((n : ℝ) * kAct + kOff)) := by
  simp [linearQuantumMean, conditionalMean, activationFraction,
    effectiveActivationRate]
  field_simp [hkOff, hden]
  ring

/-- The exact adjacent spacing is positive for physical positive rates and a
positive target pool.  Thus the generic activator-target peaks are ordered. -/
theorem adjacentSpacing_positive
    (targetTotal : ℝ) (n : ℕ) (kAct kOff : ℝ)
    (hT : 0 < targetTotal) (hkAct : 0 < kAct) (hkOff : 0 < kOff) :
    conditionalMean targetTotal n kAct kOff <
      conditionalMean targetTotal (n + 1) kAct kOff := by
  have hspace := adjacentSpacing_exact targetTotal n kAct kOff (le_of_lt hkAct) hkOff
  have hpos :
      0 < targetTotal * kAct * kOff /
        (((n : ℝ) * kAct + kOff) * (((n : ℝ) + 1) * kAct + kOff)) := by
    positivity
  linarith

/-- `relaxationRate` is positive under physical positive turnover. -/
theorem relaxationRate_positive
    (n : ℕ) (kAct kOff : ℝ) (hkAct : 0 ≤ kAct) (hkOff : 0 < kOff) :
    0 < relaxationRate n kAct kOff := by
  unfold relaxationRate effectiveActivationRate
  positivity

end StochasticQuantization
