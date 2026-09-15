import Mathlib
import StochasticQuantization.SlowFast

noncomputable section

/-!
# General dwell-time distributions and effective processivity

For a biochemical output relaxing at rate `r`, one active dwell of length `t`
retains `exp(-r*t)` of the old deviation.  For an arbitrary finite dwell-time law,
the biologically relevant quantity is therefore the weighted residual

    E[exp(-r W)],

not merely `E[W]`.  The expected completed fraction is exactly one minus this
Laplace-type residual.  `W` may itself be an active window such as
`max(residence - activationLatency, 0)`.
-/

namespace StochasticQuantization
namespace Theory
namespace DwellDistribution

/-- Finite-support dwell-time law. -/
structure FiniteLaw (I : Type*) [Fintype I] where
  weight : I → ℝ
  duration : I → ℝ
  mass_one : ∑ i : I, weight i = 1
  weight_nonneg : ∀ i, 0 ≤ weight i
  duration_nonneg : ∀ i, 0 ≤ duration i

/-- Active processive time after an activation latency. -/
def activeWindow (residence latency : ℝ) : ℝ := max (residence - latency) 0

/-- Convert a residence-time law into an active-window law after a fixed
activation latency.  Weights are unchanged; only usable processive time changes. -/
def withLatency {I : Type*} [Fintype I]
    (law : FiniteLaw I) (latency : ℝ) : FiniteLaw I where
  weight := law.weight
  duration := fun i => activeWindow (law.duration i) latency
  mass_one := law.mass_one
  weight_nonneg := law.weight_nonneg
  duration_nonneg := by
    intro i
    unfold activeWindow
    exact le_max_right _ _

/-- Fraction of the old deviation retained after one active window. -/
def retention (r t : ℝ) : ℝ := trackingErrorFraction r t

/-- Residual memory of a residence law with activation latency is exactly the
residual evaluated on its active-window transform. -/
theorem withLatency_duration
    {I : Type*} [Fintype I] (law : FiniteLaw I) (latency : ℝ) (i : I) :
    (withLatency law latency).duration i =
      activeWindow (law.duration i) latency := by
  rfl

/-- Weighted residual memory `E[exp(-r W)]`. -/
def meanResidual {I : Type*} [Fintype I] (law : FiniteLaw I) (r : ℝ) : ℝ :=
  ∑ i : I, law.weight i * retention r (law.duration i)

/-- Weighted fraction of the biochemical move completed during the dwell. -/
def meanCompleted {I : Type*} [Fintype I] (law : FiniteLaw I) (r : ℝ) : ℝ :=
  ∑ i : I, law.weight i * (1 - retention r (law.duration i))

/-- Mean dwell duration. -/
def meanDuration {I : Type*} [Fintype I] (law : FiniteLaw I) : ℝ :=
  ∑ i : I, law.weight i * law.duration i

/-- Weighted residual memory is nonnegative for a physical finite law. -/
theorem meanResidual_nonneg
    {I : Type*} [Fintype I] (law : FiniteLaw I) (r : ℝ) :
    0 ≤ meanResidual law r := by
  unfold meanResidual
  apply Finset.sum_nonneg
  intro i hi
  exact mul_nonneg (law.weight_nonneg i) (le_of_lt (Real.exp_pos _))

/-- For a nonnegative relaxation rate, residual memory is at most one. -/
theorem meanResidual_le_one
    {I : Type*} [Fintype I] (law : FiniteLaw I) (r : ℝ) (hr : 0 ≤ r) :
    meanResidual law r ≤ 1 := by
  unfold meanResidual retention trackingErrorFraction
  calc
    (∑ i : I, law.weight i * Real.exp (-r * law.duration i)) ≤
        ∑ i : I, law.weight i * 1 := by
          apply Finset.sum_le_sum
          intro i hi
          apply mul_le_mul_of_nonneg_left _ (law.weight_nonneg i)
          rw [Real.exp_le_one_iff]
          have hd := law.duration_nonneg i
          nlinarith
    _ = 1 := by simpa using law.mass_one

/-- **General dwell theorem.**  Effective processivity is one minus the weighted
residual memory. -/
theorem meanCompleted_eq_one_sub_meanResidual
    {I : Type*} [Fintype I] (law : FiniteLaw I) (r : ℝ) :
    meanCompleted law r = 1 - meanResidual law r := by
  unfold meanCompleted meanResidual retention
  simp_rw [mul_sub, mul_one]
  rw [Finset.sum_sub_distrib]
  rw [law.mass_one]

/-- For nonnegative relaxation, the expected completed fraction lies in `[0,1]`. -/
theorem meanCompleted_mem_unitInterval
    {I : Type*} [Fintype I] (law : FiniteLaw I) (r : ℝ) (hr : 0 ≤ r) :
    0 ≤ meanCompleted law r ∧ meanCompleted law r ≤ 1 := by
  rw [meanCompleted_eq_one_sub_meanResidual]
  have hlo := meanResidual_nonneg law r
  have hhi := meanResidual_le_one law r hr
  constructor <;> linarith



/-- A nonnegative activation latency cannot create more active time than the
original residence time. -/
theorem activeWindow_le_residence
    (residence latency : ℝ) (hres : 0 ≤ residence) (hlat : 0 ≤ latency) :
    activeWindow residence latency ≤ residence := by
  unfold activeWindow
  apply max_le
  · linarith
  · exact hres

/-- Adding a nonnegative activation latency can only increase residual memory
(and therefore can only reduce the completed biochemical move) when the
relaxation rate is nonnegative. -/
theorem meanResidual_le_withLatency
    {I : Type*} [Fintype I] (law : FiniteLaw I)
    (r latency : ℝ) (hr : 0 ≤ r) (hlat : 0 ≤ latency) :
    meanResidual law r ≤ meanResidual (withLatency law latency) r := by
  unfold meanResidual retention trackingErrorFraction
  apply Finset.sum_le_sum
  intro i hi
  apply mul_le_mul_of_nonneg_left _ (law.weight_nonneg i)
  apply Real.exp_le_exp.mpr
  have hw := activeWindow_le_residence
    (law.duration i) latency (law.duration_nonneg i) hlat
  exact mul_le_mul_of_nonpos_left hw (neg_nonpos.mpr hr)

/-- Equivalently, activation latency cannot improve the expected completed
fraction of the state-specific biochemical move. -/
theorem meanCompleted_withLatency_le
    {I : Type*} [Fintype I] (law : FiniteLaw I)
    (r latency : ℝ) (hr : 0 ≤ r) (hlat : 0 ≤ latency) :
    meanCompleted (withLatency law latency) r ≤ meanCompleted law r := by
  rw [meanCompleted_eq_one_sub_meanResidual,
    meanCompleted_eq_one_sub_meanResidual]
  have h := meanResidual_le_withLatency law r latency hr hlat
  linarith

/-- The exponential-dwell formula already proved in the RasQ slow/fast layer is
the continuous-law special case of the same retention principle. -/
theorem exponential_completed_eq_gamma_fraction
    (r koff : ℝ) (hr : 0 < r) (hkoff : 0 < koff) :
    meanCompletedAtDwellEnd r koff = gamma r koff / (1 + gamma r koff) := by
  exact meanCompletedAtDwellEnd_eq_gamma_fraction r koff hr hkoff

/-- Deterministic dwell residual. -/
def deterministicResidual (r d : ℝ) : ℝ := retention r d

/-- Residual for a two-point law putting half its mass at `0` and half at `2d`.
This law has the same mean duration `d` as the deterministic law. -/
def twoPointResidual (r d : ℝ) : ℝ :=
  (retention r 0 + retention r (2 * d)) / 2

/-- The deterministic dwell and the `0/2d` mixture have identical mean duration. -/
theorem twoPoint_mean_eq_deterministic (d : ℝ) :
    ((0 : ℝ) + 2 * d) / 2 = d := by ring

/-- Yet their residual memories differ by an exact nonnegative square. -/
theorem twoPointResidual_sub_deterministic
    (r d : ℝ) :
    twoPointResidual r d - deterministicResidual r d =
      (retention r d - 1) ^ 2 / 2 := by
  have hexp : retention r (2 * d) = retention r d * retention r d := by
    unfold retention trackingErrorFraction
    rw [show -r * (2 * d) = (-r * d) + (-r * d) by ring, Real.exp_add]
  unfold twoPointResidual deterministicResidual
  rw [hexp]
  simp [retention, trackingErrorFraction]
  ring

/-- Therefore equal mean residence time does not imply equal effective
processivity. -/
theorem deterministicResidual_le_twoPointResidual (r d : ℝ) :
    deterministicResidual r d ≤ twoPointResidual r d := by
  have h := twoPointResidual_sub_deterministic r d
  have hsquare : 0 ≤ (retention r d - 1) ^ 2 := sq_nonneg _
  linarith

end DwellDistribution
end Theory
end StochasticQuantization
