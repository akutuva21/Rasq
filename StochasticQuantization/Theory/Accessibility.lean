import Mathlib

noncomputable section

/-!
# Minimal spatial accessibility theory

The detailed spatial simulator suggested a simpler theoretical failure mode of
the well-mixed RasQ model: a processive catalyst may not have access to the whole
nominal target pool.  A minimal two-compartment balance has a local pool `u`
exchanging with a reservoir value `U` at rate `mix` and being consumed/activated
locally at rate `act`:

    du/dt = mix * (U-u) - act * u.

Its steady accessible fraction is `mix / (act + mix)`.  The ratio `act/mix` is a
Damkoehler-like control parameter for local depletion.
-/

namespace StochasticQuantization
namespace Theory
namespace Accessibility

/-- Fraction of the reservoir target available locally at steady state. -/
def accessibleFraction (act mix : ℝ) : ℝ := mix / (act + mix)

/-- Fraction lost to local depletion. -/
def depletionFraction (act mix : ℝ) : ℝ := act / (act + mix)

/-- Damkoehler-like competition between local reaction and mixing. -/
def damkohler (act mix : ℝ) : ℝ := act / mix

/-- Accessibility is exactly `1 / (1 + Da)` when mixing is nonzero. -/
theorem accessibleFraction_eq_inv_one_add_damkohler
    (act mix : ℝ) (hmix : mix ≠ 0) (hden : act + mix ≠ 0) :
    accessibleFraction act mix = 1 / (1 + damkohler act mix) := by
  unfold accessibleFraction damkohler
  have hden' : mix + act ≠ 0 := by simpa [add_comm] using hden
  field_simp [hmix, hden, hden']
  ring

/-- Depletion is the complementary `Da / (1 + Da)` fraction. -/
theorem depletionFraction_eq_damkohler_div_one_add
    (act mix : ℝ) (hmix : mix ≠ 0) (hden : act + mix ≠ 0) :
    depletionFraction act mix = damkohler act mix / (1 + damkohler act mix) := by
  unfold depletionFraction damkohler
  have hden' : mix + act ≠ 0 := by simpa [add_comm] using hden
  field_simp [hmix, hden, hden']
  ring

/-- Local steady target level in the two-compartment reduction. -/
def localSteady (reservoir act mix : ℝ) : ℝ :=
  reservoir * accessibleFraction act mix

/-- Accessible target count for a nominal target pool. -/
def accessibleTarget (targetTotal act mix : ℝ) : ℝ :=
  targetTotal * accessibleFraction act mix

/-- The proposed steady level exactly balances mixing influx and local reaction. -/
theorem localSteady_flux_balance
    (reservoir act mix : ℝ) (hden : act + mix ≠ 0) :
    mix * (reservoir - localSteady reservoir act mix) =
      act * localSteady reservoir act mix := by
  unfold localSteady accessibleFraction
  field_simp [hden]
  ring

/-- The flux-balance steady state is unique whenever the total removal/mixing rate
is nonzero. -/
theorem localSteady_unique
    (reservoir act mix u : ℝ) (hden : act + mix ≠ 0)
    (hbal : mix * (reservoir - u) = act * u) :
    u = localSteady reservoir act mix := by
  unfold localSteady accessibleFraction
  field_simp [hden]
  nlinarith

/-- Accessibility and depletion fractions partition the target pool. -/
theorem accessible_add_depletion
    (act mix : ℝ) (hden : act + mix ≠ 0) :
    accessibleFraction act mix + depletionFraction act mix = 1 := by
  unfold accessibleFraction depletionFraction
  field_simp [hden]
  ring

/-- Exact target loss caused by finite accessibility. -/
theorem target_loss_exact
    (targetTotal act mix : ℝ) (hden : act + mix ≠ 0) :
    targetTotal - accessibleTarget targetTotal act mix =
      targetTotal * depletionFraction act mix := by
  unfold accessibleTarget
  calc
    targetTotal - targetTotal * accessibleFraction act mix =
        targetTotal * (1 - accessibleFraction act mix) := by ring
    _ = targetTotal * depletionFraction act mix := by
      rw [show 1 - accessibleFraction act mix = depletionFraction act mix by
        linarith [accessible_add_depletion act mix hden]]

/-- If mixing is at least `k` times faster than local activation, depletion is at
most `1/(k+1)`. -/
theorem depletion_le_of_fast_mixing
    (act mix k : ℝ)
    (hact : 0 ≤ act) (hmix : 0 < mix) (hk : 0 ≤ k)
    (hfast : k * act ≤ mix) :
    depletionFraction act mix ≤ 1 / (k + 1) := by
  unfold depletionFraction
  have hden : 0 < act + mix := by linarith
  have hk1 : 0 < k + 1 := by linarith
  rw [div_le_div_iff₀ hden hk1]
  nlinarith



/-- Under physical nonnegative reaction and positive mixing, accessibility is a
true fraction in `[0,1]`. -/
theorem accessibleFraction_mem_unitInterval
    (act mix : ℝ) (hact : 0 ≤ act) (hmix : 0 < mix) :
    0 ≤ accessibleFraction act mix ∧ accessibleFraction act mix ≤ 1 := by
  unfold accessibleFraction
  have hden : 0 < act + mix := by linarith
  constructor
  · positivity
  · exact (div_le_one hden).2 (by linarith)

/-- Fast mixing gives an absolute bound on how much of a nonnegative nominal
target pool becomes inaccessible. -/
theorem target_loss_le_of_fast_mixing
    (targetTotal act mix k : ℝ)
    (hT : 0 ≤ targetTotal)
    (hact : 0 ≤ act) (hmix : 0 < mix) (hk : 0 ≤ k)
    (hfast : k * act ≤ mix) :
    targetTotal - accessibleTarget targetTotal act mix ≤
      targetTotal / (k + 1) := by
  have hden : act + mix ≠ 0 := ne_of_gt (by linarith : 0 < act + mix)
  rw [target_loss_exact targetTotal act mix hden]
  have hdep := depletion_le_of_fast_mixing act mix k hact hmix hk hfast
  have hk1 : 0 < k + 1 := by linarith
  calc
    targetTotal * depletionFraction act mix ≤ targetTotal * (1 / (k + 1)) :=
      mul_le_mul_of_nonneg_left hdep hT
    _ = targetTotal / (k + 1) := by simp [div_eq_mul_inv]

end Accessibility
end Theory
end StochasticQuantization
