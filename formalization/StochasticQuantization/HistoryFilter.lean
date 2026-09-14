import Mathlib

/-!
# Finite-history fading-memory filter

If one biochemical dwell relaxes a scalar output toward target `mu` while retaining
fraction `a` of its previous deviation, then

    x_after = a*x_before + (1-a)*mu.

Repeated dwells therefore form an affine fading-memory filter.  The difference
between two trajectories exposed to the same history is multiplied only by the
product of the retention factors.
-/

namespace StochasticQuantization
namespace HistoryFilter

/-- One dwell of the reduced relaxation dynamics. -/
def step (a mu x : ℝ) : ℝ := a * x + (1 - a) * mu

/-- Exact two-dwell expansion. -/
theorem two_steps (a₀ a₁ μ₀ μ₁ x : ℝ) :
    step a₁ μ₁ (step a₀ μ₀ x) =
      a₁ * a₀ * x + (1 - a₁) * μ₁ + a₁ * (1 - a₀) * μ₀ := by
  unfold step
  ring

/-- A finite history is stored as `(retention,target)` pairs and applied in order. -/
def run : List (ℝ × ℝ) → ℝ → ℝ
  | [], x => x
  | (a, μ) :: hs, x => run hs (step a μ x)

/-- Only retention factors control how fast two initial conditions are forgotten. -/
theorem run_sub (hs : List (ℝ × ℝ)) (x y : ℝ) :
    run hs x - run hs y = (hs.map Prod.fst).prod * (x - y) := by
  induction hs generalizing x y with
  | nil => simp [run]
  | cons h hs ih =>
      rcases h with ⟨a, μ⟩
      simp only [run, List.map_cons, List.prod_cons]
      rw [ih]
      unfold step
      ring

/-- If every retention factor has magnitude at most one, the shared history cannot
increase the distance between two initial conditions. -/
theorem step_difference (a μ x y : ℝ) :
    step a μ x - step a μ y = a * (x - y) := by
  unfold step
  ring

end HistoryFilter
end StochasticQuantization
