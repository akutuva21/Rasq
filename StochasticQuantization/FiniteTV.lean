import Mathlib
import StochasticQuantization.RasStateSpace
import StochasticQuantization.Theory.FiniteMetric

noncomputable section

/-!
# L1 distance and total variation on the finite Ras state space

This file is now a thin Ras-specific wrapper around the generic dependent finite
metric layer.  Keeping the names here preserves the existing stationary-theorem
API while avoiding a second implementation of L1/TV.
-/

namespace StochasticQuantization
namespace Ras
namespace FiniteTV

open StateSpace

/-- L1 norm of a signed finite Ras distribution. -/
def l1 {R : ℕ} (x : Distribution R) : ℝ :=
  Theory.FiniteMetric.l1 x

/-- Total-variation distance between two finite distributions. -/
def tv {R : ℕ} (x y : Distribution R) : ℝ :=
  Theory.FiniteMetric.tv x y

@[simp] theorem l1_zero {R : ℕ} : l1 (0 : Distribution R) = 0 := by
  simp [l1, Theory.FiniteMetric.l1]

/-- L1 is nonnegative. -/
theorem l1_nonneg {R : ℕ} (x : Distribution R) : 0 ≤ l1 x := by
  exact Theory.FiniteMetric.l1_nonneg x

/-- Exact scalar behavior of finite L1. -/
theorem l1_smul {R : ℕ} (c : ℝ) (x : Distribution R) :
    l1 (fun b m => c * x b m) = |c| * l1 x := by
  exact Theory.FiniteMetric.l1_smul c x

/-- Triangle inequality written componentwise. -/
theorem l1_add_le {R : ℕ} (x y : Distribution R) :
    l1 (fun b m => x b m + y b m) ≤ l1 x + l1 y := by
  exact Theory.FiniteMetric.l1_add_le x y

/-- TV is exactly half the L1 defect. -/
theorem tv_eq_half_l1 {R : ℕ} (x y : Distribution R) :
    tv x y = (1 / 2 : ℝ) * l1 (fun b m => x b m - y b m) := rfl

end FiniteTV
end Ras
end StochasticQuantization
