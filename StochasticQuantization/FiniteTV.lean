import Mathlib
import StochasticQuantization.RasStateSpace

noncomputable section

/-!
# L1 distance and total variation on the finite Ras state space

The numerical analysis reports total-variation distance.  These definitions make
that same metric explicit in Lean rather than relying on an unrelated default
function-space norm.
-/

namespace StochasticQuantization
namespace Ras
namespace FiniteTV

open StateSpace

/-- L1 norm of a signed finite Ras distribution. -/
def l1 {R : ℕ} (x : Distribution R) : ℝ :=
  ∑ b : Block R, ∑ m : FastState b, |x b m|

/-- Total-variation distance between two finite distributions. -/
def tv {R : ℕ} (x y : Distribution R) : ℝ :=
  (1 / 2 : ℝ) * l1 (fun b m => x b m - y b m)

@[simp] theorem l1_zero {R : ℕ} : l1 (0 : Distribution R) = 0 := by
  simp [l1]

/-- L1 is nonnegative. -/
theorem l1_nonneg {R : ℕ} (x : Distribution R) : 0 ≤ l1 x := by
  unfold l1
  positivity

/-- Exact scalar behavior of finite L1. -/
theorem l1_smul {R : ℕ} (c : ℝ) (x : Distribution R) :
    l1 (fun b m => c * x b m) = |c| * l1 x := by
  unfold l1
  simp_rw [abs_mul, Finset.mul_sum]

/-- Triangle inequality written componentwise. -/
theorem l1_add_le {R : ℕ} (x y : Distribution R) :
    l1 (fun b m => x b m + y b m) ≤ l1 x + l1 y := by
  unfold l1
  calc
    (∑ b : Block R, ∑ m : FastState b, |x b m + y b m|) ≤
        ∑ b : Block R, ∑ m : FastState b, (|x b m| + |y b m|) := by
          apply Finset.sum_le_sum
          intro b hb
          apply Finset.sum_le_sum
          intro m hm
          exact abs_add_le _ _
    _ = (∑ b : Block R, ∑ m : FastState b, |x b m|) +
        (∑ b : Block R, ∑ m : FastState b, |y b m|) := by
          simp_rw [Finset.sum_add_distrib]

/-- TV is exactly half the L1 defect. -/
theorem tv_eq_half_l1 {R : ℕ} (x y : Distribution R) :
    tv x y = (1 / 2 : ℝ) * l1 (fun b m => x b m - y b m) := rfl

end FiniteTV
end Ras
end StochasticQuantization
