import Mathlib
import StochasticQuantization.FiniteTV

/-!
# Generic finite-state slow/fast stationary identity

Let `Q_epsilon = Qfast + epsilon * Qslow`.  Let `P` project onto the equilibria
of the fast blocks and `R` be the fast Poisson corrector satisfying
`R Qfast = I - P`.  If `pi` is stationary for the full generator, then exactly

    pi - P pi = -epsilon R Qslow pi.
-/

namespace StochasticQuantization
namespace StationaryMixture

/-- Exact stationary-defect identity on an arbitrary real vector space. -/
theorem defect_identity
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (Qfast Qslow P Rop : E →ₗ[ℝ] E)
    (epsilon : ℝ) (pi : E)
    (hRQ : Rop.comp Qfast = LinearMap.id - P)
    (hstationary : (Qfast + epsilon • Qslow) pi = 0) :
    pi - P pi = -epsilon • Rop (Qslow pi) := by
  have hs := congrArg (fun z => Rop z) hstationary
  simp only [LinearMap.add_apply, LinearMap.smul_apply, map_add, map_smul,
    map_zero] at hs
  have hrq := congrArg (fun A : E →ₗ[ℝ] E => A pi) hRQ
  simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.id_apply] at hrq
  rw [hrq] at hs
  simpa only [neg_smul] using eq_neg_of_add_eq_zero_left hs

end StationaryMixture

namespace Ras
namespace StationaryMixtureTV

open StateSpace
open FiniteTV

/-- Total variation form of the exact stationary defect identity. -/
theorem tv_from_defect
    {Rtot : ℕ} (epsilon : ℝ)
    (pi Ppi corr : Distribution Rtot)
    (h : (fun b m => pi b m - Ppi b m) =
      (fun b m => -epsilon * corr b m)) :
    tv pi Ppi = (|epsilon| / 2) * l1 corr := by
  unfold tv Theory.FiniteMetric.tv Theory.FiniteMetric.distanceL1
  rw [h]
  rw [Theory.FiniteMetric.l1_smul]
  rw [abs_neg]
  change (1 / 2 : ℝ) * (|epsilon| * Theory.FiniteMetric.l1 corr) =
    |epsilon| / 2 * Theory.FiniteMetric.l1 corr
  ring

/-- L1 operator-bound version used to obtain an explicit `O(epsilon)` TV bound. -/
theorem tv_bound_of_operator_bounds
    {Rtot : ℕ} (epsilon CR CS : ℝ)
    (pi Ppi slow corr : Distribution Rtot)
    (hdefect : (fun b m => pi b m - Ppi b m) =
      (fun b m => -epsilon * corr b m))
    (hR : l1 corr ≤ CR * l1 slow)
    (hS : l1 slow ≤ CS)
    (hCR : 0 ≤ CR) (hCS : 0 ≤ CS) :
    tv pi Ppi ≤ (|epsilon| / 2) * CR * CS := by
  rw [tv_from_defect epsilon pi Ppi corr hdefect]
  have hRc : l1 corr ≤ CR * CS :=
    le_trans hR (mul_le_mul_of_nonneg_left hS hCR)
  have hcoef : 0 ≤ |epsilon| / 2 := by positivity
  nlinarith

end StationaryMixtureTV
end Ras
end StochasticQuantization
