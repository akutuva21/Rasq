import Mathlib
import StochasticQuantization.RasReversePoisson
import StochasticQuantization.StationaryMixture

/-!
# End-to-end stationary theorem for the six-reaction Ras count process

This file is the formal endpoint of the project.

For the exact finite fixed-total Ras state space, decompose the forward generator
into

    Q_epsilon = Q_Ras + epsilon Q_SOS,

where `Q_Ras` is processive Ras activation/deactivation inside a frozen SOS block
and `Q_SOS` contains the four SOS binding/unbinding reactions.

`P` replaces the conditional free-RasGTP distribution in each frozen SOS block by
its exact binomial equilibrium while preserving that block's probability mass.
`R` is the constructive O(F) birth/death Poisson corrector.

For any stationary signed distribution `pi`, the exact identity is

    pi - P pi = -epsilon R Q_SOS pi.

Nothing in this theorem truncates SOS occupancy.  Numerical scripts use a cap only
for tractable sparse stationary solves at RasTotal=1000.
-/

namespace StochasticQuantization
namespace Ras
namespace FullStationary

open StateSpace
open FiniteOperators
open ReversePoisson
open FiniteTV

/-- **Exact Ras stationary-defect theorem.** -/
theorem stationary_defect
    (p : Params) (Rtot : ℕ) (epsilon : ℝ) (pi : Distribution Rtot)
    (hk1 : 0 ≤ p.kcat1) (hk2 : 0 < p.kcat2)
    (hstationary : fullLinear p Rtot epsilon pi = 0) :
    pi - StateSpace.project p pi =
      -epsilon • GlobalCorrector.corrector p (slowForward p pi) := by
  have hRQ := ReversePoisson.corrector_comp_fast p Rtot hk1 hk2
  have hstat :
      (fastLinear p Rtot + epsilon • slowLinear p Rtot) pi = 0 := by
    simpa [fullLinear] using hstationary
  simpa [projectLinear, correctorLinear, slowLinear] using
    StochasticQuantization.StationaryMixture.defect_identity
      (fastLinear p Rtot) (slowLinear p Rtot)
      (projectLinear p Rtot) (correctorLinear p Rtot)
      epsilon pi hRQ hstat

/-- Pointwise form, useful for readers who do not want to read vector notation. -/
theorem stationary_defect_pointwise
    (p : Params) (Rtot : ℕ) (epsilon : ℝ) (pi : Distribution Rtot)
    (hk1 : 0 ≤ p.kcat1) (hk2 : 0 < p.kcat2)
    (hstationary : fullLinear p Rtot epsilon pi = 0)
    (b : Block Rtot) (m : FastState b) :
    pi b m - StateSpace.project p pi b m =
      -epsilon * GlobalCorrector.corrector p (slowForward p pi) b m := by
  have h := stationary_defect p Rtot epsilon pi hk1 hk2 hstationary
  exact congrFun (congrFun h b) m

/-- **Exact total-variation version.**

This is the same metric used by the numerical CTMC report. -/
theorem stationary_tv_exact
    (p : Params) (Rtot : ℕ) (epsilon : ℝ) (pi : Distribution Rtot)
    (hk1 : 0 ≤ p.kcat1) (hk2 : 0 < p.kcat2)
    (hstationary : fullLinear p Rtot epsilon pi = 0) :
    FiniteTV.tv pi (StateSpace.project p pi) =
      (|epsilon| / 2) *
        FiniteTV.l1 (GlobalCorrector.corrector p (slowForward p pi)) := by
  apply StochasticQuantization.Ras.StationaryMixtureTV.tv_from_defect
  funext b m
  exact stationary_defect_pointwise p Rtot epsilon pi hk1 hk2 hstationary b m

/-- **Explicit TV O(epsilon) bound.**

`CR` and `CS` can be supplied by a numerical certificate or a separate analytic
bound.  For a probability law `pi`, `CS` is a bound on the L1 size of the SOS
forcing and `CR` is the induced L1 bound of the compact fast corrector. -/
theorem stationary_tv_bound
    (p : Params) (Rtot : ℕ) (epsilon CR CS : ℝ) (pi : Distribution Rtot)
    (hk1 : 0 ≤ p.kcat1) (hk2 : 0 < p.kcat2)
    (hstationary : fullLinear p Rtot epsilon pi = 0)
    (hR : FiniteTV.l1
        (GlobalCorrector.corrector p (slowForward p pi)) ≤
          CR * FiniteTV.l1 (slowForward p pi))
    (hS : FiniteTV.l1 (slowForward p pi) ≤ CS)
    (hCR : 0 ≤ CR) (hCS : 0 ≤ CS) :
    FiniteTV.tv pi (StateSpace.project p pi) ≤
      (|epsilon| / 2) * CR * CS := by
  apply StochasticQuantization.Ras.StationaryMixtureTV.tv_bound_of_operator_bounds
    epsilon CR CS pi (StateSpace.project p pi)
      (slowForward p pi)
      (GlobalCorrector.corrector p (slowForward p pi))
  · funext b m
    exact stationary_defect_pointwise p Rtot epsilon pi hk1 hk2 hstationary b m
  · exact hR
  · exact hS
  · exact hCR
  · exact hCS

/-- Model 1 satisfies the physical catalytic assumptions. -/
theorem model1_stationary_defect
    (rhoSOS epsilon : ℝ) (pi : Distribution 1000)
    (hstationary : fullLinear (model1 rhoSOS) 1000 epsilon pi = 0) :
    pi - StateSpace.project (model1 rhoSOS) pi =
      -epsilon • GlobalCorrector.corrector (model1 rhoSOS)
        (slowForward (model1 rhoSOS) pi) := by
  apply stationary_defect (model1 rhoSOS) 1000 epsilon pi
  · norm_num [model1]
  · norm_num [model1]
  · exact hstationary

/-- Model 2 satisfies the same theorem with its faster RasGAP rate. -/
theorem model2_stationary_defect
    (rhoSOS epsilon : ℝ) (pi : Distribution 1000)
    (hstationary : fullLinear (model2 rhoSOS) 1000 epsilon pi = 0) :
    pi - StateSpace.project (model2 rhoSOS) pi =
      -epsilon • GlobalCorrector.corrector (model2 rhoSOS)
        (slowForward (model2 rhoSOS) pi) := by
  apply stationary_defect (model2 rhoSOS) 1000 epsilon pi
  · norm_num [model2]
  · norm_num [model2]
  · exact hstationary

/-- Model 3 satisfies the theorem too; its SOS operator is simply 1000x faster. -/
theorem model3_stationary_defect
    (rhoSOS epsilon : ℝ) (pi : Distribution 1000)
    (hstationary : fullLinear (model3 rhoSOS) 1000 epsilon pi = 0) :
    pi - StateSpace.project (model3 rhoSOS) pi =
      -epsilon • GlobalCorrector.corrector (model3 rhoSOS)
        (slowForward (model3 rhoSOS) pi) := by
  apply stationary_defect (model3 rhoSOS) 1000 epsilon pi
  · norm_num [model3, speedBinding, model1]
  · norm_num [model3, speedBinding, model1]
  · exact hstationary

end FullStationary
end Ras
end StochasticQuantization
