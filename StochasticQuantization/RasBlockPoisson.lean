import Mathlib
import StochasticQuantization.RasFastBlock
import StochasticQuantization.BirthDeathPoisson

noncomputable section

/-!
# Compact Poisson corrector for one frozen Ras block

The frozen free-RasGTP coordinate is a one-dimensional birth/death chain.  Instead
of inverting a dense generator, solve its Poisson equation with cumulative edge
flux, then remove the stationary null mode by centering the solution.
-/

namespace StochasticQuantization
namespace Ras
namespace BlockPoisson

open BirthDeathPoisson

/-- Number of free Ras molecules in this block. -/
def F (R g t : ℕ) : ℕ := FastBlock.freePool R g t
/-- Per-free-Ras activation rate. -/
def a (g t : ℕ) (kcat1 : ℝ) : ℝ := FastBlock.activationRate g t kcat1
/-- Birth-rate function for free RasGTP. -/
def birthFn (R g t : ℕ) (kcat1 : ℝ) : ℕ → ℝ :=
  fun m => ((F R g t - m : ℕ) : ℝ) * a g t kcat1
/-- Death-rate function for free RasGTP. -/
def deathFn (kcat2 : ℝ) : ℕ → ℝ := fun m => (m : ℝ) * kcat2

theorem deathFn_ne_zero (kcat2 : ℝ) (hkcat2 : kcat2 ≠ 0)
    (m : ℕ) (hm : 0 < m) : deathFn kcat2 m ≠ 0 := by
  unfold deathFn
  exact mul_ne_zero (by exact_mod_cast (Nat.ne_of_gt hm)) hkcat2
/-- Frozen stationary PMF, extended over natural-number coordinates. -/
def rho (R g t : ℕ) (kcat1 kcat2 : ℝ) : ℕ → ℝ :=
  fun m => FastBlock.rho (F R g t) m (a g t kcat1) kcat2

/-- Every physical edge carries zero stationary net flux. -/
theorem rho_zeroFlux
    (R g t m : ℕ) (kcat1 kcat2 : ℝ) (hm : m < F R g t) :
    edgeFlux (birthFn R g t kcat1) (deathFn kcat2)
      (rho R g t kcat1 kcat2) m = 0 := by
  unfold edgeFlux birthFn deathFn rho F a
  have h := FastBlock.rho_detailedBalance
    (FastBlock.freePool R g t) m
    (FastBlock.activationRate g t kcat1) kcat2 hm
  linarith

/-- Frozen PMF has unit total mass. -/
theorem rho_total_one
    (R g t : ℕ) (kcat1 kcat2 : ℝ)
    (hden : a g t kcat1 + kcat2 ≠ 0) :
    totalOver (F R g t) (rho R g t kcat1 kcat2) = 1 := by
  unfold totalOver rho F a
  exact FastBlock.sum_rho _ _ _ hden

/-- Component of `y` lying in the stationary null direction. -/
def projectedPart
    (R g t : ℕ) (kcat1 kcat2 : ℝ) (y : ℕ → ℝ) : ℕ → ℝ :=
  fun m => totalOver (F R g t) y * rho R g t kcat1 kcat2 m

/-- Remove the stationary component so the forcing has zero total mass. -/
def zeroMassForcing
    (R g t : ℕ) (kcat1 kcat2 : ℝ) (y : ℕ → ℝ) : ℕ → ℝ :=
  fun m => y m - projectedPart R g t kcat1 kcat2 y m

@[simp] theorem zeroMassForcing_add
    (R g t : ℕ) (kcat1 kcat2 : ℝ) (y₁ y₂ : ℕ → ℝ) :
    zeroMassForcing R g t kcat1 kcat2 (fun m => y₁ m + y₂ m) =
      fun m => zeroMassForcing R g t kcat1 kcat2 y₁ m +
        zeroMassForcing R g t kcat1 kcat2 y₂ m := by
  funext m
  unfold zeroMassForcing projectedPart
  rw [totalOver_add]
  ring

@[simp] theorem zeroMassForcing_smul
    (R g t : ℕ) (kcat1 kcat2 c : ℝ) (y : ℕ → ℝ) :
    zeroMassForcing R g t kcat1 kcat2 (fun m => c * y m) =
      fun m => c * zeroMassForcing R g t kcat1 kcat2 y m := by
  funext m
  unfold zeroMassForcing projectedPart
  rw [totalOver_smul]
  ring

/-- Subtracting the projected null component gives zero total forcing. -/
theorem zeroMassForcing_total_zero
    (R g t : ℕ) (kcat1 kcat2 : ℝ) (y : ℕ → ℝ)
    (hden : a g t kcat1 + kcat2 ≠ 0) :
    totalOver (F R g t)
      (zeroMassForcing R g t kcat1 kcat2 y) = 0 := by
  unfold zeroMassForcing projectedPart
  unfold totalOver
  rw [Finset.sum_sub_distrib]
  rw [← Finset.mul_sum]
  have hrho := rho_total_one R g t kcat1 kcat2 hden
  unfold totalOver at hrho
  rw [hrho]
  ring

/-- Raw path solve followed by removal of the stationary null mode. -/
def corrector
    (R g t : ℕ) (kcat1 kcat2 : ℝ) (y : ℕ → ℝ) : ℕ → ℝ :=
  let forcing := zeroMassForcing R g t kcat1 kcat2 y
  let raw := poissonRaw (birthFn R g t kcat1) (deathFn kcat2) forcing
  centered (F R g t) (rho R g t kcat1 kcat2) raw

/-- The correction itself has zero block mass. -/
theorem corrector_total_zero
    (R g t : ℕ) (kcat1 kcat2 : ℝ) (y : ℕ → ℝ)
    (hden : a g t kcat1 + kcat2 ≠ 0) :
    totalOver (F R g t) (corrector R g t kcat1 kcat2 y) = 0 := by
  unfold corrector
  apply totalOver_centered
  exact rho_total_one R g t kcat1 kcat2 hden

/-- Lower boundary of the compact Poisson solve. -/
theorem corrector_lower
    (R g t : ℕ) (kcat1 kcat2 : ℝ) (y : ℕ → ℝ)
    (hkcat2 : kcat2 ≠ 0) (hF : 0 < F R g t) :
    lowerForward (birthFn R g t kcat1) (deathFn kcat2)
      (corrector R g t kcat1 kcat2 y) =
      zeroMassForcing R g t kcat1 kcat2 y 0 := by
  unfold corrector
  rw [lowerForward_eq_neg_flux]
  rw [edgeFlux_centered]
  · rw [poissonRaw_edgeFlux]
    · simp [prefixSum]
    · simp [deathFn, hkcat2]
  · exact rho_zeroFlux R g t 0 kcat1 kcat2 (by omega)

/-- Interior coordinate of the compact Poisson solve. -/
theorem corrector_interior
    (R g t m : ℕ) (kcat1 kcat2 : ℝ) (y : ℕ → ℝ)
    (hkcat2 : kcat2 ≠ 0) (hm : m + 1 < F R g t) :
    interiorForward (birthFn R g t kcat1) (deathFn kcat2)
      (corrector R g t kcat1 kcat2 y) m =
      zeroMassForcing R g t kcat1 kcat2 y (m + 1) := by
  unfold corrector
  rw [interiorForward_eq_fluxDifference]
  rw [edgeFlux_centered, edgeFlux_centered]
  · rw [poissonRaw_edgeFlux]
    · rw [poissonRaw_edgeFlux]
      · rw [prefixSum_succ]
        ring
      · exact deathFn_ne_zero kcat2 hkcat2 (m + 2) (by omega)
    · exact deathFn_ne_zero kcat2 hkcat2 (m + 1) (by omega)
  · exact rho_zeroFlux R g t (m + 1) kcat1 kcat2 hm
  · exact rho_zeroFlux R g t m kcat1 kcat2 (by omega)

/-- Upper boundary closes because the projected forcing has zero total mass. -/
theorem corrector_upper
    (R g t : ℕ) (kcat1 kcat2 : ℝ) (y : ℕ → ℝ)
    (hkcat2 : kcat2 ≠ 0) (hF : 0 < F R g t)
    (hden : a g t kcat1 + kcat2 ≠ 0) :
    upperForward (birthFn R g t kcat1) (deathFn kcat2)
      (corrector R g t kcat1 kcat2 y) (F R g t - 1) =
      zeroMassForcing R g t kcat1 kcat2 y (F R g t) := by
  unfold corrector
  rw [upperForward_eq_flux]
  rw [edgeFlux_centered]
  · rw [poissonRaw_edgeFlux]
    · have hzero := zeroMassForcing_total_zero R g t kcat1 kcat2 y hden
      unfold totalOver at hzero
      have hprefix : prefixSum
          (zeroMassForcing R g t kcat1 kcat2 y) (F R g t) = 0 := hzero
      have hs := prefixSum_succ
        (zeroMassForcing R g t kcat1 kcat2 y) (F R g t - 1)
      rw [show F R g t - 1 + 1 = F R g t by omega] at hs
      linarith
    · exact deathFn_ne_zero kcat2 hkcat2 (F R g t - 1 + 1) (by omega)
  · exact rho_zeroFlux R g t (F R g t - 1) kcat1 kcat2 (by omega)

end BlockPoisson
end Ras
end StochasticQuantization
