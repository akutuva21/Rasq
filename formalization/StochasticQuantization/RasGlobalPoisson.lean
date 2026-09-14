import Mathlib
import StochasticQuantization.RasGlobalCorrector

/-!
# Componentwise global Poisson equation for Ras

This file proves the concrete statement behind the compact certificate:

    Q_fast (R y) = y - P y

inside every physical frozen SOS block with at least one free Ras molecule.

`R` is the blockwise path corrector from `RasGlobalCorrector.lean`; `P` is the
actual finite-state frozen-binomial projector from `RasStateSpace.lean`.

The proof is deliberately componentwise.  That keeps the biology visible:

* state 0 uses the lower birth/death boundary equation;
* interior RasGTP counts use flux differences;
* the maximum free-RasGTP state uses the upper boundary equation;
* zero total forcing closes the upper boundary automatically.

No dense matrix appears anywhere.
-/

namespace StochasticQuantization
namespace Ras
namespace GlobalPoisson

open BirthDeathPoisson
open StateSpace
open GlobalCorrector

/-- Extending a finite block vector by zero and summing over its physical natural
indices gives exactly its finite block mass. -/
theorem totalOver_extendFastVector
    {R : ℕ} (b : Block R) (v : FastState b → ℝ) :
    totalOver (freeTotal b) (extendFastVector b v) =
      ∑ m : FastState b, v m := by
  unfold totalOver
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro m hm
  exact extendFastVector_apply b v m

/-- Therefore the blockwise `y-Py` used by the path solver is exactly the
componentwise difference from the global frozen-equilibrium projector. -/
theorem zeroMassForcing_eq_sub_project
    (p : Params) {R : ℕ} (x : Distribution R)
    (b : Block R) (m : FastState b) :
    BlockPoisson.zeroMassForcing
      R (boundGDP b) (boundGTP b) p.kcat1 p.kcat2
      (extendFastVector b (x b)) m.1 =
      x b m - StateSpace.project p x b m := by
  unfold BlockPoisson.zeroMassForcing BlockPoisson.projectedPart
  rw [totalOver_extendFastVector]
  unfold StateSpace.project BlockProjection.project BlockProjection.blockMass
    StateSpace.rho BlockPoisson.rho
  rw [extendFastVector_apply]
  rfl

/-- The forward fast generator at one natural-number free-RasGTP coordinate.
The `F=0` block has no fast reaction and is handled explicitly. -/
def fastForwardNat
    (p : Params) (R : ℕ) (b : Block R) (z : ℕ → ℝ) (m : ℕ) : ℝ :=
  if hF : freeTotal b = 0 then 0
  else if h0 : m = 0 then
    lowerForward
      (BlockPoisson.birthFn R (boundGDP b) (boundGTP b) p.kcat1)
      (BlockPoisson.deathFn p.kcat2) z
  else if htop : m = freeTotal b then
    upperForward
      (BlockPoisson.birthFn R (boundGDP b) (boundGTP b) p.kcat1)
      (BlockPoisson.deathFn p.kcat2) z (freeTotal b - 1)
  else
    interiorForward
      (BlockPoisson.birthFn R (boundGDP b) (boundGTP b) p.kcat1)
      (BlockPoisson.deathFn p.kcat2) z (m - 1)

/-- Fast forward generator on a full finite signed distribution, assembled block
by block. -/
def fastForward
    (p : Params) {R : ℕ} (x : Distribution R) : Distribution R :=
  fun b m => fastForwardNat p R b (extendFastVector b (x b)) m.1

/-- **Concrete Ras left-Poisson identity.**

For every physical block containing at least one free Ras molecule, applying the
fast forward generator to the compact blockwise corrector returns exactly
`x-Px` at every free-RasGTP count.
-/
theorem fastForward_corrector
    (p : Params) {R : ℕ} (x : Distribution R)
    (b : Block R) (m : FastState b)
    (hkcat2 : p.kcat2 ≠ 0)
    (hden : FastBlock.activationRate (boundGDP b) (boundGTP b) p.kcat1 + p.kcat2 ≠ 0)
    (hF : 0 < freeTotal b) :
    fastForward p (GlobalCorrector.corrector p x) b m =
      x b m - StateSpace.project p x b m := by
  unfold fastForward fastForwardNat
  simp [ne_of_gt hF]
  by_cases h0 : m.1 = 0
  · simp [h0]
    have h := BlockPoisson.corrector_lower
      R (boundGDP b) (boundGTP b) p.kcat1 p.kcat2
      (extendFastVector b (x b)) hkcat2 hF
    rw [h]
    exact zeroMassForcing_eq_sub_project p x b m
  · simp [h0]
    by_cases htop : m.1 = freeTotal b
    · simp [htop]
      have h := BlockPoisson.corrector_upper
        R (boundGDP b) (boundGTP b) p.kcat1 p.kcat2
        (extendFastVector b (x b)) hkcat2 hF hden
      rw [h]
      simpa [htop] using zeroMassForcing_eq_sub_project p x b m
    · simp [htop]
      have hmle : m.1 ≤ freeTotal b := by omega
      have hmlt : m.1 < freeTotal b := lt_of_le_of_ne hmle htop
      have hprev : m.1 - 1 + 1 = m.1 := by omega
      have hint := BlockPoisson.corrector_interior
        R (boundGDP b) (boundGTP b) (m.1 - 1) p.kcat1 p.kcat2
        (extendFastVector b (x b)) hkcat2 (by omega)
      rw [hint]
      rw [hprev]
      exact zeroMassForcing_eq_sub_project p x b m



/-- The degenerate `F=0` block is not an exception to the Poisson identity.
There is only one fast state, so projection is the identity inside that block and
both sides are exactly zero. -/
theorem fastForward_corrector_zeroFree
    (p : Params) {R : ℕ} (x : Distribution R)
    (b : Block R) (m : FastState b)
    (hden : FastBlock.activationRate (boundGDP b) (boundGTP b) p.kcat1 + p.kcat2 ≠ 0)
    (hF : freeTotal b = 0) :
    fastForward p (GlobalCorrector.corrector p x) b m =
      x b m - StateSpace.project p x b m := by
  have hBF : BlockPoisson.F R (boundGDP b) (boundGTP b) = 0 := by
    simpa [BlockPoisson.F, FastBlock.freePool, freeTotal, boundTotal] using hF
  have hzero := BlockPoisson.zeroMassForcing_total_zero
    R (boundGDP b) (boundGTP b) p.kcat1 p.kcat2
    (extendFastVector b (x b)) hden
  have hm0 : m.1 = 0 := by
    have hm_lt : m.1 < freeTotal b + 1 := m.2
    omega
  have hforce0 :
      BlockPoisson.zeroMassForcing
        R (boundGDP b) (boundGTP b) p.kcat1 p.kcat2
        (extendFastVector b (x b)) m.1 = 0 := by
    rw [hm0]
    unfold totalOver at hzero
    simp [hBF] at hzero
    exact hzero
  unfold fastForward fastForwardNat
  simp [hF]
  calc
    0 = BlockPoisson.zeroMassForcing
          R (boundGDP b) (boundGTP b) p.kcat1 p.kcat2
          (extendFastVector b (x b)) m.1 := hforce0.symm
    _ = x b m - StateSpace.project p x b m :=
      zeroMassForcing_eq_sub_project p x b m

/-- **Global compact Ras Poisson identity, including every physical block.**

The earlier theorem handled blocks with at least one free Ras molecule.  The
lemma above handles the one-state block.  Together they remove the last
state-space edge-case:

    Q_fast (R x) = x - P x

for every encoded fixed-total Ras state. -/
theorem fastForward_corrector_all
    (p : Params) {R : ℕ} (x : Distribution R)
    (b : Block R) (m : FastState b)
    (hkcat2 : p.kcat2 ≠ 0)
    (hden : FastBlock.activationRate (boundGDP b) (boundGTP b) p.kcat1 + p.kcat2 ≠ 0) :
    fastForward p (GlobalCorrector.corrector p x) b m =
      x b m - StateSpace.project p x b m := by
  by_cases hF0 : freeTotal b = 0
  · exact fastForward_corrector_zeroFree p x b m hden hF0
  · exact fastForward_corrector p x b m hkcat2 hden (Nat.pos_of_ne_zero hF0)

end GlobalPoisson
end Ras
end StochasticQuantization
