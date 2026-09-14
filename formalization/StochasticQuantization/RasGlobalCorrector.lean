import Mathlib
import StochasticQuantization.RasStateSpace
import StochasticQuantization.RasBlockPoisson

noncomputable section

namespace StochasticQuantization
namespace Ras
namespace GlobalCorrector

open StateSpace

def extendFastVector {R : ℕ} (b : Block R) (v : FastState b → ℝ) : ℕ → ℝ :=
  fun m => if hm : m < freeTotal b + 1 then v ⟨m, hm⟩ else 0

theorem extendFastVector_add
    {R : ℕ} (b : Block R) (v w : FastState b → ℝ) :
    extendFastVector b (fun m => v m + w m) =
      fun m => extendFastVector b v m + extendFastVector b w m := by
  funext m
  unfold extendFastVector
  by_cases hm : m < freeTotal b + 1 <;> simp [hm]

theorem extendFastVector_smul
    {R : ℕ} (b : Block R) (c : ℝ) (v : FastState b → ℝ) :
    extendFastVector b (fun m => c * v m) =
      fun m => c * extendFastVector b v m := by
  funext m
  unfold extendFastVector
  by_cases hm : m < freeTotal b + 1 <;> simp [hm]

@[simp] theorem extendFastVector_apply
    {R : ℕ} (b : Block R) (v : FastState b → ℝ) (m : FastState b) :
    extendFastVector b v m.1 = v m := by
  unfold extendFastVector
  simp [m.2]

def corrector (p : Params) {R : ℕ} (x : Distribution R) : Distribution R :=
  fun b m =>
    BlockPoisson.corrector R (boundGDP b) (boundGTP b) p.kcat1 p.kcat2
      (extendFastVector b (x b)) m.1

theorem corrector_add
    (p : Params) {R : ℕ} (x y : Distribution R) :
    corrector p (fun b m => x b m + y b m) =
      fun b m => corrector p x b m + corrector p y b m := by
  funext b m
  unfold corrector
  unfold BlockPoisson.corrector
  rw [extendFastVector_add]
  rw [BlockPoisson.zeroMassForcing_add]
  have hraw :
      BirthDeathPoisson.poissonRaw
          (BlockPoisson.birthFn R (boundGDP b) (boundGTP b) p.kcat1)
          (BlockPoisson.deathFn p.kcat2)
          (fun n =>
            BlockPoisson.zeroMassForcing R (boundGDP b) (boundGTP b)
                p.kcat1 p.kcat2 (extendFastVector b (x b)) n +
              BlockPoisson.zeroMassForcing R (boundGDP b) (boundGTP b)
                p.kcat1 p.kcat2 (extendFastVector b (y b)) n) =
        fun n =>
          BirthDeathPoisson.poissonRaw
              (BlockPoisson.birthFn R (boundGDP b) (boundGTP b) p.kcat1)
              (BlockPoisson.deathFn p.kcat2)
              (BlockPoisson.zeroMassForcing R (boundGDP b) (boundGTP b)
                p.kcat1 p.kcat2 (extendFastVector b (x b))) n +
            BirthDeathPoisson.poissonRaw
              (BlockPoisson.birthFn R (boundGDP b) (boundGTP b) p.kcat1)
              (BlockPoisson.deathFn p.kcat2)
              (BlockPoisson.zeroMassForcing R (boundGDP b) (boundGTP b)
                p.kcat1 p.kcat2 (extendFastVector b (y b))) n := by
    funext n
    exact BirthDeathPoisson.poissonRaw_add _ _ _ _ n
  rw [hraw]
  rw [BirthDeathPoisson.centered_add]

theorem corrector_smul
    (p : Params) {R : ℕ} (c : ℝ) (x : Distribution R) :
    corrector p (fun b m => c * x b m) =
      fun b m => c * corrector p x b m := by
  funext b m
  unfold corrector
  unfold BlockPoisson.corrector
  rw [extendFastVector_smul]
  rw [BlockPoisson.zeroMassForcing_smul]
  have hraw :
      BirthDeathPoisson.poissonRaw
          (BlockPoisson.birthFn R (boundGDP b) (boundGTP b) p.kcat1)
          (BlockPoisson.deathFn p.kcat2)
          (fun n => c * BlockPoisson.zeroMassForcing R (boundGDP b) (boundGTP b)
            p.kcat1 p.kcat2 (extendFastVector b (x b)) n) =
        fun n => c * BirthDeathPoisson.poissonRaw
          (BlockPoisson.birthFn R (boundGDP b) (boundGTP b) p.kcat1)
          (BlockPoisson.deathFn p.kcat2)
          (BlockPoisson.zeroMassForcing R (boundGDP b) (boundGTP b)
            p.kcat1 p.kcat2 (extendFastVector b (x b))) n := by
    funext n
    exact BirthDeathPoisson.poissonRaw_smul _ _ _ c n
  rw [hraw]
  rw [BirthDeathPoisson.centered_smul]

noncomputable def correctorLinear (p : Params) (R : ℕ) :
    Distribution R →ₗ[ℝ] Distribution R where
  toFun := corrector p
  map_add' := by intro x y; exact corrector_add p x y
  map_smul' := by intro c x; exact corrector_smul p c x

theorem blockMass_corrector_zero
    (p : Params) {R : ℕ} (x : Distribution R) (b : Block R)
    (hden : FastBlock.activationRate (boundGDP b) (boundGTP b) p.kcat1 + p.kcat2 ≠ 0) :
  blockMass (corrector p x) b = 0 := by
  unfold blockMass BlockProjection.blockMass corrector
  let f : ℕ → ℝ := fun n =>
    BlockPoisson.corrector R (boundGDP b) (boundGTP b) p.kcat1 p.kcat2
      (extendFastVector b (x b)) n
  change (∑ m : Fin (freeTotal b + 1), f m.1) = 0
  rw [Fin.sum_univ_eq_sum_range f]
  dsimp [f]
  exact BlockPoisson.corrector_total_zero
    R (boundGDP b) (boundGTP b) p.kcat1 p.kcat2
    (extendFastVector b (x b)) hden

theorem project_corrector_zero
    (p : Params) {R : ℕ} (x : Distribution R)
    (hden : ∀ b : Block R,
      FastBlock.activationRate (boundGDP b) (boundGTP b) p.kcat1 + p.kcat2 ≠ 0) :
    StateSpace.project p (corrector p x) = 0 := by
  funext b m
  change blockMass (corrector p x) b * rho p b m = 0
  rw [blockMass_corrector_zero p x b (hden b)]
  simp

end GlobalCorrector
end Ras
end StochasticQuantization
