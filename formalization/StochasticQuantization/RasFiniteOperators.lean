import Mathlib
import StochasticQuantization.RasGlobalPoisson
import StochasticQuantization.RasSlowForward

noncomputable section

namespace StochasticQuantization
namespace Ras
namespace FiniteOperators

open StateSpace
open GlobalCorrector
open GlobalPoisson

def rawOfDistribution {R : ℕ} (x : Distribution R) : SlowForward.RawDistribution :=
  fun g t m =>
    if h : g + t + m ≤ R then
      let gf : Fin (R + 1) := ⟨g, by omega⟩
      let tf : Fin (R + 1) := ⟨t, by omega⟩
      let b : Block R := ⟨(gf, tf), by
        dsimp [gf, tf]
        omega⟩
      let mf : FastState b := ⟨m, by
        unfold freeTotal boundTotal boundGDP boundGTP
        dsimp [b, gf, tf]
        omega⟩
      x b mf
    else 0

theorem rawOfDistribution_encoded
    {R : ℕ} (x : Distribution R) (b : Block R) (m : FastState b) :
    rawOfDistribution x (boundGDP b) (boundGTP b) m.1 = x b m := by
  unfold rawOfDistribution
  have hphys : boundGDP b + boundGTP b + m.1 ≤ R := by
    have hb : boundGDP b + boundGTP b ≤ R := by
      exact b.2
    have hm0 : m.1 ≤ R - (boundGDP b + boundGTP b) := by
      have hm := m.2
      unfold freeTotal boundTotal at hm
      omega
    omega
  simp only [dif_pos hphys]
  congr 1

theorem rawOfDistribution_add
    {R : ℕ} (x y : Distribution R) :
    rawOfDistribution (fun b m => x b m + y b m) =
      fun g t m => rawOfDistribution x g t m + rawOfDistribution y g t m := by
  funext g t m
  unfold rawOfDistribution
  split_ifs <;> simp

theorem rawOfDistribution_smul
    {R : ℕ} (c : ℝ) (x : Distribution R) :
    rawOfDistribution (fun b m => c * x b m) =
      fun g t m => c * rawOfDistribution x g t m := by
  funext g t m
  unfold rawOfDistribution
  split_ifs <;> simp

def slowForward (p : Params) {R : ℕ} (x : Distribution R) : Distribution R :=
  fun b m => SlowForward.apply p R (rawOfDistribution x)
    (boundGDP b) (boundGTP b) m.1

theorem slowForward_add
    (p : Params) {R : ℕ} (x y : Distribution R) :
    slowForward p (fun b m => x b m + y b m) =
      fun b m => slowForward p x b m + slowForward p y b m := by
  funext b m
  unfold slowForward
  rw [rawOfDistribution_add]
  exact SlowForward.apply_add p R (boundGDP b) (boundGTP b) m.1
    (rawOfDistribution x) (rawOfDistribution y)

theorem slowForward_smul
    (p : Params) {R : ℕ} (c : ℝ) (x : Distribution R) :
    slowForward p (fun b m => c * x b m) =
      fun b m => c * slowForward p x b m := by
  funext b m
  unfold slowForward
  rw [rawOfDistribution_smul]
  exact SlowForward.apply_smul p R (boundGDP b) (boundGTP b) m.1 c
    (rawOfDistribution x)

noncomputable def slowLinear (p : Params) (R : ℕ) :
    Distribution R →ₗ[ℝ] Distribution R where
  toFun := slowForward p
  map_add' := by intro x y; exact slowForward_add p x y
  map_smul' := by intro c x; exact slowForward_smul p c x

theorem slowForward_speedBinding
    (c : ℝ) (p : Params) {R : ℕ} (x : Distribution R) :
    slowForward (speedBinding c p) x = fun b m => c * slowForward p x b m := by
  funext b m
  unfold slowForward SlowForward.apply speedBinding
  dsimp
  split_ifs <;> ring

theorem fastForwardNat_add
    (p : Params) (R : ℕ) (b : Block R) (m : ℕ) (z w : ℕ → ℝ) :
    GlobalPoisson.fastForwardNat p R b (fun n => z n + w n) m =
      GlobalPoisson.fastForwardNat p R b z m +
        GlobalPoisson.fastForwardNat p R b w m := by
  unfold GlobalPoisson.fastForwardNat
  split_ifs <;>
    try simp only [BirthDeathPoisson.lowerForward_add,
      BirthDeathPoisson.interiorForward_add,
      BirthDeathPoisson.upperForward_add]
  all_goals ring

theorem fastForwardNat_smul
    (p : Params) (R : ℕ) (b : Block R) (m : ℕ) (c : ℝ) (z : ℕ → ℝ) :
    GlobalPoisson.fastForwardNat p R b (fun n => c * z n) m =
      c * GlobalPoisson.fastForwardNat p R b z m := by
  unfold GlobalPoisson.fastForwardNat
  split_ifs <;>
    try simp only [BirthDeathPoisson.lowerForward_smul,
      BirthDeathPoisson.interiorForward_smul,
      BirthDeathPoisson.upperForward_smul]
  all_goals ring

theorem fastForward_add
    (p : Params) {R : ℕ} (x y : Distribution R) :
    GlobalPoisson.fastForward p (fun b m => x b m + y b m) =
      fun b m => GlobalPoisson.fastForward p x b m +
        GlobalPoisson.fastForward p y b m := by
  funext b m
  unfold GlobalPoisson.fastForward
  rw [GlobalCorrector.extendFastVector_add]
  exact fastForwardNat_add p R b m.1
    (GlobalCorrector.extendFastVector b (x b))
    (GlobalCorrector.extendFastVector b (y b))

theorem fastForward_smul
    (p : Params) {R : ℕ} (c : ℝ) (x : Distribution R) :
    GlobalPoisson.fastForward p (fun b m => c * x b m) =
      fun b m => c * GlobalPoisson.fastForward p x b m := by
  funext b m
  unfold GlobalPoisson.fastForward
  rw [GlobalCorrector.extendFastVector_smul]
  exact fastForwardNat_smul p R b m.1 c
    (GlobalCorrector.extendFastVector b (x b))

noncomputable def fastLinear (p : Params) (R : ℕ) :
    Distribution R →ₗ[ℝ] Distribution R where
  toFun := GlobalPoisson.fastForward p
  map_add' := by intro x y; exact fastForward_add p x y
  map_smul' := by intro c x; exact fastForward_smul p c x

abbrev projectLinear (p : Params) (R : ℕ) := StateSpace.projectLinear p R
abbrev correctorLinear (p : Params) (R : ℕ) := GlobalCorrector.correctorLinear p R

noncomputable def fullLinear (p : Params) (R : ℕ) (epsilon : ℝ) :
    Distribution R →ₗ[ℝ] Distribution R :=
  fastLinear p R + epsilon • slowLinear p R

theorem model3_full_eq_model1_rescaled
    (rhoSOS epsilon : ℝ) (R : ℕ) :
    fullLinear (model3 rhoSOS) R epsilon =
    fullLinear (model1 rhoSOS) R (1000 * epsilon) := by
  apply LinearMap.ext
  intro x
  funext b m
  dsimp [fullLinear, fastLinear, slowLinear]
  rw [show model3 rhoSOS = speedBinding 1000 (model1 rhoSOS) by rfl]
  rw [show fastForward (speedBinding 1000 (model1 rhoSOS)) x b m =
      fastForward (model1 rhoSOS) x b m by rfl]
  rw [slowForward_speedBinding 1000 (model1 rhoSOS) x]
  ring

end FiniteOperators
end Ras
end StochasticQuantization
