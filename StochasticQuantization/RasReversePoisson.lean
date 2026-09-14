import Mathlib
import StochasticQuantization.RasFiniteOperators
import Mathlib.LinearAlgebra.StdBasis

/-!
# Reverse Poisson identity for the full finite Ras space

`RasGlobalPoisson.lean` constructs the compact corrector and proves

    Q_fast R = I - P.

The stationary-defect theorem needs the reverse order

    R Q_fast = I - P.

For a finite-dimensional space these follow from one another once we also know:

* frozen equilibria are stationary: `Q_fast P = 0`;
* corrections have zero projected block mass: `P R = 0`;
* `P` is idempotent.

The proof below uses the augmented operators

    A = Q_fast + P,   B = R + P.

The known identities give `A B = I`.  A one-sided inverse of an endomorphism on a
finite-dimensional vector space is automatically two-sided, so `B A = I`; the
reverse Poisson identity follows.
-/

namespace StochasticQuantization
namespace Ras
namespace ReversePoisson

open StateSpace
open GlobalPoisson
open GlobalCorrector
open FiniteOperators

/-- The natural-number frozen equilibrium agrees with the state-space PMF on all
physical within-block coordinates. -/
theorem extend_project_eq_scaled_rho
    (p : Params) {R : ℕ} (x : Distribution R) (b : Block R)
    (hden : FastBlock.activationRate (boundGDP b) (boundGTP b) p.kcat1 + p.kcat2 ≠ 0) :
    extendFastVector b ((StateSpace.project p x) b) =
      fun k => blockMass x b *
        BlockPoisson.rho R (boundGDP b) (boundGTP b) p.kcat1 p.kcat2 k := by
  funext k
  by_cases hk : k < freeTotal b + 1
  · simp only [GlobalCorrector.extendFastVector, hk]
    change StateSpace.project p x b ⟨k, hk⟩ =
      blockMass x b * BlockPoisson.rho R (boundGDP b) (boundGTP b)
        p.kcat1 p.kcat2 k
    change blockMass x b * StateSpace.rho p b ⟨k, hk⟩ = _
    rfl
  · have hlt : freeTotal b < k := by omega
    have hFB : BlockPoisson.F R (boundGDP b) (boundGTP b) = freeTotal b := by
      rfl
    simp [GlobalCorrector.extendFastVector, hk]
    unfold BlockPoisson.rho FastBlock.rho FastBlock.rhoWeight
    rw [hFB]
    have hchoose : (freeTotal b).choose k = 0 := by
      exact Nat.choose_eq_zero_of_lt hlt
    simp [hchoose]

/-- One frozen-binomial block is stationary under the fast Ras generator. -/
theorem fastForwardNat_rho_zero
    (p : Params) {R : ℕ} (b : Block R) (m : FastState b) :
    fastForwardNat p R b
      (BlockPoisson.rho R (boundGDP b) (boundGTP b) p.kcat1 p.kcat2) m.1 = 0 := by
  unfold fastForwardNat
  by_cases hF : freeTotal b = 0
  · simp [hF]
  · have hFpos : 0 < freeTotal b := Nat.pos_of_ne_zero hF
    have hFB : BlockPoisson.F R (boundGDP b) (boundGTP b) = freeTotal b := by
      rfl
    simp only [dif_neg hF]
    by_cases h0 : m.1 = 0
    · simp only [dif_pos h0]
      rw [BirthDeathPoisson.lowerForward_eq_neg_flux]
      rw [BlockPoisson.rho_zeroFlux]
      · simp
      · exact hFpos
    · simp only [dif_neg h0]
      by_cases htop : m.1 = freeTotal b
      · simp only [dif_pos htop]
        rw [BirthDeathPoisson.upperForward_eq_flux]
        rw [BlockPoisson.rho_zeroFlux]
        · rw [hFB]
          omega
      · simp only [dif_neg htop]
        rw [BirthDeathPoisson.interiorForward_eq_fluxDifference]
        rw [BlockPoisson.rho_zeroFlux, BlockPoisson.rho_zeroFlux]
        · ring
        · rw [hFB]
          have hm := m.2
          omega
        · rw [hFB]
          have hm := m.2
          omega

/-- Frozen-equilibrium projection is killed by the fast generator: `Q_fast P=0`. -/
theorem fastForward_project_zero
    (p : Params) {R : ℕ} (x : Distribution R)
    (hk1 : 0 ≤ p.kcat1) (hk2 : 0 < p.kcat2) :
    GlobalPoisson.fastForward p (StateSpace.project p x) = 0 := by
  funext b m
  have hden := ne_of_gt (StateSpace.frozenDen_pos p b hk1 hk2)
  unfold GlobalPoisson.fastForward
  rw [extend_project_eq_scaled_rho p x b hden]
  have hlin := fastForwardNat_smul p R b m.1 (blockMass x b)
    (BlockPoisson.rho R (boundGDP b) (boundGTP b) p.kcat1 p.kcat2)
  rw [hlin, fastForwardNat_rho_zero p b m]
  simp

/-- Map-level form of `Q_fast R = I-P`. -/
theorem fast_comp_corrector
    (p : Params) (Rtot : ℕ)
    (hk1 : 0 ≤ p.kcat1) (hk2 : 0 < p.kcat2) :
    (FiniteOperators.fastLinear p Rtot).comp
        (FiniteOperators.correctorLinear p Rtot) =
      LinearMap.id - StateSpace.projectLinear p Rtot := by
  apply LinearMap.ext
  intro x
  funext b m
  simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.id_apply]
  exact GlobalPoisson.fastForward_corrector_all p x b m
    (ne_of_gt hk2) (ne_of_gt (StateSpace.frozenDen_pos p b hk1 hk2))

/-- Map-level `Q_fast P=0`. -/
theorem fast_comp_project
    (p : Params) (Rtot : ℕ)
    (hk1 : 0 ≤ p.kcat1) (hk2 : 0 < p.kcat2) :
    (FiniteOperators.fastLinear p Rtot).comp
        (StateSpace.projectLinear p Rtot) = 0 := by
  apply LinearMap.ext
  intro x
  funext b m
  have h := congrFun (congrFun (fastForward_project_zero p x hk1 hk2) b) m
  simpa [FiniteOperators.fastLinear, StateSpace.projectLinear] using h

/-- Map-level `P R=0`: compact corrections have zero block mass. -/
theorem project_comp_corrector
    (p : Params) (Rtot : ℕ)
    (hk1 : 0 ≤ p.kcat1) (hk2 : 0 < p.kcat2) :
    (StateSpace.projectLinear p Rtot).comp
        (FiniteOperators.correctorLinear p Rtot) = 0 := by
  apply LinearMap.ext
  intro x
  funext b m
  have hden : ∀ b : Block Rtot,
      FastBlock.activationRate (boundGDP b) (boundGTP b) p.kcat1 + p.kcat2 ≠ 0 :=
    fun b => ne_of_gt (StateSpace.frozenDen_pos p b hk1 hk2)
  have h := congrFun (congrFun (GlobalCorrector.project_corrector_zero p x hden) b) m
  simpa [StateSpace.projectLinear, GlobalCorrector.correctorLinear] using h

/-- Map-level `P^2=P`. -/
theorem project_idempotent
    (p : Params) (Rtot : ℕ)
    (hk1 : 0 ≤ p.kcat1) (hk2 : 0 < p.kcat2) :
    (StateSpace.projectLinear p Rtot).comp
        (StateSpace.projectLinear p Rtot) = StateSpace.projectLinear p Rtot := by
  apply LinearMap.ext
  intro x
  funext b m
  simp only [LinearMap.comp_apply]
  exact congrFun (congrFun (StateSpace.project_project p x hk1 hk2) b) m

/-- **Reverse Poisson identity.**

This is the key finite-dimensional step needed by the full stationary theorem:

    R Q_fast = I - P.
-/
theorem corrector_comp_fast
    (p : Params) (Rtot : ℕ)
    (hk1 : 0 ≤ p.kcat1) (hk2 : 0 < p.kcat2) :
    (FiniteOperators.correctorLinear p Rtot).comp
        (FiniteOperators.fastLinear p Rtot) =
      LinearMap.id - StateSpace.projectLinear p Rtot := by
  let Q := FiniteOperators.fastLinear p Rtot
  let P := StateSpace.projectLinear p Rtot
  let K := FiniteOperators.correctorLinear p Rtot
  let A : Distribution Rtot →ₗ[ℝ] Distribution Rtot := Q + P
  let B : Distribution Rtot →ₗ[ℝ] Distribution Rtot := K + P
  have hQK : Q.comp K = LinearMap.id - P := by
    simpa [Q, P, K] using fast_comp_corrector p Rtot hk1 hk2
  have hQP : Q.comp P = 0 := by
    simpa [Q, P] using fast_comp_project p Rtot hk1 hk2
  have hPK : P.comp K = 0 := by
    simpa [P, K] using project_comp_corrector p Rtot hk1 hk2
  have hPP : P.comp P = P := by
    simpa [P] using project_idempotent p Rtot hk1 hk2
  have hAB : A.comp B = LinearMap.id := by
    apply LinearMap.ext
    intro x
    simp only [A, B, LinearMap.comp_apply, LinearMap.add_apply]
    have h1 := congrArg (fun L : Distribution Rtot →ₗ[ℝ] Distribution Rtot => L x) hQK
    have h2 := congrArg (fun L : Distribution Rtot →ₗ[ℝ] Distribution Rtot => L x) hQP
    have h3 := congrArg (fun L : Distribution Rtot →ₗ[ℝ] Distribution Rtot => L x) hPK
    have h4 := congrArg (fun L : Distribution Rtot →ₗ[ℝ] Distribution Rtot => L x) hPP
    simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.id_apply,
      LinearMap.zero_apply] at h1 h2 h3 h4
    rw [map_add, map_add, h1, h2, h3, h4]
    abel
  have hBA : B.comp A = LinearMap.id :=
    (LinearMap.comp_eq_id_comm ℝ (Distribution Rtot)).mp hAB

  -- First derive K P = 0 from A P = P and B A = I.
  have hAP : A.comp P = P := by
    apply LinearMap.ext
    intro x
    simp only [A, LinearMap.comp_apply, LinearMap.add_apply]
    have h2 := congrArg (fun L : Distribution Rtot →ₗ[ℝ] Distribution Rtot => L x) hQP
    have h4 := congrArg (fun L : Distribution Rtot →ₗ[ℝ] Distribution Rtot => L x) hPP
    simp only [LinearMap.comp_apply, LinearMap.zero_apply] at h2
    simp only [LinearMap.comp_apply] at h4
    rw [h2, h4]
    simp
  have hBP : B.comp P = P := by
    calc
      B.comp P = B.comp (A.comp P) := by rw [hAP]
      _ = (B.comp A).comp P := by ext x; rfl
      _ = LinearMap.id.comp P := by rw [hBA]
      _ = P := by ext x; rfl
  have hKP : K.comp P = 0 := by
    apply LinearMap.ext
    intro x
    change K (P x) = 0
    have hb := congrArg (fun L : Distribution Rtot →ₗ[ℝ] Distribution Rtot => L x) hBP
    have hp := congrArg (fun L : Distribution Rtot →ₗ[ℝ] Distribution Rtot => L x) hPP
    change K (P x) + P (P x) = P x at hb
    change P (P x) = P x at hp
    rw [hp] at hb
    simpa only [add_eq_right] using hb

  -- `P B=P`, hence using `A B=I` gives `P A=P`, so P Q=0.
  have hPB : P.comp B = P := by
    apply LinearMap.ext
    intro x
    have hpk := congrArg (fun L : Distribution Rtot →ₗ[ℝ] Distribution Rtot => L x) hPK
    have hpp := congrArg (fun L : Distribution Rtot →ₗ[ℝ] Distribution Rtot => L x) hPP
    change P (K x) = 0 at hpk
    change P (P x) = P x at hpp
    change P (K x + P x) = P x
    rw [map_add, hpk, hpp]
    simp
  have hPA : P.comp A = P := by
    calc
      P.comp A = (P.comp B).comp A := by rw [hPB]
      _ = P.comp (B.comp A) := by ext x; rfl
      _ = P.comp LinearMap.id := by rw [hBA]
      _ = P := by ext x; rfl
  have hPQ : P.comp Q = 0 := by
    apply LinearMap.ext
    intro x
    have hpa := congrArg (fun L : Distribution Rtot →ₗ[ℝ] Distribution Rtot => L x) hPA
    have hpp := congrArg (fun L : Distribution Rtot →ₗ[ℝ] Distribution Rtot => L x) hPP
    change P (Q x + P x) = P x at hpa
    change P (P x) = P x at hpp
    rw [map_add, hpp] at hpa
    have hzero : P (Q x) = 0 := by
      simpa only [add_eq_right] using hpa
    change P (Q x) = 0
    exact hzero

  -- Expand `B A=I`; all cross terms are now known to vanish.
  apply LinearMap.ext
  intro x
  change K (Q x) = x - P x
  have hba := congrArg (fun L : Distribution Rtot →ₗ[ℝ] Distribution Rtot => L x) hBA
  have hkp := congrArg (fun L : Distribution Rtot →ₗ[ℝ] Distribution Rtot => L x) hKP
  have hpq := congrArg (fun L : Distribution Rtot →ₗ[ℝ] Distribution Rtot => L x) hPQ
  have hpp := congrArg (fun L : Distribution Rtot →ₗ[ℝ] Distribution Rtot => L x) hPP
  simp only [B, A, LinearMap.comp_apply, LinearMap.add_apply, LinearMap.id_apply] at hba
  simp only [LinearMap.comp_apply, LinearMap.zero_apply] at hkp hpq
  simp only [LinearMap.comp_apply] at hpp
  rw [map_add, map_add, hkp, hpq, hpp] at hba
  simp only [map_add, add_zero, zero_add] at hba
  exact eq_sub_iff_add_eq.mpr hba

end ReversePoisson
end Ras
end StochasticQuantization
