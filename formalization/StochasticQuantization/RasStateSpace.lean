import Mathlib
import StochasticQuantization.RasGenerator
import StochasticQuantization.RasFastBlock

noncomputable section

/-!
# Full finite fixed-total Ras state space and frozen-equilibrium projector

A block fixes `(boundGDP,boundGTP)`.  Inside that block the only fast coordinate is
free RasGTP.  This dependent encoding contains exactly the physical four-pool count
states with conserved total Ras.
-/

namespace StochasticQuantization
namespace Ras

/- Generic blockwise projector helpers, kept explicit because later proofs unfold
these definitions when comparing local and global formulas. -/
namespace BlockProjection

variable {B : Type*} [Fintype B]
variable {S : B → Type*} [∀ b, Fintype (S b)]

/-- Signed mass in one block. -/
def blockMass (x : ∀ b : B, S b → ℝ) (b : B) : ℝ := ∑ m : S b, x b m

/-- Preserve block mass while replacing its conditional shape by `rho`. -/
def project (rho : ∀ b : B, S b → ℝ) (x : ∀ b : B, S b → ℝ) :
    ∀ b : B, S b → ℝ :=
  fun b m => blockMass x b * rho b m

end BlockProjection

namespace StateSpace

/-- A frozen SOS block: GDP-bound and GTP-bound counts whose sum cannot exceed R. -/
abbrev Block (R : ℕ) :=
  { b : Fin (R + 1) × Fin (R + 1) // (b.1 : ℕ) + (b.2 : ℕ) ≤ R }

/-- GDP-Ras:SOS count. -/
def boundGDP {R : ℕ} (b : Block R) : ℕ := b.1.1
/-- GTP-Ras:SOS count. -/
def boundGTP {R : ℕ} (b : Block R) : ℕ := b.1.2
/-- Total bound SOS/Ras count. -/
def boundTotal {R : ℕ} (b : Block R) : ℕ := boundGDP b + boundGTP b
/-- Number of Ras molecules that remain free in this block. -/
def freeTotal {R : ℕ} (b : Block R) : ℕ := R - boundTotal b
/-- Free RasGTP coordinate inside a frozen block. -/
abbrev FastState {R : ℕ} (b : Block R) := Fin (freeTotal b + 1)
/-- Signed distributions on the complete conserved state space. -/
abbrev Distribution (R : ℕ) := ∀ b : Block R, FastState b → ℝ
/-- One encoded physical state. -/
abbrev EncodedState (R : ℕ) := Σ b : Block R, FastState b

/-- Convert the dependent encoding to the four explicit Ras pools. -/
def toCountState {R : ℕ} (s : EncodedState R) : Generator.CountState where
  boundGDP := boundGDP s.1
  boundGTP := boundGTP s.1
  freeGTP := s.2.1
  freeGDP := R - (boundGDP s.1 + boundGTP s.1 + s.2.1)

/-- Every encoded state obeys total-Ras conservation. -/
theorem toCountState_physical {R : ℕ} (s : EncodedState R) :
    Generator.Physical R (toCountState s) := by
  let g : ℕ := boundGDP s.1
  let t : ℕ := boundGTP s.1
  let m : ℕ := s.2.1
  have hb : g + t ≤ R := by
    simpa [g, t, boundGDP, boundGTP] using s.1.2
  have hm : m < R - (g + t) + 1 := by
    simpa [m, g, t, freeTotal, boundTotal, boundGDP, boundGTP] using s.2.2
  have hsum : g + t + m ≤ R := by omega
  change R - (g + t + m) + m + g + t = R
  omega

/-- Four-pool view carrying conservation transparently. -/
structure FourPoolState (R : ℕ) where
  freeGDP : ℕ
  freeGTP : ℕ
  boundGDP : ℕ
  boundGTP : ℕ
  conservation : freeGDP + freeGTP + boundGDP + boundGTP = R
  deriving Repr

@[ext] theorem FourPoolState.ext {R : ℕ} {x y : FourPoolState R}
    (hfreeGDP : x.freeGDP = y.freeGDP)
    (hfreeGTP : x.freeGTP = y.freeGTP)
    (hboundGDP : x.boundGDP = y.boundGDP)
    (hboundGTP : x.boundGTP = y.boundGTP) : x = y := by
  cases x
  cases y
  simp_all

/-- Convert an encoded state back to all four Ras pools. -/
def toFourPool {R : ℕ} (s : EncodedState R) : FourPoolState R where
  boundGDP := boundGDP s.1
  boundGTP := boundGTP s.1
  freeGTP := s.2.1
  freeGDP := R - (boundGDP s.1 + boundGTP s.1 + s.2.1)
  conservation := by
    have hphys := toCountState_physical s
    unfold Generator.Physical toCountState at hphys
    omega

/-- Construct an encoded state from any conserved four-pool count state. -/
noncomputable def fromFourPool {R : ℕ} (s : FourPoolState R) : EncodedState R := by
  have hcons := s.conservation
  have hbound : s.boundGDP + s.boundGTP ≤ R := by omega
  let g : Fin (R + 1) := ⟨s.boundGDP, by omega⟩
  let t : Fin (R + 1) := ⟨s.boundGTP, by omega⟩
  let b : Block R := ⟨(g,t), by simpa [g, t] using hbound⟩
  let m : FastState b := ⟨s.freeGTP, by
    unfold freeTotal boundTotal boundGDP boundGTP
    dsimp [b, g, t]
    omega⟩
  exact ⟨b,m⟩

/-- The explicit inverse really recovers the original four pools. -/
theorem toFourPool_fromFourPool {R : ℕ} (s : FourPoolState R) :
    toFourPool (fromFourPool s) = s := by
  have hcons := s.conservation
  ext <;>
    simp [fromFourPool, toFourPool, boundGDP, boundGTP, freeTotal, boundTotal]
  omega

/-- Total signed mass in one frozen SOS block. -/
def blockMass {R : ℕ} (x : Distribution R) (b : Block R) : ℝ :=
  BlockProjection.blockMass x b

/-- Frozen-binomial probability for one finite block. -/
def rho (p : Params) {R : ℕ} (b : Block R) (m : FastState b) : ℝ :=
  FastBlock.rho (freeTotal b) m.1
    (FastBlock.activationRate (boundGDP b) (boundGTP b) p.kcat1) p.kcat2

/-- Physical catalytic parameters make every frozen block denominator positive. -/
theorem frozenDen_pos
    (p : Params) {R : ℕ} (b : Block R)
    (hk1 : 0 ≤ p.kcat1) (hk2 : 0 < p.kcat2) :
    0 < FastBlock.activationRate (boundGDP b) (boundGTP b) p.kcat1 + p.kcat2 := by
  unfold FastBlock.activationRate FastBlock.boundTotal
  positivity

/-- Every frozen block PMF has total mass one. -/
theorem sum_rho
    (p : Params) {R : ℕ} (b : Block R)
    (hk1 : 0 ≤ p.kcat1) (hk2 : 0 < p.kcat2) :
    (∑ m : FastState b, rho p b m) = 1 := by
  classical
  let f : ℕ → ℝ := fun n =>
    FastBlock.rho (freeTotal b) n
      (FastBlock.activationRate (boundGDP b) (boundGTP b) p.kcat1) p.kcat2
  change (∑ m : Fin (freeTotal b + 1), f m.1) = 1
  rw [Fin.sum_univ_eq_sum_range f]
  dsimp [f]
  exact FastBlock.sum_rho _ _ _ (ne_of_gt (frozenDen_pos p b hk1 hk2))

/-- Project a signed distribution onto the exact frozen equilibrium in each block. -/
def project (p : Params) {R : ℕ} (x : Distribution R) : Distribution R :=
  BlockProjection.project (rho p) x

/-- Projecting preserves the total mass assigned to each block. -/
theorem blockMass_project
    (p : Params) {R : ℕ} (x : Distribution R) (b : Block R)
    (hk1 : 0 ≤ p.kcat1) (hk2 : 0 < p.kcat2) :
    blockMass (project p x) b = blockMass x b := by
  unfold blockMass project BlockProjection.project BlockProjection.blockMass
  rw [← Finset.mul_sum]
  rw [sum_rho p b hk1 hk2]
  ring

/-- `P` really is a projector. -/
theorem project_project
    (p : Params) {R : ℕ} (x : Distribution R)
    (hk1 : 0 ≤ p.kcat1) (hk2 : 0 < p.kcat2) :
    project p (project p x) = project p x := by
  funext b m
  change blockMass (project p x) b * rho p b m = blockMass x b * rho p b m
  rw [blockMass_project p x b hk1 hk2]

/-- Projection is additive. -/
theorem project_add
    (p : Params) {R : ℕ} (x y : Distribution R) :
    project p (fun b m => x b m + y b m) =
      fun b m => project p x b m + project p y b m := by
  funext b m
  simp [project, BlockProjection.project, BlockProjection.blockMass,
    Finset.sum_add_distrib]
  ring

/-- Projection commutes with scalar multiplication. -/
theorem project_smul
    (p : Params) {R : ℕ} (c : ℝ) (x : Distribution R) :
    project p (fun b m => c * x b m) =
      fun b m => c * project p x b m := by
  funext b m
  unfold project BlockProjection.project BlockProjection.blockMass
  rw [← Finset.mul_sum]
  ring

/-- Linear-map form of the frozen-equilibrium projector. -/
noncomputable def projectLinear (p : Params) (R : ℕ) :
    Distribution R →ₗ[ℝ] Distribution R where
  toFun := project p
  map_add' := by intro x y; exact project_add p x y
  map_smul' := by intro c x; exact project_smul p c x

end StateSpace
end Ras
end StochasticQuantization
