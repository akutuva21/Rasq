import Mathlib
import StochasticQuantization.RasFullStationary
import StochasticQuantization.Theory

noncomputable section

/-!
# Ras-specific bridge to the general stochastic-quantization theory

The generic theory files deliberately avoid Ras-specific state-space details.
This module connects those abstractions back to the exact finite Ras model:

* the stationary TV defect is the Ras tracking-error term;
* the slow Ras microstate `(boundGDP,boundGTP)` is mapped to its total catalytic
  SOS occupancy;
* frozen output codewords are indexed by that catalytic class; and
* redistributing slow-state weight inside a fixed catalytic class cannot change
  the frozen downstream mixture.
-/

namespace StochasticQuantization
namespace Ras
namespace TheoryBridge

open StateSpace
open FiniteOperators

/-- Tracking error between the live stationary law and its frozen-SOS projection. -/
def trackingTV {R : ℕ} (p : Params) (pi : Distribution R) : ℝ :=
  FiniteTV.tv pi (StateSpace.project p pi)

/-- The existing exact stationary theorem is exactly a formula for the tracking
error used by the broader theory. -/
theorem trackingTV_stationary_exact
    (p : Params) (Rtot : ℕ) (epsilon : ℝ) (pi : Distribution Rtot)
    (hk1 : 0 ≤ p.kcat1) (hk2 : 0 < p.kcat2)
    (hstationary : fullLinear p Rtot epsilon pi = 0) :
    trackingTV p pi =
      (|epsilon| / 2) *
        FiniteTV.l1 (GlobalCorrector.corrector p (slowForward p pi)) := by
  exact FullStationary.stationary_tv_exact
    p Rtot epsilon pi hk1 hk2 hstationary

/-- Catalytic equivalence class of a slow Ras microstate: total SOS-bound Ras. -/
def catalyticClass {R : ℕ} (b : Block R) : Fin (R + 1) :=
  ⟨boundTotal b, by
    have hb : boundTotal b ≤ R := by
      simpa [boundTotal, boundGDP, boundGTP] using b.2
    omega⟩

/-- A common fixed output alphabet `0,...,R` for comparing frozen Ras codewords.
Impossible free-RasGTP counts outside the class-specific free pool receive zero
mass. -/
def codeword (p : Params) (R : ℕ) (c : Fin (R + 1)) (m : Fin (R + 1)) : ℝ :=
  if m.1 ≤ R - c.1 then
    FastBlock.rho (R - c.1) m.1 ((c.1 : ℝ) * p.kcat1) p.kcat2
  else 0

/-- Changing only SOS binding/unbinding speed leaves the frozen Ras codebook
exactly unchanged.  This is the formal separation between codeword geometry and
slow occupancy kinetics. -/
theorem codeword_speedBinding
    (scale : ℝ) (p : Params) (R : ℕ)
    (c m : Fin (R + 1)) :
    codeword (speedBinding scale p) R c m = codeword p R c m := by
  rfl

/-- In particular Models 1 and 3 have the same complete frozen codebook, not
merely the same conditional means. -/
theorem model1_model3_same_codeword
    (rhoSOS : ℝ) (R : ℕ) (c m : Fin (R + 1)) :
    codeword (model3 rhoSOS) R c m = codeword (model1 rhoSOS) R c m := by
  rfl

/-- The common-alphabet codeword agrees exactly with the block PMF on every
physical fast state. -/
theorem codeword_eq_block_rho
    (p : Params) {R : ℕ} (b : Block R) (m : FastState b) :
    codeword p R (catalyticClass b) ⟨m.1, by
      have hb : boundTotal b ≤ R := by
        simpa [boundTotal, boundGDP, boundGTP] using b.2
      have hm : m.1 ≤ R - boundTotal b := by
        have hmlt := m.2
        unfold freeTotal at hmlt
        omega
      omega⟩ = StateSpace.rho p b m := by
  have hm : m.1 ≤ R - boundTotal b := by
    have hmlt := m.2
    unfold freeTotal at hmlt
    omega
  have hm' : m.1 ≤ R - (boundGDP b + boundGTP b) := by
    simpa [boundTotal] using hm
  unfold codeword catalyticClass StateSpace.rho
  split
  · simp [freeTotal, FastBlock.activationRate, FastBlock.boundTotal,
      boundTotal, boundGDP, boundGTP]
  · rename_i hnot
    exfalso
    apply hnot
    simpa [boundTotal, boundGDP, boundGTP] using hm

/-- Slow-state block mass used as the weight of one microscopic SOS state. -/
def blockWeight {R : ℕ} (x : Distribution R) (b : Block R) : ℝ :=
  StateSpace.blockMass x b

/-- Frozen Ras output mixture written over microscopic SOS states. -/
def frozenOutputMixture
    (p : Params) {R : ℕ} (x : Distribution R) (m : Fin (R + 1)) : ℝ :=
  StochasticQuantization.Theory.CatalyticLumping.microMixture
    (catalyticClass (R := R)) (codeword p R) (blockWeight x) m

/-- At fixed slow-state weights, changing only SOS binding speed cannot alter the
frozen output mixture. -/
theorem frozenOutputMixture_speedBinding
    (scale : ℝ) (p : Params) {R : ℕ} (x : Distribution R) :
    frozenOutputMixture (speedBinding scale p) x = frozenOutputMixture p x := by
  funext m
  unfold frozenOutputMixture StochasticQuantization.Theory.CatalyticLumping.microMixture
  apply Finset.sum_congr rfl
  intro b hb
  rw [codeword_speedBinding]

/-- If two slow-state laws have the same total mass at every total-SOS occupancy,
their frozen Ras output mixtures are identical, even if GDP-bound and GTP-bound
microstate weights differ inside an occupancy class. -/
theorem frozenOutputMixture_eq_of_catalytic_class_mass_eq
    (p : Params) {R : ℕ} (x y : Distribution R)
    (hclass : ∀ c : Fin (R + 1),
      StochasticQuantization.Theory.CatalyticLumping.classMass
        (catalyticClass (R := R)) (blockWeight x) c =
      StochasticQuantization.Theory.CatalyticLumping.classMass
        (catalyticClass (R := R)) (blockWeight y) c) :
    frozenOutputMixture p x = frozenOutputMixture p y := by
  exact StochasticQuantization.Theory.CatalyticLumping.microMixture_eq_of_classMass_eq
    (catalyticClass (R := R)) (codeword p R)
    (blockWeight x) (blockWeight y) hclass


/-- Flatten the dependent Ras distribution onto its sigma-encoded physical state
space. -/
def encodedMass {R : ℕ} (x : Distribution R) : EncodedState R → ℝ :=
  fun s => x s.1 s.2

/-- Flattening is metric-preserving: ordinary TV on encoded states is exactly the
existing dependent Ras TV. -/
theorem flatTV_encodedMass_eq
    {R : ℕ} (x y : Distribution R) :
    StochasticQuantization.Theory.FiniteMetric.flatTV
      (encodedMass x) (encodedMass y) = FiniteTV.tv x y := by
  unfold StochasticQuantization.Theory.FiniteMetric.flatTV
    StochasticQuantization.Theory.FiniteMetric.flatDistanceL1
    StochasticQuantization.Theory.FiniteMetric.flatL1
    FiniteTV.tv StochasticQuantization.Theory.FiniteMetric.tv
    StochasticQuantization.Theory.FiniteMetric.distanceL1
    StochasticQuantization.Theory.FiniteMetric.l1 encodedMass
  congr 1
  exact Fintype.sum_sigma'
    (fun b m => |x b m - y b m|)

/-- Free-RasGTP count embedded in the common output alphabet `0,...,R`. -/
def outputCount {R : ℕ} (s : EncodedState R) : Fin (R + 1) :=
  ⟨s.2.1, by
    have hm : s.2.1 ≤ freeTotal s.1 := by
      have hlt := s.2.2
      omega
    have hfree : freeTotal s.1 ≤ R := Nat.sub_le _ _
    omega⟩

/-- Observable pair used for biochemical decoding: catalytic SOS class and
free-RasGTP count. -/
def observation {R : ℕ} (s : EncodedState R) :
    Fin (R + 1) × Fin (R + 1) :=
  (catalyticClass s.1, outputCount s)

/-- Observable joint signed law obtained from a full Ras distribution. -/
def observableJoint {R : ℕ} (x : Distribution R) :
    Fin (R + 1) → Fin (R + 1) → ℝ :=
  StochasticQuantization.Theory.Decoder.observedJoint
    (observation (R := R)) (encodedMass x)

/-- Error mass for decoding total catalytic SOS occupancy from RasGTP count. -/
def decodeError {R : ℕ}
    (x : Distribution R) (decode : Fin (R + 1) → Fin (R + 1)) : ℝ :=
  StochasticQuantization.Theory.Decoder.errorMass (observableJoint x) decode

/-- **Ras decoder theorem.**  Live decoding error is at most frozen-state overlap
error plus twice the exact Ras tracking TV.  No bistability assumption appears. -/
theorem decodeError_le_frozen_add_tracking
    (p : Params) {R : ℕ} (x : Distribution R)
    (decode : Fin (R + 1) → Fin (R + 1)) :
    decodeError x decode ≤
      decodeError (StateSpace.project p x) decode + 2 * trackingTV p x := by
  have h :=
    StochasticQuantization.Theory.Decoder.observed_error_le_reference_add_two_source_tv
      (observation (R := R))
      (encodedMass x) (encodedMass (StateSpace.project p x)) decode
  rw [flatTV_encodedMass_eq] at h
  exact h

/-- At stationarity, the decoder theorem composes with the exact slow/fast defect
identity.  The extra decoding penalty beyond frozen overlap is bounded by the
SOS switching disturbance passed through the Ras corrector. -/
theorem stationary_decodeError_bound
    (p : Params) (Rtot : ℕ) (epsilon : ℝ) (pi : Distribution Rtot)
    (decode : Fin (Rtot + 1) → Fin (Rtot + 1))
    (hk1 : 0 ≤ p.kcat1) (hk2 : 0 < p.kcat2)
    (hstationary : fullLinear p Rtot epsilon pi = 0) :
    decodeError pi decode ≤
      decodeError (StateSpace.project p pi) decode +
        |epsilon| * FiniteTV.l1
          (GlobalCorrector.corrector p (slowForward p pi)) := by
  calc
    decodeError pi decode ≤
        decodeError (StateSpace.project p pi) decode + 2 * trackingTV p pi :=
      decodeError_le_frozen_add_tracking p pi decode
    _ = decodeError (StateSpace.project p pi) decode +
        |epsilon| * FiniteTV.l1
          (GlobalCorrector.corrector p (slowForward p pi)) := by
      rw [trackingTV_stationary_exact p Rtot epsilon pi hk1 hk2 hstationary]
      ring

end TheoryBridge
end Ras
end StochasticQuantization
