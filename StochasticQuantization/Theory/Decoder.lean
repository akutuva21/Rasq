import Mathlib
import StochasticQuantization.Theory.FiniteMetric

noncomputable section

/-!
# Decoding a discrete molecular state from a biochemical output

Quantization is more informative when phrased as a decoding problem rather than
as visible multimodality.  `joint s y` is a finite joint signed mass over a slow
molecular state `s` and an observed biochemical output `y`.  A deterministic
decoder maps `y` back to a proposed slow state.

The main theorem is intentionally elementary and assumption-light: replacing a
reference joint law by another law can increase decoder error by at most their
L1 distance, equivalently twice the finite total-variation distance.  Taking the
reference law to be the frozen-state codebook gives

    live decoding error <= frozen overlap error + 2 * tracking TV.

No simulator or path-space probability formalism is needed for this statement.
-/

namespace StochasticQuantization
namespace Theory
namespace Decoder

variable {S Y : Type*} [Fintype S] [DecidableEq S] [Fintype Y] [DecidableEq Y]

/-- Finite L1 distance between two joint signed masses. -/
def jointL1 (p q : S → Y → ℝ) : ℝ :=
  FiniteMetric.distanceL1 p q

/-- Finite total-variation distance, defined as half the L1 distance. -/
def jointTV (p q : S → Y → ℝ) : ℝ :=
  FiniteMetric.tv p q

/-- Total mass decoded incorrectly.  For probability laws this is the ordinary
misclassification probability. -/
def errorMass (joint : S → Y → ℝ) (decode : Y → S) : ℝ :=
  ∑ s : S, ∑ y : Y, if decode y = s then 0 else joint s y

/-- Frozen-state reference joint law from slow-state weights and conditional
output codewords. -/
def idealJoint (weight : S → ℝ) (codeword : S → Y → ℝ) : S → Y → ℝ :=
  fun s y => weight s * codeword s y

/-- Decoder error intrinsic to overlap of the frozen-state codewords. -/
def overlapError
    (weight : S → ℝ) (codeword : S → Y → ℝ) (decode : Y → S) : ℝ :=
  errorMass (idealJoint weight codeword) decode

@[simp] theorem jointL1_self (p : S → Y → ℝ) : jointL1 p p = 0 := by
  exact FiniteMetric.distanceL1_self p

/-- Pointwise replacement can increase decoder error by at most finite L1
mismatch.  This theorem does not need normalization assumptions. -/
theorem errorMass_le_add_jointL1
    (p q : S → Y → ℝ) (decode : Y → S) :
    errorMass p decode ≤ errorMass q decode + jointL1 p q := by
  unfold errorMass jointL1 FiniteMetric.distanceL1 FiniteMetric.l1
  calc
    (∑ s : S, ∑ y : Y, if decode y = s then 0 else p s y) ≤
        ∑ s : S, ∑ y : Y,
          ((if decode y = s then 0 else q s y) + |p s y - q s y|) := by
            apply Finset.sum_le_sum
            intro s hs
            apply Finset.sum_le_sum
            intro y hy
            by_cases h : decode y = s
            · simp [h]
            · simp only [h, ↓reduceIte]
              have habs : p s y - q s y ≤ |p s y - q s y| := le_abs_self _
              linarith
    _ = (∑ s : S, ∑ y : Y, if decode y = s then 0 else q s y) +
        (∑ s : S, ∑ y : Y, |p s y - q s y|) := by
          simp_rw [Finset.sum_add_distrib]

/-- L1 and TV are exactly related by the conventional factor two. -/
theorem jointL1_eq_two_mul_tv (p q : S → Y → ℝ) :
    jointL1 p q = 2 * jointTV p q := by
  exact FiniteMetric.distanceL1_eq_two_mul_tv p q


/-- Reference-law version of the decoder decomposition. -/
theorem errorMass_le_reference_add_two_tv
    (p q : S → Y → ℝ) (decode : Y → S) :
    errorMass p decode ≤ errorMass q decode + 2 * jointTV p q := by
  calc
    errorMass p decode ≤ errorMass q decode + jointL1 p q :=
      errorMass_le_add_jointL1 p q decode
    _ = errorMass q decode + 2 * jointTV p q := by
      rw [jointL1_eq_two_mul_tv]

variable {X : Type*} [Fintype X]

/-- Observable joint law obtained by deterministically coarse-graining a finer
finite source state. -/
def observedJoint (observe : X → S × Y) (source : X → ℝ) : S → Y → ℝ :=
  fun s y => FiniteMetric.pushforward observe source (s, y)

/-- The joint TV used by the decoder is exactly the ordinary TV of the
pushforward law on the product observation space. -/
theorem jointTV_observed_eq_flatTV_pushforward
    (observe : X → S × Y) (p q : X → ℝ) :
    jointTV (observedJoint observe p) (observedJoint observe q) =
      FiniteMetric.flatTV
        (FiniteMetric.pushforward observe p)
        (FiniteMetric.pushforward observe q) := by
  unfold jointTV observedJoint
  unfold FiniteMetric.tv FiniteMetric.distanceL1 FiniteMetric.l1
  unfold FiniteMetric.flatTV FiniteMetric.flatDistanceL1 FiniteMetric.flatL1
  rw [← Fintype.sum_prod_type']

/-- Data processing: observable decoder TV cannot exceed TV on the underlying
fine-grained state. -/
theorem jointTV_observed_le_sourceTV
    (observe : X → S × Y) (p q : X → ℝ) :
    jointTV (observedJoint observe p) (observedJoint observe q) ≤
      FiniteMetric.flatTV p q := by
  rw [jointTV_observed_eq_flatTV_pushforward]
  exact FiniteMetric.flatTV_pushforward_le observe p q

/-- **Coarse-grained decoder theorem.**  Decoding after any deterministic
observation map is controlled by frozen/reference decoder error plus twice the
TV mismatch of the full microscopic laws. -/
theorem observed_error_le_reference_add_two_source_tv
    (observe : X → S × Y) (p q : X → ℝ) (decode : Y → S) :
    errorMass (observedJoint observe p) decode ≤
      errorMass (observedJoint observe q) decode +
        2 * FiniteMetric.flatTV p q := by
  have hdec := errorMass_le_reference_add_two_tv
    (observedJoint observe p) (observedJoint observe q) decode
  have htv := jointTV_observed_le_sourceTV observe p q
  nlinarith



/-- Two-stage reference decomposition.  This is useful when the live system is
first compared with an accessible/frozen reference and that reference is then
compared with an ideal well-mixed codebook.  The three terms correspond to
intrinsic overlap, tracking error, and model/accessibility mismatch. -/
theorem errorMass_le_two_stage_reference
    (p q r : S → Y → ℝ) (decode : Y → S) :
    errorMass p decode ≤
      errorMass r decode + 2 * jointTV p q + 2 * jointTV q r := by
  have hpq := errorMass_le_reference_add_two_tv p q decode
  have hqr := errorMass_le_reference_add_two_tv q r decode
  linarith

/-- **Decoder decomposition.**  Live-state decoding error is bounded by the
frozen-codeword overlap plus twice the tracking TV distance. -/
theorem errorMass_le_overlap_add_two_tv
    (joint : S → Y → ℝ)
    (weight : S → ℝ) (codeword : S → Y → ℝ) (decode : Y → S) :
    errorMass joint decode ≤
      overlapError weight codeword decode +
        2 * jointTV joint (idealJoint weight codeword) := by
  calc
    errorMass joint decode ≤
        errorMass (idealJoint weight codeword) decode +
          jointL1 joint (idealJoint weight codeword) :=
      errorMass_le_add_jointL1 joint (idealJoint weight codeword) decode
    _ = overlapError weight codeword decode +
        2 * jointTV joint (idealJoint weight codeword) := by
      rw [jointL1_eq_two_mul_tv]
      rfl

end Decoder
end Theory
end StochasticQuantization
