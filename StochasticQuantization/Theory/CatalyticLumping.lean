import Mathlib
import StochasticQuantization.Theory.FiniteMetric

noncomputable section

/-!
# Catalytic equivalence classes and feedback/lumping

A slow biochemical network can have many microscopic states that present the
same catalytic capacity to a downstream fast system.  `classOf` maps slow
microstates to these catalytic equivalence classes; `codeword` depends only on
the class.

The main theorem says that if two slow-state laws have the same total weight in
every catalytic class, then they induce the same downstream mixture, regardless
of how weight is redistributed among microstates inside each class.  This is the
formal core of the statement that feedback can change microscopic occupancy
statistics without moving a codeword unless it changes catalytic-class weights
or the fast chemistry itself.
-/

namespace StochasticQuantization
namespace Theory
namespace CatalyticLumping

variable {S C Y : Type*}
variable [Fintype S] [Fintype C] [DecidableEq C] [Fintype Y]

/-- Total slow-state weight in one catalytic equivalence class. -/
def classMass (classOf : S → C) (weight : S → ℝ) (c : C) : ℝ :=
  FiniteMetric.pushforward classOf weight c

/-- Downstream mixture written directly over slow microstates. -/
def microMixture
    (classOf : S → C) (codeword : C → Y → ℝ)
    (weight : S → ℝ) (y : Y) : ℝ :=
  ∑ s : S, weight s * codeword (classOf s) y

/-- The same mixture regrouped by catalytic class. -/
def classMixture
    (classOf : S → C) (codeword : C → Y → ℝ)
    (weight : S → ℝ) (y : Y) : ℝ :=
  ∑ c : C, classMass classOf weight c * codeword c y

/-- Regrouping microstates by catalytic class leaves the downstream mixture
unchanged. -/
theorem microMixture_eq_classMixture
    (classOf : S → C) (codeword : C → Y → ℝ)
    (weight : S → ℝ) (y : Y) :
    microMixture classOf codeword weight y =
      classMixture classOf codeword weight y := by
  unfold microMixture classMixture classMass FiniteMetric.pushforward
  calc
    (∑ s : S, weight s * codeword (classOf s) y) =
        ∑ s : S, ∑ c : C,
          if classOf s = c then weight s * codeword c y else 0 := by
            apply Finset.sum_congr rfl
            intro s hs
            simp
    _ = ∑ c : C, ∑ s : S,
          if classOf s = c then weight s * codeword c y else 0 := by
            rw [Finset.sum_comm]
    _ = ∑ c : C,
          (∑ s : S, if classOf s = c then weight s else 0) * codeword c y := by
            apply Finset.sum_congr rfl
            intro c hc
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro s hs
            by_cases h : classOf s = c <;> simp [h]

/-- **Lumping theorem.** Equal catalytic-class masses imply identical downstream
mixtures. -/
theorem microMixture_eq_of_classMass_eq
    (classOf : S → C) (codeword : C → Y → ℝ)
    (w₁ w₂ : S → ℝ)
    (hclass : ∀ c, classMass classOf w₁ c = classMass classOf w₂ c) :
    microMixture classOf codeword w₁ = microMixture classOf codeword w₂ := by
  funext y
  rw [microMixture_eq_classMixture, microMixture_eq_classMixture]
  unfold classMixture
  apply Finset.sum_congr rfl
  intro c hc
  rw [hclass c]

end CatalyticLumping
end Theory
end StochasticQuantization
