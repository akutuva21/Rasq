import Mathlib

noncomputable section

/-!
# L1 and total variation on finite dependent state spaces

Many RasQ objects are finite tables, but the Ras state space is naturally
dependent: the number of allowed free-RasGTP counts depends on the frozen SOS
block.  This file provides one metric implementation for both ordinary and
dependent finite state spaces.
-/

namespace StochasticQuantization
namespace Theory
namespace FiniteMetric

variable {A : Type*} [Fintype A]
variable {B : A → Type*} [∀ a, Fintype (B a)]

/-- L1 norm of a signed finite dependent table. -/
def l1 (x : ∀ a : A, B a → ℝ) : ℝ :=
  ∑ a : A, ∑ b : B a, |x a b|

/-- L1 distance between two finite dependent tables. -/
def distanceL1 (x y : ∀ a : A, B a → ℝ) : ℝ :=
  l1 (fun a b => x a b - y a b)

/-- Total variation, defined as half finite L1 distance. -/
def tv (x y : ∀ a : A, B a → ℝ) : ℝ :=
  (1 / 2 : ℝ) * distanceL1 x y

@[simp] theorem l1_zero :
    l1 (A := A) (B := B) (fun _ _ => (0 : ℝ)) = 0 := by
  simp [l1]

@[simp] theorem distanceL1_self (x : ∀ a : A, B a → ℝ) :
    distanceL1 x x = 0 := by
  simp [distanceL1, l1]

/-- L1 is nonnegative. -/
theorem l1_nonneg (x : ∀ a : A, B a → ℝ) : 0 ≤ l1 x := by
  unfold l1
  positivity

/-- Exact scalar behavior of finite L1. -/
theorem l1_smul (c : ℝ) (x : ∀ a : A, B a → ℝ) :
    l1 (fun a b => c * x a b) = |c| * l1 x := by
  unfold l1
  simp_rw [abs_mul, Finset.mul_sum]

/-- Triangle inequality in component form. -/
theorem l1_add_le
    (x y : ∀ a : A, B a → ℝ) :
    l1 (fun a b => x a b + y a b) ≤ l1 x + l1 y := by
  unfold l1
  calc
    (∑ a : A, ∑ b : B a, |x a b + y a b|) ≤
        ∑ a : A, ∑ b : B a, (|x a b| + |y a b|) := by
          apply Finset.sum_le_sum
          intro a ha
          apply Finset.sum_le_sum
          intro b hb
          exact abs_add_le _ _
    _ = (∑ a : A, ∑ b : B a, |x a b|) +
        (∑ a : A, ∑ b : B a, |y a b|) := by
          simp_rw [Finset.sum_add_distrib]

/-- Conventional factor-two relation between L1 distance and TV. -/
theorem distanceL1_eq_two_mul_tv
    (x y : ∀ a : A, B a → ℝ) :
    distanceL1 x y = 2 * tv x y := by
  unfold tv
  ring

end FiniteMetric
end Theory
end StochasticQuantization

namespace StochasticQuantization
namespace Theory
namespace FiniteMetric

/-!
## Ordinary finite pushforwards

A deterministic coarse-graining cannot increase finite L1/TV distance.  This is
the data-processing fact needed to pass from the full Ras microstate law to the
observable pair `(catalytic class, RasGTP count)` used by the decoder theory.
-/

variable {X C : Type*} [Fintype X] [Fintype C] [DecidableEq C]

/-- L1 norm on an ordinary finite type. -/
def flatL1 (x : X → ℝ) : ℝ := ∑ i : X, |x i|

/-- L1 distance on an ordinary finite type. -/
def flatDistanceL1 (x y : X → ℝ) : ℝ := flatL1 (fun i => x i - y i)

/-- Total variation on an ordinary finite type. -/
def flatTV (x y : X → ℝ) : ℝ := (1 / 2 : ℝ) * flatDistanceL1 x y

/-- Push a signed finite law through a deterministic map. -/
def pushforward (f : X → C) (x : X → ℝ) (c : C) : ℝ :=
  ∑ i : X, if f i = c then x i else 0

/-- Pushforward commutes with subtraction. -/
theorem pushforward_sub (f : X → C) (x y : X → ℝ) (c : C) :
    pushforward f (fun i => x i - y i) c =
      pushforward f x c - pushforward f y c := by
  unfold pushforward
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases h : f i = c <;> simp [h]

/-- Deterministic coarse-graining cannot increase L1 norm. -/
theorem flatL1_pushforward_le (f : X → C) (x : X → ℝ) :
    flatL1 (pushforward f x) ≤ flatL1 x := by
  unfold flatL1 pushforward
  calc
    (∑ c : C, |∑ i : X, if f i = c then x i else 0|) ≤
        ∑ c : C, ∑ i : X, |if f i = c then x i else 0| := by
          apply Finset.sum_le_sum
          intro c hc
          exact Finset.abs_sum_le_sum_abs
            (fun i : X => if f i = c then x i else 0) Finset.univ
    _ = ∑ i : X, |x i| := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro i hi
          rw [Finset.sum_eq_single (f i)]
          · simp
          · intro c hc hne
            simp [Ne.symm hne]
          · simp

/-- Deterministic coarse-graining cannot increase L1 distance. -/
theorem flatDistanceL1_pushforward_le
    (f : X → C) (x y : X → ℝ) :
    flatDistanceL1 (pushforward f x) (pushforward f y) ≤
      flatDistanceL1 x y := by
  unfold flatDistanceL1
  have hsub :
      (fun c => pushforward f x c - pushforward f y c) =
        pushforward f (fun i => x i - y i) := by
    funext c
    symm
    exact pushforward_sub f x y c
  rw [hsub]
  exact flatL1_pushforward_le f (fun i => x i - y i)

/-- Total variation also contracts under deterministic coarse-graining. -/
theorem flatTV_pushforward_le
    (f : X → C) (x y : X → ℝ) :
    flatTV (pushforward f x) (pushforward f y) ≤ flatTV x y := by
  unfold flatTV
  have h := flatDistanceL1_pushforward_le f x y
  nlinarith

end FiniteMetric
end Theory
end StochasticQuantization
