import Mathlib
import StochasticQuantization.Ras
import StochasticQuantization.BirthDeath

noncomputable section

namespace StochasticQuantization
namespace Ras
namespace FastBlock

/-- Number of SOS-bound Ras molecules. -/
def boundTotal (g t : ℕ) : ℕ := g + t
/-- Number of free Ras molecules when `(g,t)` is frozen. -/
def freePool (R g t : ℕ) : ℕ := R - boundTotal g t
/-- Per-free-Ras activation rate in a frozen block. -/
def activationRate (g t : ℕ) (kcat1 : ℝ) : ℝ :=
  (boundTotal g t : ℝ) * kcat1
/-- Upward rate `m -> m+1`. -/
def birth (R g t m : ℕ) (kcat1 : ℝ) : ℝ :=
  ((freePool R g t - m : ℕ) : ℝ) * activationRate g t kcat1
/-- Downward rate `m -> m-1`. -/
def death (m : ℕ) (kcat2 : ℝ) : ℝ := (m : ℝ) * kcat2
/-- Unnormalized binomial stationary weight. -/
def rhoWeight (F m : ℕ) (a d : ℝ) : ℝ :=
  (F.choose m : ℝ) * a ^ m * d ^ (F - m)
/-- Normalizing constant. -/
def rhoNorm (F : ℕ) (a d : ℝ) : ℝ := (a + d) ^ F
/-- Closed-form frozen-block stationary probability. -/
def rho (F m : ℕ) (a d : ℝ) : ℝ := rhoWeight F m a d / rhoNorm F a d

theorem rhoNorm_ne_zero (F : ℕ) (a d : ℝ) (h : a + d ≠ 0) :
    rhoNorm F a d ≠ 0 := by
  unfold rhoNorm
  exact pow_ne_zero _ h

theorem sum_rhoWeight (F : ℕ) (a d : ℝ) :
    (∑ m ∈ Finset.range (F + 1), rhoWeight F m a d) = (a + d) ^ F := by
  rw [add_pow]
  apply Finset.sum_congr rfl
  intro m hm
  unfold rhoWeight
  ring

theorem sum_rho (F : ℕ) (a d : ℝ) (h : a + d ≠ 0) :
    (∑ m ∈ Finset.range (F + 1), rho F m a d) = 1 := by
  unfold rho
  rw [← Finset.sum_div]
  rw [sum_rhoWeight]
  unfold rhoNorm
  exact div_self (pow_ne_zero _ h)

theorem sum_m_mul_rhoWeight (F : ℕ) (a d : ℝ) :
    (∑ m ∈ Finset.range (F + 1), (m : ℝ) * rhoWeight F m a d) =
      (F : ℝ) * a * (a + d) ^ (F - 1) := by
  induction F with
  | zero => simp [rhoWeight]
  | succ F ih =>
      let A : ℝ := ∑ i ∈ Finset.range (F + 1),
        (i : ℝ) * rhoWeight F i a d
      let B : ℝ := ∑ i ∈ Finset.range (F + 1), rhoWeight F i a d
      have hsplit := Finset.sum_choose_succ_mul
        (fun i j : ℕ => (i : ℝ) * a ^ i * d ^ j) F
      have hfirst :
          (∑ i ∈ Finset.range (F + 1),
            (F.choose i : ℝ) * ((i : ℝ) * a ^ i * d ^ (F + 1 - i))) = d * A := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        have hiF : i ≤ F := Nat.le_of_lt_succ (Finset.mem_range.1 hi)
        have hpow : F + 1 - i = (F - i) + 1 := by omega
        simp only [rhoWeight]
        rw [hpow, pow_succ]
        ring
      have hsecond :
          (∑ i ∈ Finset.range (F + 1),
            (F.choose i : ℝ) * (((i + 1 : ℕ) : ℝ) * a ^ (i + 1) * d ^ (F - i))) =
            a * (A + B) := by
        rw [mul_add, Finset.mul_sum, Finset.mul_sum]
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro i hi
        simp only [A, B, rhoWeight]
        norm_num [pow_succ, Nat.cast_add]
        ring
      calc
        (∑ m ∈ Finset.range (F + 1 + 1),
            (m : ℝ) * rhoWeight (F + 1) m a d) =
          (∑ m ∈ Finset.range (F + 1 + 1),
            ((F + 1).choose m : ℝ) * ((m : ℝ) * a ^ m * d ^ (F + 1 - m))) := by
              apply Finset.sum_congr rfl
              intro m hm
              unfold rhoWeight
              ring
        _ = (∑ i ∈ Finset.range (F + 1),
              (F.choose i : ℝ) * ((i : ℝ) * a ^ i * d ^ (F + 1 - i))) +
            ∑ i ∈ Finset.range (F + 1),
              (F.choose i : ℝ) * (((i + 1 : ℕ) : ℝ) * a ^ (i + 1) * d ^ (F - i)) := by
              simpa using hsplit
        _ = d * A + a * (A + B) := by rw [hfirst, hsecond]
        _ = (F.succ : ℝ) * a * (a + d) ^ (F.succ - 1) := by
              dsimp [A, B]
              rw [ih, sum_rhoWeight]
              cases F with
              | zero => simp
              | succ F =>
                  rw [show F.succ - 1 = F by omega, pow_succ]
                  norm_num [Nat.cast_add]
                  ring

theorem mean_rho (F : ℕ) (a d : ℝ) (h : a + d ≠ 0) :
    (∑ m ∈ Finset.range (F + 1), (m : ℝ) * rho F m a d) =
      (F : ℝ) * a / (a + d) := by
  unfold rho
  simp_rw [← mul_div_assoc]
  rw [← Finset.sum_div]
  rw [sum_m_mul_rhoWeight]
  unfold rhoNorm
  cases F with
  | zero => simp
  | succ F =>
      simp only [Nat.succ_sub_one]
      field_simp [h]
      ring

theorem rhoWeight_detailedBalance
    (F m : ℕ) (a d : ℝ) (hm : m < F) :
    rhoWeight F m a d * (((F - m : ℕ) : ℝ) * a) =
      rhoWeight F (m + 1) a d * (((m + 1 : ℕ) : ℝ) * d) := by
  unfold rhoWeight
  have hsub : F - m = (F - (m + 1)) + 1 := by omega
  have hchoose := Nat.choose_succ_right_eq F m
  have hchooseR :
      (F.choose (m + 1) : ℝ) * ((m + 1 : ℕ) : ℝ) =
        (F.choose m : ℝ) * ((F - m : ℕ) : ℝ) := by
    exact_mod_cast hchoose
  rw [hsub, pow_succ]
  rw [pow_succ a m]
  have hsub' : F - (m + 1) + 1 = F - m := by omega
  rw [hsub']
  calc
    (F.choose m : ℝ) * a ^ m * (d ^ (F - (m + 1)) * d) *
        (((F - m : ℕ) : ℝ) * a) =
      (F.choose m : ℝ) * ((F - m : ℕ) : ℝ) * (a ^ m * a) *
        (d ^ (F - (m + 1)) * d) := by ring
    _ = (F.choose (m + 1) : ℝ) * ((m + 1 : ℕ) : ℝ) *
        (a ^ m * a) * (d ^ (F - (m + 1)) * d) := by rw [hchooseR]
    _ = (F.choose (m + 1) : ℝ) * (a ^ m * a) *
        d ^ (F - (m + 1)) * (((m + 1 : ℕ) : ℝ) * d) := by ring

theorem rho_detailedBalance
    (F m : ℕ) (a d : ℝ) (hm : m < F) :
    rho F m a d * (((F - m : ℕ) : ℝ) * a) =
      rho F (m + 1) a d * (((m + 1 : ℕ) : ℝ) * d) := by
  unfold rho
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div,
    rhoWeight_detailedBalance F m a d hm]

theorem ras_frozen_mean
    (R g t : ℕ) (kcat1 kcat2 : ℝ)
    (hden : activationRate g t kcat1 + kcat2 ≠ 0) :
    (∑ m ∈ Finset.range (freePool R g t + 1),
      (m : ℝ) * rho (freePool R g t) m (activationRate g t kcat1) kcat2) =
      (freePool R g t : ℝ) * activationRate g t kcat1 /
        (activationRate g t kcat1 + kcat2) := by
  exact mean_rho _ _ _ hden

end FastBlock
end Ras
end StochasticQuantization
