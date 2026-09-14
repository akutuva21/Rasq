import Mathlib
import StochasticQuantization.Core

noncomputable section

/-!
# Finite stochastic target chain

At fixed catalyst count `n`, let `m` be the number of active target molecules out
of a finite pool `T`.

    m -> m+1    at rate (T-m) * n*kAct
    m -> m-1    at rate m * kOff

This is the standard finite birth/death chain whose normalized equilibrium weights
are binomial.  Instead of importing a large CTMC framework, we prove the local
*detailed-balance recurrence* directly.  Detailed balance means that, at equilibrium,
probability flux across every neighboring pair cancels exactly.

The recursive weights below are unnormalized.  Normalizing them over `0..T`
produces the stationary distribution.  A future extension can prove the closed-form
`Binomial(T, p_n)` identity inside Lean; the recurrence proved here is already the
mechanistic core of that result.
-/

namespace StochasticQuantization

/-- Upward transition rate `m -> m+1` for the finite target chain. -/
def birthRate (T n m : ℕ) (kAct : ℝ) : ℝ :=
  ((T - m : ℕ) : ℝ) * effectiveActivationRate n kAct

/-- Downward transition rate `m -> m-1`. -/
def deathRate (m : ℕ) (kOff : ℝ) : ℝ := (m : ℝ) * kOff

/-- Unnormalized stationary weights, constructed from the birth/death ratio.
`stationaryWeight 0 = 1`; each successive weight is chosen to make neighboring
fluxes balance. -/
def stationaryWeight (T n : ℕ) (kAct kOff : ℝ) : ℕ → ℝ
  | 0 => 1
  | m + 1 =>
      stationaryWeight T n kAct kOff m * birthRate T n m kAct /
        deathRate (m + 1) kOff

/-- The recursively constructed weights satisfy exact local detailed balance. -/
theorem stationaryWeight_detailedBalance
    (T n m : ℕ) (kAct kOff : ℝ) (hkOff : kOff ≠ 0) :
    stationaryWeight T n kAct kOff m * birthRate T n m kAct =
      stationaryWeight T n kAct kOff (m + 1) * deathRate (m + 1) kOff := by
  have hm : ((m + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  have hd : deathRate (m + 1) kOff ≠ 0 := by
    unfold deathRate
    exact mul_ne_zero hm hkOff
  rw [stationaryWeight]
  exact (div_mul_cancel₀ _ hd).symm

/-- Pairwise detailed balance on both sides of an interior state implies zero net
stationary flux at that state.  This is the algebraic reason detailed balance is
stronger than ordinary stationarity. -/
theorem interior_stationary_of_detailedBalance
    (w b d : ℕ → ℝ) (m : ℕ)
    (hleft : w m * b m = w (m + 1) * d (m + 1))
    (hright : w (m + 1) * b (m + 1) = w (m + 2) * d (m + 2)) :
    w m * b m + w (m + 2) * d (m + 2) =
      w (m + 1) * (b (m + 1) + d (m + 1)) := by
  linarith

/-- Detailed balance also supplies the lower boundary equation. -/
theorem lowerBoundary_stationary_of_detailedBalance
    (w b d : ℕ → ℝ)
    (h : w 0 * b 0 = w 1 * d 1) :
    w 1 * d 1 = w 0 * b 0 := by
  exact h.symm

end StochasticQuantization
