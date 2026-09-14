import Mathlib

/-!
# Deterministic steady-state uniqueness for the four-state Ras/SOS reduction

This file addresses a different question from stochastic quantization:

> Could the observed digital/multimodal Ras output actually be ordinary deterministic
> bistability hidden underneath stochastic simulations?

For the four-rule BNGL model, write the positive steady-state concentrations/counts as

* `G`  = free RasGDP
* `P`  = free RasGTP
* `CG` = RasGDP:SOS
* `CP` = RasGTP:SOS

At steady state the binding reactions imply

    CG = alpha * G,       alpha = Kon_GDP / Koff_GDP
    CP = beta  * P,       beta  = Kon_GTP / Koff_GTP.

Let `x = P/G > 0`.  Ras conservation and catalytic balance reduce the entire positive
steady-state problem to one quadratic equation

    A*x^2 + B*x - C = 0

with

    A = Kcat2 * (1 + beta)                       > 0
    B = Kcat2 * (1 + alpha) - Kcat1*RasTotal*beta   (any sign)
    C = Kcat1 * RasTotal * alpha                 > 0.

A quadratic with positive leading coefficient and *negative constant term* has at
most one positive root.  The theorem below proves that fact without using the
quadratic formula.  Therefore the reduced deterministic Ras system cannot have two
positive steady states in one Ras-total class; its digital stochastic output does
not require deterministic bistability.

This is a model-specific algebraic theorem about the Ras equations.
-/

namespace StochasticQuantization
namespace Ras

/-- Generic algebraic lemma used by the Ras steady-state reduction. -/
theorem quadratic_atMostOnePositiveRoot
    (A B C x y : ℝ)
    (hA : 0 < A) (hC : 0 < C)
    (hx : 0 < x) (hy : 0 < y)
    (hqx : A * x^2 + B * x - C = 0)
    (hqy : A * y^2 + B * y - C = 0) :
    x = y := by
  have hAxB : 0 < A * x + B := by
    by_contra h
    have hnonpos : A * x + B ≤ 0 := le_of_not_gt h
    have : x * (A * x + B) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (le_of_lt hx) hnonpos
    nlinarith
  have hfactorPos : 0 < A * (x + y) + B := by
    nlinarith
  have hfactor : (x - y) * (A * (x + y) + B) = 0 := by
    nlinarith [hqx, hqy]
  rcases mul_eq_zero.mp hfactor with hxy | hbad
  · linarith
  · exfalso
    nlinarith

/-- Association equilibrium ratio for one Ras nucleotide state. -/
def associationRatio (kon koff : ℝ) : ℝ := kon / koff

/-- Coefficient of `x^2` in the reduced Ras equilibrium equation. -/
def eqA (kcat2 beta : ℝ) : ℝ := kcat2 * (1 + beta)

/-- Coefficient of `x` in the reduced Ras equilibrium equation. -/
def eqB (kcat1 kcat2 rasTotal alpha beta : ℝ) : ℝ :=
  kcat2 * (1 + alpha) - kcat1 * rasTotal * beta

/-- Positive quantity appearing with a minus sign as the constant term. -/
def eqC (kcat1 rasTotal alpha : ℝ) : ℝ := kcat1 * rasTotal * alpha

/-- Reduced scalar steady-state equation for the positive ratio `x = freeRasGTP/freeRasGDP`. -/
def ratioEquilibriumEquation
    (kcat1 kcat2 rasTotal alpha beta x : ℝ) : Prop :=
  eqA kcat2 beta * x^2 + eqB kcat1 kcat2 rasTotal alpha beta * x -
    eqC kcat1 rasTotal alpha = 0


/-- The denominator-cleared version of the positive ratio equation.

This is useful because it can be derived directly from conservation and catalytic
balance without dividing by `G`.  When `G > 0`, dividing this identity by `G^2`
gives the scalar equation in `x = P/G` used above. -/
def clearedRatioEquation
    (kcat1 kcat2 rasTotal alpha beta G P : ℝ) : Prop :=
  eqA kcat2 beta * P^2 +
      eqB kcat1 kcat2 rasTotal alpha beta * P * G -
      eqC kcat1 rasTotal alpha * G^2 = 0

/-- Direct algebraic bridge from the reduced Ras steady-state relations to the
cleared scalar equation.

Biological reading:
* `G` is free RasGDP and `P` is free RasGTP;
* `alpha` and `beta` are the GDP- and GTP-state SOS association/dissociation ratios;
* conservation says every Ras molecule is free GDP, free GTP, GDP:SOS, or GTP:SOS;
* catalytic balance says processive SOS activation of free GDP equals RasGAP
  deactivation of free GTP at steady state.

The binding-equilibrium substitutions `CG = alpha*G` and `CP = beta*P` have already
been made before these two equations are written. -/
theorem steadyStateRelations_imply_clearedRatioEquation
    (kcat1 kcat2 rasTotal alpha beta G P : ℝ)
    (hconservation :
      rasTotal = (1 + alpha) * G + (1 + beta) * P)
    (hcatalytic :
      kcat1 * G * (alpha * G + beta * P) = kcat2 * P) :
    clearedRatioEquation kcat1 kcat2 rasTotal alpha beta G P := by
  unfold clearedRatioEquation eqA eqB eqC
  rw [hconservation]
  have hzero : kcat1 * G * (alpha * G + beta * P) - kcat2 * P = 0 := by
    exact sub_eq_zero.mpr hcatalytic
  calc
    kcat2 * (1 + beta) * P ^ 2 +
          (kcat2 * (1 + alpha) -
              kcat1 * ((1 + alpha) * G + (1 + beta) * P) * beta) * P * G -
          kcat1 * ((1 + alpha) * G + (1 + beta) * P) * alpha * G ^ 2 =
        -((1 + alpha) * G + (1 + beta) * P) *
          (kcat1 * G * (alpha * G + beta * P) - kcat2 * P) := by
      ring
    _ = 0 := by rw [hzero]; ring

/-- For positive physical parameters, the reduced Ras equilibrium equation has at
most one positive solution. -/
theorem ratioEquilibrium_atMostOnePositive
    (kcat1 kcat2 rasTotal alpha beta x y : ℝ)
    (hk1 : 0 < kcat1) (hk2 : 0 < kcat2)
    (hR : 0 < rasTotal) (ha : 0 < alpha) (hb : 0 ≤ beta)
    (hx : 0 < x) (hy : 0 < y)
    (hex : ratioEquilibriumEquation kcat1 kcat2 rasTotal alpha beta x)
    (hey : ratioEquilibriumEquation kcat1 kcat2 rasTotal alpha beta y) :
    x = y := by
  apply quadratic_atMostOnePositiveRoot
      (eqA kcat2 beta)
      (eqB kcat1 kcat2 rasTotal alpha beta)
      (eqC kcat1 rasTotal alpha)
      x y
  · unfold eqA
    positivity
  · unfold eqC
    positivity
  · exact hx
  · exact hy
  · exact hex
  · exact hey

end Ras
end StochasticQuantization
