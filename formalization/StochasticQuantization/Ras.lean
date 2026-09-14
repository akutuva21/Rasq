import Mathlib
import StochasticQuantization.Core
import StochasticQuantization.Processivity

/-!
# Application to the Ras/SOS models in this repository

The full BNGL model is not identical to the minimal activator-target model.
The useful reduction is:

* catalyst count `n`  := number of Ras:SOS complexes (`totalBoundRas`);
* target              := the remaining free Ras molecules;
* target activation   := processive SOS-catalyzed GDP -> GTP, rate `n*Kcat1`;
* target deactivation := RasGAP-mediated GTP -> GDP, rate `Kcat2`.

Because each SOS complex sequesters one Ras molecule, the free target pool is
`RasTotal - n`, giving

    mu_n = (RasTotal-n) * n*Kcat1 / (n*Kcat1 + Kcat2).

This is exact for the *frozen-occupancy reduced model*.  It is an approximation to
the full BNGL trajectory whenever SOS occupancy changes on a comparable or faster
time scale than Ras relaxation.  That caveat is central, not cosmetic: Model 3 is
designed to violate the quasi-static assumption.
-/

namespace StochasticQuantization
namespace Ras

/-- Kinetic parameters needed to connect the formal reduction to a Ras BNGL model. -/
structure Params where
  rasTotal : ℝ
  kcat1 : ℝ
  kcat2 : ℝ
  konGDP : ℝ
  koffGDP : ℝ
  konGTP : ℝ
  koffGTP : ℝ
  deriving Repr

/-- Frozen-occupancy mean of *free* RasGTP in the reduced model. -/
def freePeak (p : Params) (n : ℕ) : ℝ :=
  (p.rasTotal - (n : ℝ)) * effectiveActivationRate n p.kcat1 /
    (effectiveActivationRate n p.kcat1 + p.kcat2)

/-- Conditional variance of the free target pool under the independent-target
birth/death reduction. -/
def freeVariance (p : Params) (n : ℕ) : ℝ :=
  let q := activationFraction n p.kcat1 p.kcat2
  (p.rasTotal - (n : ℝ)) * q * (1 - q)

/-- Nominal unsaturated quantum if we ignore both saturation and sequestration. -/
def linearPeak (p : Params) (n : ℕ) : ℝ :=
  (n : ℝ) * p.rasTotal * p.kcat1 / p.kcat2

/-- Exact error of the naive equally-spaced Ras approximation.

Two effects are bundled into this error:
* saturation: `n*kcat1/kcat2` is not tiny;
* sequestration: `n` Ras molecules are tied up in Ras:SOS complexes.
-/
theorem linearPeak_error_exact
    (p : Params) (n : ℕ)
    (hk2 : p.kcat2 ≠ 0)
    (hden : (n : ℝ) * p.kcat1 + p.kcat2 ≠ 0) :
    linearPeak p n - freePeak p n =
      p.kcat1 * ((n : ℝ) ^ 2) * (p.rasTotal * p.kcat1 + p.kcat2) /
        (p.kcat2 * ((n : ℝ) * p.kcat1 + p.kcat2)) := by
  simp [linearPeak, freePeak, effectiveActivationRate]
  field_simp [hk2, hden]
  ring

/-- Exact spacing between neighboring Ras peaks in the frozen-occupancy reduction.

Unlike the generic target model, Ras loses one free target for every bound SOS.
That creates an extra peak-crowding term. -/
theorem adjacentSpacing_exact
    (p : Params) (n : ℕ)
    (hk1 : 0 ≤ p.kcat1) (hk2 : 0 < p.kcat2) :
    freePeak p (n + 1) - freePeak p n =
      p.kcat1 *
          (p.kcat2 * (p.rasTotal - 2 * (n : ℝ) - 1) -
            p.kcat1 * (n : ℝ) * ((n : ℝ) + 1)) /
        (((n : ℝ) * p.kcat1 + p.kcat2) *
          (((n : ℝ) + 1) * p.kcat1 + p.kcat2)) := by
  have h0 : (n : ℝ) * p.kcat1 + p.kcat2 ≠ 0 := by positivity
  have h1 : ((n : ℝ) + 1) * p.kcat1 + p.kcat2 ≠ 0 := by positivity
  simp [freePeak, effectiveActivationRate, Nat.cast_add, Nat.cast_one]
  field_simp [h0, h1]
  ring

/-- A transparent sufficient condition for neighboring frozen Ras peaks to remain
ordered.  If this fails at high occupancy, peaks crowd and can eventually turn over. -/
theorem adjacentPeak_increases_of_condition
    (p : Params) (n : ℕ)
    (hk1 : 0 < p.kcat1) (hk2 : 0 < p.kcat2)
    (hcond :
      0 < p.kcat2 * (p.rasTotal - 2 * (n : ℝ) - 1) -
        p.kcat1 * (n : ℝ) * ((n : ℝ) + 1)) :
    freePeak p n < freePeak p (n + 1) := by
  have hspace := adjacentSpacing_exact p n (le_of_lt hk1) hk2
  have hden0 : 0 < (n : ℝ) * p.kcat1 + p.kcat2 := by positivity
  have hden1 : 0 < ((n : ℝ) + 1) * p.kcat1 + p.kcat2 := by positivity
  have hpos :
      0 < p.kcat1 *
          (p.kcat2 * (p.rasTotal - 2 * (n : ℝ) - 1) -
            p.kcat1 * (n : ℝ) * ((n : ℝ) + 1)) /
        (((n : ℝ) * p.kcat1 + p.kcat2) *
          (((n : ℝ) + 1) * p.kcat1 + p.kcat2)) := by
    positivity
  linarith

/-- The experimentally plotted `totalRasGTP` also counts bound GTP-Ras.
If exactly `n` Ras molecules are bound to SOS, the omitted bound-GTP contribution
can change the count by at most `n`.  This tiny bookkeeping bound explains why the
free-pool formula is still accurate at low occupancy. -/
theorem totalPeak_within_boundCorrection
    (freeTotal boundGTP : ℝ) (n : ℕ)
    (hlo : 0 ≤ boundGTP) (hhi : boundGTP ≤ (n : ℝ)) :
    freeTotal ≤ freeTotal + boundGTP ∧
      freeTotal + boundGTP ≤ freeTotal + (n : ℝ) := by
  constructor <;> linarith

/-- Apply a common speed-up to all SOS association/dissociation rates while keeping
Ras catalytic chemistry unchanged.  This abstracts the Model 1 -> Model 3 edit. -/
def speedBinding (scale : ℝ) (p : Params) : Params where
  rasTotal := p.rasTotal
  kcat1 := p.kcat1
  kcat2 := p.kcat2
  konGDP := scale * p.konGDP
  koffGDP := scale * p.koffGDP
  konGTP := scale * p.konGTP
  koffGTP := scale * p.koffGTP

/-- Accelerating only SOS binding kinetics leaves every frozen Ras peak exactly
unchanged.  It changes whether those peaks have time to form, not where the reduced
model says they would be. -/
theorem speedBinding_preserves_freePeak
    (scale : ℝ) (p : Params) (n : ℕ) :
    freePeak (speedBinding scale p) n = freePeak p n := by
  rfl

/-- Model 1 parameterization at a chosen pseudo-first-order SOS concentration.
The `kon` values here should already include `RhoSOS`, matching the BNGL file. -/
def model1 (rhoSOS : ℝ) : Params where
  rasTotal := 1000
  kcat1 := 1 / 100
  kcat2 := 1 / 400
  konGDP := (7 / 100000000) * rhoSOS
  koffGDP := 1 / 200
  konGTP := (7 / 100000000) * rhoSOS
  koffGTP := 1 / 2000

/-- Model 2 differs from Model 1 mainly by 10x faster RasGAP (`Kcat2`). -/
def model2 (rhoSOS : ℝ) : Params where
  rasTotal := 1000
  kcat1 := 1 / 100
  kcat2 := 1 / 40
  konGDP := (7 / 100000000) * rhoSOS
  koffGDP := 1 / 200
  konGTP := (7 / 100000000) * rhoSOS
  koffGTP := 1 / 2000

/-- Model 3 uses Model 1 Ras chemistry but 1000x faster SOS binding and unbinding. -/
def model3 (rhoSOS : ℝ) : Params := speedBinding 1000 (model1 rhoSOS)

/-- Formal statement of the intended Model 1 -> Model 3 intervention. -/
theorem model3_is_1000x_binding_speedup (rhoSOS : ℝ) :
    model3 rhoSOS = speedBinding 1000 (model1 rhoSOS) := by
  rfl

/-- Therefore Model 1 and Model 3 have exactly the same frozen-occupancy peak
geometry for every occupancy `n`. -/
theorem model1_model3_same_frozenPeaks (rhoSOS : ℝ) (n : ℕ) :
    freePeak (model3 rhoSOS) n = freePeak (model1 rhoSOS) n := by
  rfl


/-- The common 1000x speed-up preserves the GDP-state SOS binding ratio. -/
theorem model1_model3_same_bindingRatio_GDP (rhoSOS : ℝ) :
    bindingRatio (model3 rhoSOS).konGDP (model3 rhoSOS).koffGDP =
      bindingRatio (model1 rhoSOS).konGDP (model1 rhoSOS).koffGDP := by
  change bindingRatio (1000 * (model1 rhoSOS).konGDP)
      (1000 * (model1 rhoSOS).koffGDP) =
    bindingRatio (model1 rhoSOS).konGDP (model1 rhoSOS).koffGDP
  apply commonScaling_preserves_bindingRatio
  · norm_num
  · norm_num [model1]

/-- The same is true for the GTP-state SOS binding ratio. -/
theorem model1_model3_same_bindingRatio_GTP (rhoSOS : ℝ) :
    bindingRatio (model3 rhoSOS).konGTP (model3 rhoSOS).koffGTP =
      bindingRatio (model1 rhoSOS).konGTP (model1 rhoSOS).koffGTP := by
  change bindingRatio (1000 * (model1 rhoSOS).konGTP)
      (1000 * (model1 rhoSOS).koffGTP) =
    bindingRatio (model1 rhoSOS).konGTP (model1 rhoSOS).koffGTP
  apply commonScaling_preserves_bindingRatio
  · norm_num
  · norm_num [model1]

/-- Model 3 shortens the GDP-bound SOS dwell time by exactly 1000x. -/
theorem model3_GDP_dwell_1000x_shorter (rhoSOS : ℝ) :
    dwellTime (model3 rhoSOS).koffGDP =
      dwellTime (model1 rhoSOS).koffGDP / 1000 := by
  norm_num [model3, speedBinding, model1, dwellTime]

/-- Model 3 shortens the GTP-bound SOS dwell time by exactly 1000x. -/
theorem model3_GTP_dwell_1000x_shorter (rhoSOS : ℝ) :
    dwellTime (model3 rhoSOS).koffGTP =
      dwellTime (model1 rhoSOS).koffGTP / 1000 := by
  norm_num [model3, speedBinding, model1, dwellTime]

/-- Model 1, n=1: the frozen free-RasGTP peak is 799.2 molecules. -/
example (rhoSOS : ℝ) : freePeak (model1 rhoSOS) 1 = 3996 / 5 := by
  norm_num [freePeak, model1, effectiveActivationRate]

/-- Model 2, n=1: faster RasGAP pulls the first nonzero peak down to ~285.43. -/
example (rhoSOS : ℝ) : freePeak (model2 rhoSOS) 1 = 19980 / 70 := by
  norm_num [freePeak, model2, effectiveActivationRate]

/-- Model 1 has ~25 target relaxation rates per GTP-bound SOS unbinding rate at n=1. -/
example : persistenceRatio 1 (1 / 100 : ℝ) (1 / 400) (1 / 2000) = 25 := by
  norm_num [persistenceRatio, relaxationRate, effectiveActivationRate]

/-- Model 2 has ~70 such relaxation rates because RasGAP is faster. -/
example : persistenceRatio 1 (1 / 100 : ℝ) (1 / 40) (1 / 2000) = 70 := by
  norm_num [persistenceRatio, relaxationRate, effectiveActivationRate]

/-- Model 3 collapses the same ratio to 0.025 = 1/40, breaking quasi-static tracking. -/
example : persistenceRatio 1 (1 / 100 : ℝ) (1 / 400) (1 / 2) = 1 / 40 := by
  norm_num [persistenceRatio, relaxationRate, effectiveActivationRate]

end Ras
end StochasticQuantization
