import Mathlib
import StochasticQuantization.Core

/-!
# Processivity and time-scale separation

The Ras Model 1 -> Model 3 intervention multiplies both SOS association and
SOS dissociation rates by 1000 while leaving catalytic Ras activation and RasGAP
turnover unchanged.

Common scaling has three mathematically distinct effects:

1. `kon/koff` is unchanged: an equilibrium binding ratio is preserved.
2. `1/koff` shrinks by the scale factor: each binding event is shorter lived.
3. `kcat/koff` shrinks by the same factor: fewer catalytic events fit inside one
   residence time, i.e. lower processivity.

This file proves those statements in a model-independent way.
-/

namespace StochasticQuantization

/-- Equilibrium association-to-dissociation ratio.  This is proportional to binding
occupancy in a simple pseudo-first-order binding step. -/
def bindingRatio (kon koff : ℝ) : ℝ := kon / koff

/-- Mean residence time of an exponential unbinding event. -/
def dwellTime (koff : ℝ) : ℝ := 1 / koff

/-- Kinetic persistence factor `kcat/koff`.  For a bimolecular catalytic step this
is *not by itself* dimensionless processivity; multiply by an available substrate
count/concentration to obtain catalytic opportunities per residence time. -/
def kineticPersistenceFactor (kcat koff : ℝ) : ℝ := kcat / koff

/-- Expected catalytic opportunities during one catalyst residence time if the
available substrate level is approximately constant.  This is the dimensionless
quantity closest to the biological idea of processivity in the reduced model. -/
def processivityAtSubstrate (substrate kcat koff : ℝ) : ℝ :=
  substrate * kcat / koff

/-- Number of target-relaxation rates per unbinding rate.
Large values mean the target has time to approach its frozen-occupancy state before
that catalyst leaves; small values mean occupancy changes too quickly. -/
def persistenceRatio (n : ℕ) (kAct kTargetOff kCatalystOff : ℝ) : ℝ :=
  relaxationRate n kAct kTargetOff / kCatalystOff

/-- Scaling `kon` and `koff` by the same nonzero factor preserves `kon/koff`. -/
theorem commonScaling_preserves_bindingRatio
    (scale kon koff : ℝ) (hscale : scale ≠ 0) (hkoff : koff ≠ 0) :
    bindingRatio (scale * kon) (scale * koff) = bindingRatio kon koff := by
  unfold bindingRatio
  field_simp [hscale, hkoff]
  ring

/-- Common kinetic acceleration shortens dwell time by exactly the scale factor. -/
theorem commonScaling_shortens_dwellTime
    (scale koff : ℝ) (hscale : scale ≠ 0) (hkoff : koff ≠ 0) :
    dwellTime (scale * koff) = dwellTime koff / scale := by
  unfold dwellTime
  field_simp [hscale, hkoff]
  ring

/-- If catalysis itself is not scaled, common binding/unbinding acceleration reduces
`kcat/koff` by exactly the same factor. -/
theorem commonScaling_reduces_kineticPersistence
    (scale kcat koff : ℝ) (hscale : scale ≠ 0) (hkoff : koff ≠ 0) :
    kineticPersistenceFactor kcat (scale * koff) =
      kineticPersistenceFactor kcat koff / scale := by
  unfold kineticPersistenceFactor
  field_simp [hscale, hkoff]
  ring

/-- The substrate-aware processivity number is also reduced by the same factor if
substrate abundance and catalysis are held fixed. -/
theorem commonScaling_reduces_processivityAtSubstrate
    (scale substrate kcat koff : ℝ) (hscale : scale ≠ 0) (hkoff : koff ≠ 0) :
    processivityAtSubstrate substrate kcat (scale * koff) =
      processivityAtSubstrate substrate kcat koff / scale := by
  unfold processivityAtSubstrate
  field_simp [hscale, hkoff]
  ring


end StochasticQuantization
