import Mathlib

noncomputable section

/-!
# Mesoscopic scaling of quantized biochemical levels

A convenient dimensionless measure of neighboring-level resolvability is the
squared separation divided by conditional variance.  If the per-catalyst level
spacing stays O(1) while conditional variance grows linearly with system area,
this resolution falls exactly like `1 / area`.

The file states finite threshold theorems rather than relying only on asymptotic
notation.  Together with a minimum-target requirement, they define a genuine
mesoscopic size window.
-/

namespace StochasticQuantization
namespace Theory
namespace Mesoscopic

/-- Squared standardized separation when conditional variance is `area * varDensity`. -/
def resolutionSq (area spacing varDensity : ℝ) : ℝ :=
  spacing ^ 2 / (area * varDensity)

/-- Target count under fixed surface density. -/
def targetCount (area targetDensity : ℝ) : ℝ := area * targetDensity

/-- Exact inverse-area scaling under a common area multiplier. -/
theorem resolutionSq_scale
    (area spacing varDensity scale : ℝ)
    (harea : area ≠ 0) (hvar : varDensity ≠ 0) (hscale : scale ≠ 0) :
    resolutionSq (scale * area) spacing varDensity =
      resolutionSq area spacing varDensity / scale := by
  unfold resolutionSq
  field_simp [harea, hvar, hscale]

/-- Above this finite size, squared resolution is at most `κ`. -/
theorem resolutionSq_le_of_large_area
    (area spacing varDensity κ : ℝ)
    (harea : 0 < area) (hvar : 0 < varDensity) (hκ : 0 < κ)
    (hlarge : spacing ^ 2 / (κ * varDensity) ≤ area) :
    resolutionSq area spacing varDensity ≤ κ := by
  unfold resolutionSq
  have hden : 0 < area * varDensity := mul_pos harea hvar
  rw [div_le_iff₀ hden]
  have hkv : 0 < κ * varDensity := mul_pos hκ hvar
  have hcross := (div_le_iff₀ hkv).mp hlarge
  nlinarith

/-- Below the corresponding finite size, squared resolution is at least `κ`. -/
theorem resolutionSq_ge_of_small_area
    (area spacing varDensity κ : ℝ)
    (harea : 0 < area) (hvar : 0 < varDensity) (hκ : 0 < κ)
    (hsmall : area ≤ spacing ^ 2 / (κ * varDensity)) :
    κ ≤ resolutionSq area spacing varDensity := by
  unfold resolutionSq
  have hden : 0 < area * varDensity := mul_pos harea hvar
  rw [le_div_iff₀ hden]
  have hkv : 0 < κ * varDensity := mul_pos hκ hvar
  have hcross := (le_div_iff₀ hkv).mp hsmall
  nlinarith

/-- A minimum target-pool requirement induces a lower size threshold. -/
theorem targetCount_ge_min
    (area targetDensity minTargets : ℝ)
    (hdensity : 0 < targetDensity)
    (harea : minTargets / targetDensity ≤ area) :
    minTargets ≤ targetCount area targetDensity := by
  unfold targetCount
  have h := (div_le_iff₀ hdensity).mp harea
  nlinarith

/-- Lower edge of the mesoscopic window from target amplification. -/
def lowerArea (minTargets targetDensity : ℝ) : ℝ :=
  minTargets / targetDensity

/-- Upper edge of the mesoscopic window from state resolvability. -/
def upperArea (spacing varDensity κ : ℝ) : ℝ :=
  spacing ^ 2 / (κ * varDensity)

/-- A system size lies in the mesoscopic window when it is large enough to
supply the required target amplification but small enough to preserve the
requested state resolution. -/
def InWindow
    (area minTargets targetDensity spacing varDensity κ : ℝ) : Prop :=
  lowerArea minTargets targetDensity ≤ area ∧
    area ≤ upperArea spacing varDensity κ

/-- **Mesoscopic window theorem.**  Every positive area inside the window has
both enough targets and at least the requested squared resolution. -/
theorem inWindow_gives_amplification_and_resolution
    (area minTargets targetDensity spacing varDensity κ : ℝ)
    (harea : 0 < area) (hdensity : 0 < targetDensity)
    (hvar : 0 < varDensity) (hκ : 0 < κ)
    (hwindow : InWindow area minTargets targetDensity spacing varDensity κ) :
    minTargets ≤ targetCount area targetDensity ∧
      κ ≤ resolutionSq area spacing varDensity := by
  rcases hwindow with ⟨hlow, hupp⟩
  constructor
  · exact targetCount_ge_min area targetDensity minTargets hdensity hlow
  · exact resolutionSq_ge_of_small_area area spacing varDensity κ
      harea hvar hκ hupp

/-- There is a nonempty size window exactly when the amplification lower edge is
below the resolution upper edge. -/
def WindowNonempty
    (minTargets targetDensity spacing varDensity κ : ℝ) : Prop :=
  lowerArea minTargets targetDensity ≤ upperArea spacing varDensity κ



/-- The interval definition really is a nonempty-window criterion: a mesoscopic
area exists exactly when its amplification lower edge does not exceed its
resolution upper edge. -/
theorem windowNonempty_iff_exists
    (minTargets targetDensity spacing varDensity κ : ℝ) :
    WindowNonempty minTargets targetDensity spacing varDensity κ ↔
      ∃ area, InWindow area minTargets targetDensity spacing varDensity κ := by
  constructor
  · intro h
    refine ⟨lowerArea minTargets targetDensity, le_rfl, ?_⟩
    exact h
  · rintro ⟨area, hlow, hupp⟩
    exact hlow.trans hupp

end Mesoscopic
end Theory
end StochasticQuantization
