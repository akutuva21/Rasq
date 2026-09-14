import Mathlib
import StochasticQuantization.BirthDeath

noncomputable section

open scoped BigOperators

/-!
# Constructive Poisson solver for a finite birth/death chain

This file removes the main reason one might think the slow/fast theorem needs a
huge matrix inverse.

For a frozen SOS block, free RasGTP is a one-dimensional birth/death chain.  If
`z m` is a signed correction at state `m`, define the probability flux across the
edge `m <-> m+1` by

    J_m = birth_m * z_m - death_(m+1) * z_(m+1).

The forward-generator equation `A z = y` is then just a flux-difference equation:

    y_m = J_(m-1) - J_m.

Therefore the edge flux is determined by cumulative forcing:

    J_m = - sum_{i=0}^m y_i.

That gives a linear-time Poisson solve along the path.  No dense inverse is
needed.  The solution is unique only up to adding the stationary distribution;
`centered` removes that null-mode by forcing the correction to have total mass
zero.

For non-mathematicians: this is the exact algebraic reason the Ras certificate can
be small.  We solve along neighboring RasGTP counts rather than invert the whole
coupled Ras/SOS state space.
-/

namespace StochasticQuantization
namespace BirthDeathPoisson

/-- Cumulative forcing through state `m`. -/
def prefixSum (y : ℕ → ℝ) (m : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (m + 1), y i

@[simp] theorem prefixSum_zero (y : ℕ → ℝ) : prefixSum y 0 = y 0 := by
  simp [prefixSum]

/-- Adding one state adds exactly that state's forcing to the prefix sum. -/
theorem prefixSum_succ (y : ℕ → ℝ) (m : ℕ) :
    prefixSum y (m + 1) = prefixSum y m + y (m + 1) := by
  simp [prefixSum, Finset.sum_range_succ, Nat.add_assoc]

/-- Signed flux through the edge `m <-> m+1`. -/
def edgeFlux
    (birth death z : ℕ → ℝ) (m : ℕ) : ℝ :=
  birth m * z m - death (m + 1) * z (m + 1)

/-- Forward-generator expression at the lower boundary state 0. -/
def lowerForward
    (birth death z : ℕ → ℝ) : ℝ :=
  death 1 * z 1 - birth 0 * z 0

/-- Forward-generator expression at the interior state `m+1`. -/
def interiorForward
    (birth death z : ℕ → ℝ) (m : ℕ) : ℝ :=
  birth m * z m + death (m + 2) * z (m + 2) -
    (birth (m + 1) + death (m + 1)) * z (m + 1)

/-- Forward-generator expression at the upper boundary state `m+1`, where the
birth rate out of the finite state space is zero. -/
def upperForward
    (birth death z : ℕ → ℝ) (m : ℕ) : ℝ :=
  birth m * z m - death (m + 1) * z (m + 1)

/-- Interior generator action is exactly the difference of neighboring fluxes. -/
theorem interiorForward_eq_fluxDifference
    (birth death z : ℕ → ℝ) (m : ℕ) :
    interiorForward birth death z m =
      edgeFlux birth death z m - edgeFlux birth death z (m + 1) := by
  unfold interiorForward edgeFlux
  ring

/-- Lower-boundary generator action is minus the first edge flux. -/
theorem lowerForward_eq_neg_flux
    (birth death z : ℕ → ℝ) :
    lowerForward birth death z = -edgeFlux birth death z 0 := by
  unfold lowerForward edgeFlux
  ring

/-- The upper-boundary generator action is the final edge flux. -/
theorem upperForward_eq_flux
    (birth death z : ℕ → ℝ) (m : ℕ) :
    upperForward birth death z m = edgeFlux birth death z m := by
  rfl

/-- Raw O(F) Poisson recurrence.  We choose `z 0 = 0`; any other solution differs
by a stationary null-mode that can be removed afterwards. -/
def poissonRaw
    (birth death y : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | m + 1 =>
      (birth m * poissonRaw birth death y m + prefixSum y m) /
        death (m + 1)

/-- The raw recurrence produces exactly the required cumulative edge flux whenever
the downward rate on that edge is nonzero. -/
theorem poissonRaw_edgeFlux
    (birth death y : ℕ → ℝ) (m : ℕ)
    (hdeath : death (m + 1) ≠ 0) :
    edgeFlux birth death (poissonRaw birth death y) m = -prefixSum y m := by
  unfold edgeFlux
  simp only [poissonRaw]
  field_simp [hdeath]
  ring

/-- Hence the recurrence solves the generator equation at the lower boundary. -/
theorem poissonRaw_lower
    (birth death y : ℕ → ℝ)
    (hdeath : death 1 ≠ 0) :
    lowerForward birth death (poissonRaw birth death y) = y 0 := by
  rw [lowerForward_eq_neg_flux]
  rw [poissonRaw_edgeFlux birth death y 0 hdeath]
  simp [prefixSum]

/-- And it solves every interior generator equation. -/
theorem poissonRaw_interior
    (birth death y : ℕ → ℝ) (m : ℕ)
    (hdeath1 : death (m + 1) ≠ 0)
    (hdeath2 : death (m + 2) ≠ 0) :
    interiorForward birth death (poissonRaw birth death y) m = y (m + 1) := by
  rw [interiorForward_eq_fluxDifference]
  rw [poissonRaw_edgeFlux birth death y m hdeath1]
  rw [poissonRaw_edgeFlux birth death y (m + 1) hdeath2]
  rw [prefixSum_succ]
  ring

/-- At the upper boundary, zero total forcing supplies the final equation. -/
theorem poissonRaw_upper
    (birth death y : ℕ → ℝ) (m : ℕ)
    (hdeath : death (m + 1) ≠ 0)
    (htotal : prefixSum y (m + 1) = 0) :
    upperForward birth death (poissonRaw birth death y) m = y (m + 1) := by
  rw [upperForward_eq_flux]
  rw [poissonRaw_edgeFlux birth death y m hdeath]
  have hs := prefixSum_succ y m
  linarith

/-- Total signed mass over states `0,...,T`. -/
def totalOver (T : ℕ) (z : ℕ → ℝ) : ℝ :=
  ∑ i ∈ Finset.range (T + 1), z i

/-- Remove the stationary null-mode from a raw Poisson solution. -/
def centered
    (T : ℕ) (rho z : ℕ → ℝ) (m : ℕ) : ℝ :=
  z m - totalOver T z * rho m

/-- If `rho` has mass one, centering makes the correction have mass zero. -/
theorem totalOver_centered
    (T : ℕ) (rho z : ℕ → ℝ)
    (hrho : totalOver T rho = 1) :
    totalOver T (centered T rho z) = 0 := by
  have hsub (f g : ℕ → ℝ) :
      totalOver T (fun i => f i - g i) = totalOver T f - totalOver T g := by
    unfold totalOver
    rw [Finset.sum_sub_distrib]
  have hsmul (c : ℝ) (f : ℕ → ℝ) :
      totalOver T (fun i => c * f i) = c * totalOver T f := by
    unfold totalOver
    rw [Finset.mul_sum]
  calc
    totalOver T (centered T rho z) =
        totalOver T z - totalOver T (fun i => totalOver T z * rho i) := by
      change totalOver T (fun i => z i - totalOver T z * rho i) =
        totalOver T z - totalOver T (fun i => totalOver T z * rho i)
      exact hsub z (fun i => totalOver T z * rho i)
    _ = totalOver T z - totalOver T z * totalOver T rho := by
      rw [hsmul]
    _ = 0 := by rw [hrho]; ring

/-- Subtracting any stationary zero-flux shape does not change edge fluxes. -/
theorem edgeFlux_centered
    (T : ℕ) (birth death rho z : ℕ → ℝ) (m : ℕ)
    (hrhoFlux : edgeFlux birth death rho m = 0) :
    edgeFlux birth death (centered T rho z) m = edgeFlux birth death z m := by
  unfold centered
  calc
    edgeFlux birth death
        (fun k => z k - totalOver T z * rho k) m =
      edgeFlux birth death z m - totalOver T z * edgeFlux birth death rho m := by
        unfold edgeFlux
        ring
    _ = edgeFlux birth death z m := by rw [hrhoFlux]; ring



/-!
## Linearity of the path solver

The recurrence above is not just an algorithm; for fixed birth/death rates it is
a linear operation on the forcing vector.  Proving that explicitly lets the Ras
block solver be assembled into a single global linear operator later.
-/

@[simp] theorem prefixSum_add (y₁ y₂ : ℕ → ℝ) (m : ℕ) :
    prefixSum (fun i => y₁ i + y₂ i) m = prefixSum y₁ m + prefixSum y₂ m := by
  simp [prefixSum, Finset.sum_add_distrib]

@[simp] theorem prefixSum_smul (c : ℝ) (y : ℕ → ℝ) (m : ℕ) :
    prefixSum (fun i => c * y i) m = c * prefixSum y m := by
  simp [prefixSum, Finset.mul_sum]

/-- The raw O(F) Poisson recurrence is additive in its forcing. -/
theorem poissonRaw_add
    (birth death y₁ y₂ : ℕ → ℝ) : ∀ m : ℕ,
    poissonRaw birth death (fun i => y₁ i + y₂ i) m =
      poissonRaw birth death y₁ m + poissonRaw birth death y₂ m := by
  intro m
  induction m with
  | zero => simp [poissonRaw]
  | succ m ih =>
      simp only [poissonRaw, ih, prefixSum_add]
      ring

/-- The raw O(F) Poisson recurrence commutes with scalar multiplication. -/
theorem poissonRaw_smul
    (birth death y : ℕ → ℝ) (c : ℝ) : ∀ m : ℕ,
    poissonRaw birth death (fun i => c * y i) m =
      c * poissonRaw birth death y m := by
  intro m
  induction m with
  | zero => simp [poissonRaw]
  | succ m ih =>
      simp only [poissonRaw, ih, prefixSum_smul]
      ring

@[simp] theorem totalOver_add (T : ℕ) (z₁ z₂ : ℕ → ℝ) :
    totalOver T (fun i => z₁ i + z₂ i) = totalOver T z₁ + totalOver T z₂ := by
  simp [totalOver, Finset.sum_add_distrib]

@[simp] theorem totalOver_smul (T : ℕ) (c : ℝ) (z : ℕ → ℝ) :
    totalOver T (fun i => c * z i) = c * totalOver T z := by
  simp [totalOver, Finset.mul_sum]

/-- Centering around a fixed stationary shape is additive. -/
theorem centered_add
    (T : ℕ) (rho z₁ z₂ : ℕ → ℝ) (m : ℕ) :
    centered T rho (fun i => z₁ i + z₂ i) m =
      centered T rho z₁ m + centered T rho z₂ m := by
  simp [centered, totalOver_add]
  ring

/-- Centering around a fixed stationary shape commutes with scalar multiplication. -/
theorem centered_smul
    (T : ℕ) (rho z : ℕ → ℝ) (c : ℝ) (m : ℕ) :
    centered T rho (fun i => c * z i) m = c * centered T rho z m := by
  simp [centered, totalOver_smul]
  ring


/-- The lower-boundary forward generator is additive in the signed state. -/
theorem lowerForward_add
    (birth death z₁ z₂ : ℕ → ℝ) :
    lowerForward birth death (fun i => z₁ i + z₂ i) =
      lowerForward birth death z₁ + lowerForward birth death z₂ := by
  unfold lowerForward
  ring

/-- The lower-boundary forward generator commutes with scalar multiplication. -/
theorem lowerForward_smul
    (birth death z : ℕ → ℝ) (c : ℝ) :
    lowerForward birth death (fun i => c * z i) =
      c * lowerForward birth death z := by
  unfold lowerForward
  ring

/-- The interior forward generator is additive. -/
theorem interiorForward_add
    (birth death z₁ z₂ : ℕ → ℝ) (m : ℕ) :
    interiorForward birth death (fun i => z₁ i + z₂ i) m =
      interiorForward birth death z₁ m + interiorForward birth death z₂ m := by
  unfold interiorForward
  ring

/-- The interior forward generator commutes with scalar multiplication. -/
theorem interiorForward_smul
    (birth death z : ℕ → ℝ) (c : ℝ) (m : ℕ) :
    interiorForward birth death (fun i => c * z i) m =
      c * interiorForward birth death z m := by
  unfold interiorForward
  ring

/-- The upper-boundary forward generator is additive. -/
theorem upperForward_add
    (birth death z₁ z₂ : ℕ → ℝ) (m : ℕ) :
    upperForward birth death (fun i => z₁ i + z₂ i) m =
      upperForward birth death z₁ m + upperForward birth death z₂ m := by
  unfold upperForward
  ring

/-- The upper-boundary forward generator commutes with scalar multiplication. -/
theorem upperForward_smul
    (birth death z : ℕ → ℝ) (c : ℝ) (m : ℕ) :
    upperForward birth death (fun i => c * z i) m =
      c * upperForward birth death z m := by
  unfold upperForward
  ring

/-- A useful finite-path uniqueness lemma.  If every edge flux is zero, the
    downward rates are nonzero, and the first coordinate is zero, then every
    coordinate on the path is zero.  This is the elementary induction underlying
    uniqueness of a birth/death Poisson solve once its null mode is fixed. -/
theorem eq_zero_of_zero_flux_of_zero_first
    (birth death z : ℕ → ℝ) (T : ℕ)
    (hflux : ∀ m < T, edgeFlux birth death z m = 0)
    (hdeath : ∀ m < T, death (m + 1) ≠ 0)
    (hz0 : z 0 = 0) :
    ∀ m ≤ T, z m = 0 := by
  intro m hm
  induction m with
  | zero => exact hz0
  | succ m ih =>
      have hmT : m < T := by omega
      have hprev : z m = 0 := ih (by omega)
      have hf := hflux m hmT
      unfold edgeFlux at hf
      rw [hprev] at hf
      have hd := hdeath m hmT
      exact (mul_eq_zero.mp (by linarith : death (m + 1) * z (m + 1) = 0)).resolve_left hd

end BirthDeathPoisson
end StochasticQuantization
