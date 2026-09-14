import Mathlib
import StochasticQuantization.RasGenerator

/-!
# Forward slow generator for the four-pool Ras/SOS count model

`RasGenerator.lean` states the six BNGL reactions and their propensities from the
usual "start in this state, where can I jump?" point of view.  A stationary
probability calculation uses the transpose point of view: for one destination
state, add probability arriving from its neighboring source states and subtract
probability leaving the destination.

This file writes that slow (SOS binding/unbinding) forward operator explicitly in
three independent count coordinates:

* `g` = GDP-Ras:SOS,
* `t` = GTP-Ras:SOS,
* `m` = free RasGTP.

The remaining count, free RasGDP, is fixed by conservation:

    freeGDP = R - g - t - m.

Only physical states with `g+t+m <= R` are used.  The formula below is exactly the
four SOS-changing one-way reactions in the BNGL model.  It is deliberately kept
separate from the fast birth/death operator so the slow/fast split is visible to
a biological reader.
-/

namespace StochasticQuantization
namespace Ras
namespace SlowForward

/-- A raw signed array indexed by the three independent Ras counts. -/
abbrev RawDistribution := ℕ → ℕ → ℕ → ℝ

/-- Read a state only if it is physically compatible with conserved Ras total
`R`.  Impossible states contribute zero probability. -/
def physicalAt (R : ℕ) (x : RawDistribution) (g t m : ℕ) : ℝ :=
  if g + t + m ≤ R then x g t m else 0

/-- Number of free GDP-Ras molecules at a physical destination coordinate. -/
def freeGDP (R g t m : ℕ) : ℕ := R - (g + t + m)

/-- **Exact slow forward generator.**

The four positive terms are probability arriving by GDP binding, GTP binding,
GDP unbinding, and GTP unbinding.  The final term is probability leaving by any
of those four reactions.

The index shifts are worth reading biologically:

* GDP binding: `(g-1,t,m) -> (g,t,m)`;
* GTP binding: `(g,t-1,m+1) -> (g,t,m)`;
* GDP unbinding: `(g+1,t,m) -> (g,t,m)`;
* GTP unbinding: `(g,t+1,m-1) -> (g,t,m)`.
-/
def apply
    (p : Params) (R : ℕ) (x : RawDistribution) (g t m : ℕ) : ℝ :=
  let incomingBindGDP :=
    if hg : 0 < g then
      physicalAt R x (g - 1) t m * ((freeGDP R g t m + 1 : ℕ) : ℝ) * p.konGDP
    else 0
  let incomingBindGTP :=
    if ht : 0 < t then
      physicalAt R x g (t - 1) (m + 1) * ((m + 1 : ℕ) : ℝ) * p.konGTP
    else 0
  let incomingUnbindGDP :=
    physicalAt R x (g + 1) t m * ((g + 1 : ℕ) : ℝ) * p.koffGDP
  let incomingUnbindGTP :=
    if hm : 0 < m then
      physicalAt R x g (t + 1) (m - 1) * ((t + 1 : ℕ) : ℝ) * p.koffGTP
    else 0
  let here := physicalAt R x g t m
  let outgoing :=
    ((freeGDP R g t m : ℕ) : ℝ) * p.konGDP +
    (m : ℝ) * p.konGTP +
    (g : ℝ) * p.koffGDP +
    (t : ℝ) * p.koffGTP
  incomingBindGDP + incomingBindGTP + incomingUnbindGDP + incomingUnbindGTP -
    outgoing * here

/-- Reading physical coordinates is additive in the signed distribution. -/
theorem physicalAt_add
    (R g t m : ℕ) (x y : RawDistribution) :
    physicalAt R (fun a b c => x a b c + y a b c) g t m =
      physicalAt R x g t m + physicalAt R y g t m := by
  unfold physicalAt
  split_ifs <;> simp

/-- Reading physical coordinates commutes with scalar multiplication. -/
theorem physicalAt_smul
    (R g t m : ℕ) (c : ℝ) (x : RawDistribution) :
    physicalAt R (fun a b d => c * x a b d) g t m =
      c * physicalAt R x g t m := by
  unfold physicalAt
  split_ifs <;> simp

/-- The exact slow forward generator is additive. -/
theorem apply_add
    (p : Params) (R g t m : ℕ) (x y : RawDistribution) :
    apply p R (fun a b c => x a b c + y a b c) g t m =
      apply p R x g t m + apply p R y g t m := by
  unfold apply
  simp only [physicalAt_add]
  split_ifs <;> ring

/-- The exact slow forward generator commutes with scalar multiplication. -/
theorem apply_smul
    (p : Params) (R g t m : ℕ) (c : ℝ) (x : RawDistribution) :
    apply p R (fun a b d => c * x a b d) g t m =
      c * apply p R x g t m := by
  unfold apply
  simp only [physicalAt_smul]
  split_ifs <;> ring

/-- `epsilon` scales the entire SOS clock and leaves the formula otherwise
unchanged.  This is the forward-distribution counterpart of the observable-side
`fullGeneratorOn = fast + epsilon*slow` decomposition in `RasGenerator.lean`. -/
def scaledApply
    (p : Params) (epsilon : ℝ) (R : ℕ) (x : RawDistribution) (g t m : ℕ) : ℝ :=
  epsilon * apply p R x g t m

@[simp] theorem scaledApply_one
    (p : Params) (R : ℕ) (x : RawDistribution) (g t m : ℕ) :
    scaledApply p 1 R x g t m = apply p R x g t m := by
  simp [scaledApply]

end SlowForward
end Ras
end StochasticQuantization
