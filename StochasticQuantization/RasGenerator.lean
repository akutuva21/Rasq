import Mathlib
import StochasticQuantization.Ras

/-!
# Six-reaction count semantics for the Ras/SOS model

The four Ras pools are free RasGDP, free RasGTP, GDP-Ras:SOS, and GTP-Ras:SOS.
The reversible binding rules are split into their forward and reverse directions,
leaving six one-way count transitions.  RasGTP deactivation acts only on *free*
RasGTP, matching the BNGL pattern with an unbound `sos` site.
-/

namespace StochasticQuantization
namespace Ras
namespace Generator

structure CountState where
  freeGDP : ℕ
  freeGTP : ℕ
  boundGDP : ℕ
  boundGTP : ℕ
  deriving Repr, DecidableEq

/-- Conservation law for a fixed total number of Ras molecules. -/
def Physical (R : ℕ) (s : CountState) : Prop :=
  s.freeGDP + s.freeGTP + s.boundGDP + s.boundGTP = R

/-- Total SOS-bound Ras molecules, hence the number of processive catalysts. -/
def boundTotal (s : CountState) : ℕ := s.boundGDP + s.boundGTP

/-- Processive activation of one free RasGDP molecule. -/
def activationRate (p : Params) (s : CountState) : ℝ :=
  (s.freeGDP : ℝ) * (boundTotal s : ℝ) * p.kcat1

/-- RasGAP deactivation of one free RasGTP molecule. -/
def deactivationRate (p : Params) (s : CountState) : ℝ :=
  (s.freeGTP : ℝ) * p.kcat2

/-- SOS binding to free RasGDP. -/
def bindGDPRate (p : Params) (s : CountState) : ℝ :=
  (s.freeGDP : ℝ) * p.konGDP

/-- SOS binding to free RasGTP. -/
def bindGTPRate (p : Params) (s : CountState) : ℝ :=
  (s.freeGTP : ℝ) * p.konGTP

/-- SOS unbinding from GDP-Ras:SOS. -/
def unbindGDPRate (p : Params) (s : CountState) : ℝ :=
  (s.boundGDP : ℝ) * p.koffGDP

/-- SOS unbinding from GTP-Ras:SOS. -/
def unbindGTPRate (p : Params) (s : CountState) : ℝ :=
  (s.boundGTP : ℝ) * p.koffGTP

/-- Fast (within-block) total exit rate. -/
def fastExitRate (p : Params) (s : CountState) : ℝ :=
  activationRate p s + deactivationRate p s

/-- Slow (SOS-block-changing) total exit rate. -/
def slowExitRate (p : Params) (s : CountState) : ℝ :=
  bindGDPRate p s + bindGTPRate p s + unbindGDPRate p s + unbindGTPRate p s

/-- Scaling all SOS association/dissociation rates scales the slow clock exactly. -/
theorem slowExitRate_speedBinding (c : ℝ) (p : Params) (s : CountState) :
    slowExitRate (speedBinding c p) s = c * slowExitRate p s := by
  unfold slowExitRate bindGDPRate bindGTPRate unbindGDPRate unbindGTPRate speedBinding
  ring

/-- The fast chemistry is unchanged by a pure SOS-clock rescaling. -/
theorem fastExitRate_speedBinding (c : ℝ) (p : Params) (s : CountState) :
    fastExitRate (speedBinding c p) s = fastExitRate p s := by
  rfl

end Generator
end Ras
end StochasticQuantization
