import TwoCycle
import Orbit
import Canon
import Geom.Registration
import Certificate

/-!
# T-5 Oscillator triangle — RE kernel side

Frictionless limit (H = 0): two-channel labelling with swap involution,
empty/silent record, fundamental on the two-channel reading.
ODE envelope constancy is outside this module (`exhibits/quintom/`).
-/

namespace Dictionary.Quintom.Kernel

/-- Channel labels φ / σ. -/
inductive Channel where
  | phi
  | sigma
  deriving DecidableEq, Repr

/-- Swap involution on channels (image of the act under the certificate). -/
def swap : Channel → Channel
  | Channel.phi => Channel.sigma
  | Channel.sigma => Channel.phi

theorem swap_involutive (c : Channel) : swap (swap c) = c := by
  cases c <;> rfl

/-- Two-channel carrier ≃ Bool. -/
def toBool : Channel → Bool
  | Channel.phi => true
  | Channel.sigma => false

def ofBool : Bool → Channel
  | true => Channel.phi
  | false => Channel.sigma

theorem toBool_ofBool (b : Bool) : toBool (ofBool b) = b := by
  cases b <;> rfl

theorem ofBool_toBool (c : Channel) : ofBool (toBool c) = c := by
  cases c <;> rfl

theorem swap_as_not (c : Channel) : toBool (swap c) = !(toBool c) := by
  cases c <;> rfl

/-- Frictionless record: silent (no merge, no register) — AG oscillator. -/
def frictionlessStep : Bool × Unit → Bool × Unit :=
  Geom.Registration.oscStep

theorem frictionless_silent :
    Geom.Registration.Inj frictionlessStep ∧
    ¬ Geom.Registration.Merges frictionlessStep ∧
    ¬ Geom.Registration.Registers frictionlessStep :=
  Geom.Registration.osc_never_registers

/-- Act on channels via Bool negation transport. -/
def channelAct (c : Channel) : Channel := ofBool (!(toBool c))

theorem channelAct_eq_swap (c : Channel) : channelAct c = swap c := by
  cases c <;> rfl

theorem channelAct_fundamental_reading :
    (∀ c, channelAct (channelAct c) = c) ∧
    (∀ c, channelAct c ≠ c) := by
  refine ⟨fun c => by cases c <;> rfl, fun c h => ?_⟩
  cases c <;> cases h

/-- **T-5 kernel.** Oscillator triangle:
    swap involution + silent archive + two-channel fundamental reading. -/
theorem oscillator_triangle :
    (∀ c, swap (swap c) = c) ∧
    (∀ c, toBool (swap c) = !(toBool c)) ∧
    (Geom.Registration.Inj frictionlessStep ∧
      ¬ Geom.Registration.Merges frictionlessStep ∧
      ¬ Geom.Registration.Registers frictionlessStep) ∧
    Canon.IsFundamental (not : Bool → Bool) :=
  ⟨swap_involutive, swap_as_not, frictionless_silent,
   Canon.canon_is_fundamental⟩

#print axioms oscillator_triangle
#print axioms frictionless_silent
#print axioms swap_as_not

end Dictionary.Quintom.Kernel
