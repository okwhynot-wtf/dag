import TwoCycle
import Obs.Recovery
import TwoBounce

/-!
# T-7 One ℤ/2, three faces

Pole swap ≅ address reversal ≅ channel relabelling: a single
underdetermination with three named projections.

Channel *labels* stay conventional (canonicity fails). Channel *swap*
is proved content: exchanging the two factors of any two-bounce
presentation of `U` yields a presentation of `U⁻¹`
(`TwoBounce.channel_swap_is_reversal`).
-/

namespace Bridge.OneZ2

/-- The three named faces of the one ℤ/2 underdetermination. -/
inductive Face where
  | pole      -- DM: TwoCycle pole swap / two_readings
  | address   -- AG: Obs.Recovery.Address forward/reverse
  | channel   -- RE: φ ↔ σ (dictionary labels)
  deriving DecidableEq, Repr

/-- Address carriers are exactly two. -/
def AddressBit : Type := Bool

/-- Map AG address to the bit. -/
def addressBit : Obs.Recovery.Address → AddressBit
  | Obs.Recovery.Address.forward => true
  | Obs.Recovery.Address.reverse => false

/-- Map bit back to address. -/
def bitAddress : AddressBit → Obs.Recovery.Address
  | true => Obs.Recovery.Address.forward
  | false => Obs.Recovery.Address.reverse

theorem addressBit_roundtrip (a : Obs.Recovery.Address) :
    bitAddress (addressBit a) = a := by
  cases a <;> rfl

theorem bitAddress_roundtrip (b : AddressBit) :
    addressBit (bitAddress b) = b := by
  cases b <;> rfl

/-- Address space is ℤ/2 (two readings). -/
theorem address_two :
    (∃ a b : Obs.Recovery.Address, a ≠ b ∧
      ∀ x : Obs.Recovery.Address, x = a ∨ x = b) :=
  ⟨Obs.Recovery.Address.forward, Obs.Recovery.Address.reverse, by decide,
    fun x => by cases x <;> decide⟩

/-- Channel labels are ℤ/2 (φ / σ). -/
inductive Channel where
  | phi
  | sigma
  deriving DecidableEq, Repr

def channelBit : Channel → Bool
  | Channel.phi => true
  | Channel.sigma => false

def bitChannel : Bool → Channel
  | true => Channel.phi
  | false => Channel.sigma

theorem channelBit_roundtrip (c : Channel) :
    bitChannel (channelBit c) = c := by
  cases c <;> rfl

/-- Pole swap on Bool is negation (DM automorphism). -/
def poleSwap : Bool → Bool := not

theorem pole_swap_involution (b : Bool) : poleSwap (poleSwap b) = b := by
  cases b <;> rfl

/-- Address reversal as bit flip. -/
def addressSwap (a : Obs.Recovery.Address) : Obs.Recovery.Address :=
  bitAddress (!(addressBit a))

theorem address_swap_involution (a : Obs.Recovery.Address) :
    addressSwap (addressSwap a) = a := by
  cases a <;> rfl

/-- Channel relabelling as bit flip. -/
def channelSwap (c : Channel) : Channel :=
  bitChannel (!(channelBit c))

theorem channel_swap_involution (c : Channel) :
    channelSwap (channelSwap c) = c := by
  cases c <;> rfl

/-- Common ℤ/2 carrier for all three faces. -/
def Z2 : Type := Bool

/-- Project each face onto the common carrier. -/
def project : Face → Z2 → Z2
  | Face.pole, b => poleSwap b
  | Face.address, b => !b
  | Face.channel, b => !b

theorem project_involution (f : Face) (b : Z2) :
    project f (project f b) = b := by
  cases f <;> cases b <;> rfl

/-- DM supplies exactly two unpointed readings. -/
theorem dm_two_readings {α : Type} (act : α → α)
    (hs : Orbit.SymmetricStep act) (z : α)
    (e : Bool → α) (heq : ∀ b, e (!b) = act (e b))
    (hgen : TwoCycle.Generated act) :
    (∀ b, e b = TwoCycle.reading act z b) ∨
    (∀ b, e b = TwoCycle.reading act z (!b)) :=
  TwoCycle.two_readings act hs z e heq hgen

/-- **T-7.** One underdetermination, three named involutive projections. -/
theorem one_Z2_three_faces :
    (∀ f : Face, ∀ b : Z2, project f (project f b) = b) ∧
    (∃ a b : Obs.Recovery.Address, a ≠ b ∧
      ∀ x, x = a ∨ x = b) ∧
    (∀ c : Channel, channelSwap (channelSwap c) = c) ∧
    (∀ a : Obs.Recovery.Address, addressSwap (addressSwap a) = a) ∧
    (∀ b : Bool, poleSwap (poleSwap b) = b) :=
  ⟨project_involution, address_two, channel_swap_involution,
    address_swap_involution, pole_swap_involution⟩

/-- **T-7 channel column (proved).** Channel-swap of a two-bounce
    presentation covers step reversal — same involution on presentation
    space as reading the step backwards. Labels remain conventional. -/
theorem channel_swap_is_reversal {α : Type} (U : α → α)
    (f : Bridge.TwoBounce.TwoBounceFactor U) :
    (∀ x, Bridge.TwoBounce.reverseOf f (U x) = x) ∧
    (∀ x, U (Bridge.TwoBounce.reverseOf f x) = x) ∧
    Nonempty (Bridge.TwoBounce.TwoBounceFactor
      (Bridge.TwoBounce.reverseOf f)) :=
  Bridge.TwoBounce.channel_swap_is_reversal U f

#print axioms one_Z2_three_faces
#print axioms addressBit_roundtrip
#print axioms dm_two_readings
#print axioms channel_swap_is_reversal

end Bridge.OneZ2
