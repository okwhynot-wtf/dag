import Certificate
import KernelAdmit
import Quintom.Kernel
import Quintom.FixedPoint
import Orbit
import Canon
import Geom.Registration

/-!
# Quintom dictionary entry — certificate filing (T-5, T-8)

RE / re-entrant engine: nonempty-locus mode of clause (c).
The physical divide `w = −1` is the distinguished fixed locus (touched at
crossings, approached under friction). Channel-label swap remains a strict
involution with empty combinatorial Fixed on `Channel`; the locus mode is
carried by `ReState` below and `fixedMode := nonempty`.

Dynamical (ODE) content lives under `exhibits/quintom/` and is not claimed
in this module.
-/

namespace Dictionary.Quintom.Certificate

open Bridge.KernelAdmit
open Dictionary.Certificate
open Dictionary.Quintom

/-- Observable on which swap acts as negation: the channel bit. -/
def involutionObservable (c : Kernel.Channel) : Bool :=
  Kernel.toBool c

theorem observable_swap_as_not (c : Kernel.Channel) :
    involutionObservable (Kernel.swap c) = !(involutionObservable c) :=
  Kernel.swap_as_not c

/-- Physical locus carrier for nonempty-mode clause (c). -/
inductive ReState where
  | divide    -- w = −1, fixed by the involution
  | bulkPhi
  | bulkSigma
  deriving DecidableEq, Repr

/-- Involution with nonempty fixed set `{divide}`. -/
def reSwap : ReState → ReState
  | ReState.divide => ReState.divide
  | ReState.bulkPhi => ReState.bulkSigma
  | ReState.bulkSigma => ReState.bulkPhi

theorem reSwap_involutive (s : ReState) : reSwap (reSwap s) = s := by
  cases s <;> rfl

theorem reSwap_fixes_divide : reSwap ReState.divide = ReState.divide := rfl

theorem reSwap_fixed_iff (s : ReState) :
    reSwap s = s ↔ s = ReState.divide := by
  cases s <;> constructor <;> intro h <;> first | rfl | cases h

/-- Bulk observable flips; divide is a null reading (locus). -/
def reObserve : ReState → Option Bool
  | ReState.divide => none
  | ReState.bulkPhi => some true
  | ReState.bulkSigma => some false

def reObsNeg : Option Bool → Option Bool
  | none => none
  | some b => some (!b)

/-- **Nonempty-locus certificate** on `ReState`: fixed set = `{divide}` ≅ w = −1. -/
def quintomCert : KernelCert ReState (Option Bool) where
  swap := reSwap
  square := id
  swap_sq := reSwap_involutive
  square_involutive := fun _ => rfl
  observe := reObserve
  obsNeg := reObsNeg
  swap_as_not := fun s => by cases s <;> rfl
  Fixed := fun s => s = ReState.divide
  fixed_iff := fun s => (reSwap_fixed_iff s).symm
  fixedMode := FixedMode.nonemptyLocus
  noSoloCross := fun _ h => h.2

/-- Single-field no-go: no live act on a subsingleton. -/
theorem single_field_nogo :
    ¬ ∃ act : Unit → Unit, Orbit.Live act := by
  intro ⟨act, hl⟩
  exact hl () (Subsingleton.elim (act ()) ())

/-- Channel-label certificate (strict involution; combinatorial Fixed empty). -/
def channelCert : KernelCert Kernel.Channel Bool where
  swap := Kernel.swap
  square := id
  swap_sq := Kernel.swap_involutive
  square_involutive := fun _ => rfl
  observe := involutionObservable
  obsNeg := not
  swap_as_not := observable_swap_as_not
  Fixed := fun c => Kernel.swap c = c
  fixed_iff := fun _ => Iff.rfl
  fixedMode := FixedMode.emptyLocus
  noSoloCross := fun c h => FixedPoint.swap_fixed_empty c h.1


theorem divide_in_fixed : quintomCert.Fixed ReState.divide := rfl

theorem nonempty_locus_witnessed :
    ∃ s, quintomCert.Fixed s :=
  ⟨ReState.divide, divide_in_fixed⟩

/-- **M3 filing.** Kernel sides of T-5 and T-8 plus I-4 certificates. -/
theorem quintom_filed :
    (∀ c, Kernel.swap (Kernel.swap c) = c) ∧
    (∀ c, Kernel.toBool (Kernel.swap c) = !(Kernel.toBool c)) ∧
    (Geom.Registration.Inj Kernel.frictionlessStep ∧
      ¬ Geom.Registration.Merges Kernel.frictionlessStep ∧
      ¬ Geom.Registration.Registers Kernel.frictionlessStep) ∧
    Canon.IsFundamental (not : Bool → Bool) ∧
    quintomCert.fixedMode = FixedMode.nonemptyLocus ∧
    (∃ s, quintomCert.Fixed s) ∧
    (¬ ∃ act : Unit → Unit, Orbit.Live act) :=
  ⟨Kernel.swap_involutive, Kernel.swap_as_not, Kernel.frictionless_silent,
   Canon.canon_is_fundamental, rfl, nonempty_locus_witnessed, single_field_nogo⟩

#print axioms quintom_filed
#print axioms single_field_nogo
#print axioms nonempty_locus_witnessed
#print axioms reSwap_fixed_iff

end Dictionary.Quintom.Certificate
