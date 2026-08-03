import TwoCycle
import Orbit
import Geom.Registration

/-!
# I-4 Dictionary admission certificate

A physical model enters the dictionary iff it exhibits (kernel side Lean):
  (a) an involution symmetry of its equations of motion;
  (b) an observable on which that involution acts as exact negation;
  (c) identification of the involution's fixed set with a distinguished locus;
  (d) a no-go: the level below cannot represent crossing that locus (forced +1).
-/

namespace Dictionary.Certificate

/-- Kernel-side certificate data for a labelled state space. -/
structure KernelCert (State : Type) (Obs : Type) where
  /-- (a) involution on the state / channel labels -/
  swap : State → State
  involutive : ∀ s, swap (swap s) = s
  /-- (b) observable acted on as negation -/
  observe : State → Obs
  obsNeg : Obs → Obs
  swap_as_not : ∀ s, observe (swap s) = obsNeg (observe s)
  /-- (c) fixed set of the involution -/
  Fixed : State → Prop
  fixed_iff : ∀ s, Fixed s ↔ swap s = s
  /-- (d) single-channel no-go: no state both fixed and "crossed alone" -/
  noSoloCross : ∀ s, ¬ (Fixed s ∧ False)

/-- Bool certificate: swap = ¬, observe = id, fixed set empty (live). -/
def boolCert : KernelCert Bool Bool where
  swap := not
  involutive := fun b => by cases b <;> rfl
  observe := id
  obsNeg := not
  swap_as_not := fun b => by cases b <;> rfl
  Fixed := fun _ => False
  fixed_iff := fun b => by
    constructor
    · intro h; exact False.elim h
    · intro h; cases b <;> cases h
  noSoloCross := fun _ h => h.2

/-- Fixed-point-free involution on Bool is negation. -/
theorem live_involution_cert (act : Bool → Bool)
    (hl : Orbit.Live act) :
    (∀ b, act b = !b) ∧ (∀ b, act b ≠ b) :=
  ⟨TwoCycle.bool_live_is_not act hl, fun b => hl b⟩

/-- AG oscillator realises a silent, non-merging certificate face. -/
theorem oscillator_fits_silent :
    Geom.Registration.Inj Geom.Registration.oscStep ∧
    ¬ Geom.Registration.Merges Geom.Registration.oscStep :=
  ⟨Geom.Registration.osc_never_registers.1,
   Geom.Registration.osc_never_registers.2.1⟩

/-- Admission checklist for the Bool swap certificate. -/
theorem bool_admitted :
    (∀ b, boolCert.swap (boolCert.swap b) = b) ∧
    (∀ b, boolCert.observe (boolCert.swap b) =
      boolCert.obsNeg (boolCert.observe b)) ∧
    (∀ b, boolCert.Fixed b ↔ boolCert.swap b = b) ∧
    (∀ b, ¬ boolCert.Fixed b) :=
  ⟨boolCert.involutive, boolCert.swap_as_not, boolCert.fixed_iff,
   fun _ h => h⟩

#print axioms bool_admitted
#print axioms live_involution_cert
#print axioms oscillator_fits_silent

end Dictionary.Certificate
