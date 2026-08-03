import TwoCycle
import Orbit
import Geom.Registration

/-!
# I-4 Dictionary admission certificates

Two routes (spec §5):

**K-certificate** — kernel / spine instantiations:
  (a) symmetry with `swap ∘ swap = square` (id or central negation);
  (b) observable acted on as exact negation;
  (c) fixed set = distinguished locus (nonempty | empty modes);
  (d) no-go: level below cannot represent the symmetry alone (forced +1).

**L-certificate** — ledger instantiations: see `LCertificate.lean`
  (Inj U, merge, record, capacity/aliveness, exhaustion + T-10).

This module is the K-certificate schema. Between nonempty and empty modes,
the dictionary exhausts the kernel's fixed-point story
(`Orbit.void_is_excluded_fixed_point` ↔ empty mode).
-/

namespace Dictionary.Certificate

/-- Clause (c) mode: nonempty distinguished locus vs provably empty void. -/
inductive FixedMode where
  | nonempty
  | empty
  deriving DecidableEq, Repr

/-- Kernel-side certificate data for a labelled state space.
    `square = id` recovers a strict involution; `square = neg ≠ id` is
    the Kramers (T² = −1) mode. -/
structure KernelCert (State : Type) (Obs : Type) where
  /-- (a) symmetry of the EOM -/
  swap : State → State
  /-- Target of `swap ∘ swap` (`id` or central negation) -/
  square : State → State
  swap_sq : ∀ s, swap (swap s) = square s
  square_involutive : ∀ s, square (square s) = s
  /-- (b) observable acted on as negation -/
  observe : State → Obs
  obsNeg : Obs → Obs
  swap_as_not : ∀ s, observe (swap s) = obsNeg (observe s)
  /-- (c) fixed set of the symmetry -/
  Fixed : State → Prop
  fixed_iff : ∀ s, Fixed s ↔ swap s = s
  fixedMode : FixedMode
  /-- (d) no-go caricature at kernel level -/
  noSoloCross : ∀ s, ¬ (Fixed s ∧ False)

/-- Strict involution package: `square = id`. -/
def isStrictInvolution {State Obs : Type} (c : KernelCert State Obs) : Prop :=
  ∀ s, c.square s = s

/-- Bool certificate: swap = ¬, square = id, fixed set empty (live). -/
def boolCert : KernelCert Bool Bool where
  swap := not
  square := id
  swap_sq := fun b => by cases b <;> rfl
  square_involutive := fun b => rfl
  observe := id
  obsNeg := not
  swap_as_not := fun b => by cases b <;> rfl
  Fixed := fun _ => False
  fixed_iff := fun b => by
    constructor
    · intro h; exact False.elim h
    · intro h; cases b <;> cases h
  fixedMode := FixedMode.empty
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
    (∀ b, boolCert.swap (boolCert.swap b) = boolCert.square b) ∧
    (∀ b, boolCert.square b = b) ∧
    (∀ b, boolCert.observe (boolCert.swap b) =
      boolCert.obsNeg (boolCert.observe b)) ∧
    (∀ b, ¬ boolCert.Fixed b) ∧
    boolCert.fixedMode = FixedMode.empty :=
  ⟨boolCert.swap_sq, fun _ => rfl, boolCert.swap_as_not,
   fun _ h => h, rfl⟩

/-- Spine void exclusion is the empty-mode reading of clause (c). -/
theorem empty_mode_is_void_exclusion :
    (∀ x : Bool, (!x) ≠ x) ∧
    Orbit.Live (not : Bool → Bool) :=
  ⟨fun x => by cases x <;> decide, fun x => by cases x <;> decide⟩

#print axioms bool_admitted
#print axioms live_involution_cert
#print axioms oscillator_fits_silent
#print axioms empty_mode_is_void_exclusion

end Dictionary.Certificate
