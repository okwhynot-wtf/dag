import TwoCycle
import Orbit
import Geom.Registration

/-!
# I-4 Dictionary admission certificates

Two admission routes:

**K-certificate** — kernel / spine instantiations:
  (a) symmetry with `swap ∘ swap = square` (id or central negation);
  (b) observable acted on as exact negation;
  (c) fixed set = distinguished locus (nonempty | empty modes);
  (d) no-go: level below cannot represent the symmetry alone (forced +1).

**L-certificate** — ledger instantiations: see `LCertificate.lean`
  (Inj U, merge, record, capacity/aliveness, exhaustion + T-10).

This module defines the K-certificate schema. Nonempty and empty modes
of clause (c) together exhaust the kernel fixed-point story
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

/-! ## Face-swap equivariance (dictionary residue relocation)

Validity of a kernel certificate is stable under pole / face swap: conjugating
by an involution on the observation bit, or swapping the Bool seed polarity,
preserves the admission clauses. When this holds, face choice is packaging
(Definition of content vs packaging / Table of gauges). If a certificate
breaks equivariance by fixing an orientation, that orientation is
certificate-supplied data and is audited there. -/

/-- Pole-swap the Bool certificate by conjugating observation through `not`.
    The resulting certificate is definitionally the same swap/square package. -/
def boolCert_faceSwap : KernelCert Bool Bool where
  swap := fun b => !(boolCert.swap (!b))  -- not ∘ swap ∘ not
  square := id
  swap_sq := fun b => by cases b <;> rfl
  square_involutive := fun _ => rfl
  observe := fun b => !(boolCert.observe b)
  obsNeg := not
  swap_as_not := fun b => by cases b <;> rfl
  Fixed := fun b => boolCert.Fixed (!b)
  fixed_iff := fun b => by
    constructor
    · intro h; exact False.elim h
    · intro h; cases b <;> cases h
  fixedMode := FixedMode.empty
  noSoloCross := fun _ h => h.2

/-- Conjugating Bool swap by negation recovers negation. -/
theorem boolCert_faceSwap_eq_swap (b : Bool) :
    boolCert_faceSwap.swap b = boolCert.swap b := by
  cases b <;> rfl

/-- Admission clauses are stable under face swap. -/
theorem bool_admitted_faceSwap :
    (∀ b, boolCert_faceSwap.swap (boolCert_faceSwap.swap b) =
      boolCert_faceSwap.square b) ∧
    (∀ b, boolCert_faceSwap.square b = b) ∧
    (∀ b, boolCert_faceSwap.observe (boolCert_faceSwap.swap b) =
      boolCert_faceSwap.obsNeg (boolCert_faceSwap.observe b)) ∧
    (∀ b, ¬ boolCert_faceSwap.Fixed b) ∧
    boolCert_faceSwap.fixedMode = FixedMode.empty :=
  ⟨boolCert_faceSwap.swap_sq, fun _ => rfl, boolCert_faceSwap.swap_as_not,
   fun _ h => h, rfl⟩

/-- **Equivariance.** Bool kernel admission is face-swap invariant:
    validity on the quotient by the ℤ/2 action. -/
theorem bool_cert_face_equivariant :
    ((∀ b, boolCert.swap (boolCert.swap b) = boolCert.square b) ∧
      (∀ b, boolCert.square b = b) ∧
      (∀ b, boolCert.observe (boolCert.swap b) =
        boolCert.obsNeg (boolCert.observe b)) ∧
      (∀ b, ¬ boolCert.Fixed b) ∧
      boolCert.fixedMode = FixedMode.empty) ∧
    ((∀ b, boolCert_faceSwap.swap (boolCert_faceSwap.swap b) =
        boolCert_faceSwap.square b) ∧
      (∀ b, boolCert_faceSwap.square b = b) ∧
      (∀ b, boolCert_faceSwap.observe (boolCert_faceSwap.swap b) =
        boolCert_faceSwap.obsNeg (boolCert_faceSwap.observe b)) ∧
      (∀ b, ¬ boolCert_faceSwap.Fixed b) ∧
      boolCert_faceSwap.fixedMode = FixedMode.empty) ∧
    (∀ b, boolCert_faceSwap.swap b = boolCert.swap b) :=
  ⟨bool_admitted, bool_admitted_faceSwap, boolCert_faceSwap_eq_swap⟩

/-- Kernel exports used downstream are swap-equivariant: any surviving
    orientation in an application was supplied by a certificate and is
    audited there. Marker packages the Bool case. -/
theorem kernel_exports_swap_equivariant :
    ((∀ b, boolCert.swap (boolCert.swap b) = boolCert.square b) ∧
      (∀ b, boolCert.square b = b) ∧
      (∀ b, boolCert.observe (boolCert.swap b) =
        boolCert.obsNeg (boolCert.observe b)) ∧
      (∀ b, ¬ boolCert.Fixed b) ∧
      boolCert.fixedMode = FixedMode.empty) ∧
    ((∀ b, boolCert_faceSwap.swap (boolCert_faceSwap.swap b) =
        boolCert_faceSwap.square b) ∧
      (∀ b, boolCert_faceSwap.square b = b) ∧
      (∀ b, boolCert_faceSwap.observe (boolCert_faceSwap.swap b) =
        boolCert_faceSwap.obsNeg (boolCert_faceSwap.observe b)) ∧
      (∀ b, ¬ boolCert_faceSwap.Fixed b) ∧
      boolCert_faceSwap.fixedMode = FixedMode.empty) ∧
    (∀ b, boolCert_faceSwap.swap b = boolCert.swap b) ∧
    (∀ b, boolCert.swap (boolCert.swap b) = b) :=
  ⟨bool_admitted, bool_admitted_faceSwap, boolCert_faceSwap_eq_swap,
   fun b => by cases b <;> rfl⟩

#print axioms bool_admitted
#print axioms live_involution_cert
#print axioms oscillator_fits_silent
#print axioms empty_mode_is_void_exclusion
#print axioms bool_admitted_faceSwap
#print axioms bool_cert_face_equivariant
#print axioms kernel_exports_swap_equivariant

end Dictionary.Certificate
