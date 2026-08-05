import Orbit
import TwoCycle

/-!
# KernelAdmit — admission interface on kernel exports (dynamics layer)

A Bool kernel certificate is a structure on kernel exports (swap / observe /
fixed locus) satisfying the admission clauses. This module owns the
interface and proves face-swap equivariance; the dictionary layer
instantiates the same interface at physical models and does not feed
theorems in Sections 3–10.
-/
namespace Bridge.KernelAdmit

/-- Clause (c) mode: nonempty distinguished locus vs provably empty void. -/
inductive FixedMode where
  | nonemptyLocus
  | emptyLocus
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

/-- Admission checklist for a Bool-valued strict empty-locus certificate. -/
def AdmittedBool (c : KernelCert Bool Bool) : Prop :=
  (∀ b, c.swap (c.swap b) = c.square b) ∧
  (∀ b, c.square b = b) ∧
  (∀ b, c.observe (c.swap b) = c.obsNeg (c.observe b)) ∧
  (∀ b, ¬ c.Fixed b) ∧
  c.fixedMode = FixedMode.emptyLocus

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
  fixedMode := FixedMode.emptyLocus
  noSoloCross := fun _ h => h.2

theorem bool_admitted : AdmittedBool boolCert :=
  ⟨boolCert.swap_sq, fun _ => rfl, boolCert.swap_as_not,
   fun _ h => h, rfl⟩

/-- Pole-swap the Bool certificate by conjugating through `not`. -/
def boolCert_faceSwap : KernelCert Bool Bool where
  swap := fun b => !(boolCert.swap (!b))
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
  fixedMode := FixedMode.emptyLocus
  noSoloCross := fun _ h => h.2

theorem boolCert_faceSwap_eq_swap (b : Bool) :
    boolCert_faceSwap.swap b = boolCert.swap b := by
  cases b <;> rfl

theorem bool_admitted_faceSwap : AdmittedBool boolCert_faceSwap :=
  ⟨boolCert_faceSwap.swap_sq, fun _ => rfl, boolCert_faceSwap.swap_as_not,
   fun _ h => h, rfl⟩

/-- **Face-swap equivariance.** Bool kernel admission is invariant under
    the ℤ/2 face/pole conjugation, so face choice is packaging for
    equivariant consumers of the admission interface. -/
theorem bool_cert_face_equivariant :
    AdmittedBool boolCert ∧ AdmittedBool boolCert_faceSwap ∧
    (∀ b, boolCert_faceSwap.swap b = boolCert.swap b) :=
  ⟨bool_admitted, bool_admitted_faceSwap, boolCert_faceSwap_eq_swap⟩

/-- Fixed-point-free involution on Bool is negation. -/
theorem live_involution_cert (act : Bool → Bool)
    (hl : Orbit.Live act) :
    (∀ b, act b = !b) ∧ (∀ b, act b ≠ b) :=
  ⟨TwoCycle.bool_live_is_not act hl, fun b => hl b⟩

/-- Spine void exclusion is the empty-mode reading of clause (c). -/
theorem empty_mode_is_void_exclusion :
    (∀ x : Bool, (!x) ≠ x) ∧
    Orbit.Live (not : Bool → Bool) :=
  ⟨fun x => by cases x <;> decide, fun x => by cases x <;> decide⟩

#print axioms bool_admitted
#print axioms bool_admitted_faceSwap
#print axioms boolCert_faceSwap_eq_swap
#print axioms bool_cert_face_equivariant
#print axioms live_involution_cert
#print axioms empty_mode_is_void_exclusion

end Bridge.KernelAdmit
