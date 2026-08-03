import Certificate
import Orbit
import Canon
import Alphabet

/-!
# No-cloning — kernel dictionary entry (measurement companion)

Pairs with `Orbit.Lossless` the way Kramers pairs with fixed-point-freeness:
a finite three-tone no-go (computational basis + one non-eigenstate) shows
product cloning of a "superposition" disagrees with the linear image of
basis clones (Bell support ≠ product support).

Refused with T-12: Born rule, probabilities, preferred basis, Hilbert
space as Lean. This is the finite support caricature.
-/

namespace Dictionary.NoClone

open Dictionary.Certificate

/-! ## Three-tone alphabet -/

inductive Tone where
  | b0 | b1 | plus
  deriving DecidableEq, Repr

/-- Computational-basis flip; `plus` fixed (superposition locus). -/
def flip : Tone → Tone
  | .b0 => .b1
  | .b1 => .b0
  | .plus => .plus

theorem flip_involutive (t : Tone) : flip (flip t) = t := by
  cases t <;> rfl

inductive Obs where
  | zero | one | super
  deriving DecidableEq, Repr

def observe : Tone → Obs
  | .b0 => .zero
  | .b1 => .one
  | .plus => .super

def obsNeg : Obs → Obs
  | .zero => .one
  | .one => .zero
  | .super => .super

theorem observe_flip_as_neg (t : Tone) :
    observe (flip t) = obsNeg (observe t) := by
  cases t <;> rfl

/-! ## Support caricature of no-cloning -/

/-- Bell-diagonal support (linear image of |+⟩ after basis clones). -/
inductive InBell : Tone × Tone → Prop where
  | diag0 : InBell (Tone.b0, Tone.b0)
  | diag1 : InBell (Tone.b1, Tone.b1)

/-- Full computational product grid (product clone of |+⟩). -/
inductive InProduct : Tone × Tone → Prop where
  | p00 : InProduct (Tone.b0, Tone.b0)
  | p01 : InProduct (Tone.b0, Tone.b1)
  | p10 : InProduct (Tone.b1, Tone.b0)
  | p11 : InProduct (Tone.b1, Tone.b1)

theorem off_diag_product : InProduct (Tone.b0, Tone.b1) := InProduct.p01

theorem off_diag_not_bell : ¬ InBell (Tone.b0, Tone.b1) := by
  intro h
  cases h

/-- **No-cloning.** Off-diagonal pair is in the product grid, not Bell. -/
theorem no_cloning :
    InProduct (Tone.b0, Tone.b1) ∧ ¬ InBell (Tone.b0, Tone.b1) :=
  ⟨off_diag_product, off_diag_not_bell⟩

/-- Losslessness pairs: Fundamental admits no erasure. -/
theorem lossless_floor {α : Type} (act : α → α)
    (h : Canon.IsFundamental act) : Orbit.Lossless act :=
  h.lossless

/-! ## K-certificate: flip involution; fixed locus = plus (nonempty) -/

def noCloneCert : KernelCert Tone Obs where
  swap := flip
  square := id
  swap_sq := fun t => by cases t <;> rfl
  square_involutive := fun _ => rfl
  observe := observe
  obsNeg := obsNeg
  swap_as_not := observe_flip_as_neg
  Fixed := fun t => flip t = t
  fixed_iff := fun _ => Iff.rfl
  fixedMode := FixedMode.nonempty
  noSoloCross := fun _ h => h.2

theorem plus_fixed : noCloneCert.Fixed Tone.plus := rfl

theorem basis_unfixed :
    ¬ noCloneCert.Fixed Tone.b0 ∧ ¬ noCloneCert.Fixed Tone.b1 := by
  constructor <;> intro h <;> cases h

/-- Forced +1 / ancilla: Tone does not inject into Unit. -/
theorem no_injection_tone_to_unit :
    ¬ ∃ (f : Tone → Unit), ∀ x y, f x = f y → x = y := by
  intro ⟨f, hinj⟩
  have h01 : Tone.b0 = Tone.b1 := hinj _ _ (Subsingleton.elim (f _) (f _))
  cases h01

theorem forced_ancilla :
    (¬ ∃ (f : Tone → Unit), ∀ x y, f x = f y → x = y) ∧
    Bridge.Alphabet.Kmin = 2 :=
  ⟨no_injection_tone_to_unit, Bridge.Alphabet.Kmin_eq⟩

/-- **Admission.** -/
theorem noClone_admitted :
    (InProduct (Tone.b0, Tone.b1) ∧ ¬ InBell (Tone.b0, Tone.b1)) ∧
    (∀ t, noCloneCert.swap (noCloneCert.swap t) = noCloneCert.square t) ∧
    (∀ t, noCloneCert.observe (noCloneCert.swap t) =
      noCloneCert.obsNeg (noCloneCert.observe t)) ∧
    noCloneCert.Fixed Tone.plus ∧
    noCloneCert.fixedMode = FixedMode.nonempty ∧
    (¬ ∃ (f : Tone → Unit), ∀ x y, f x = f y → x = y) ∧
    Bridge.Alphabet.Kmin = 2 :=
  ⟨no_cloning, noCloneCert.swap_sq, noCloneCert.swap_as_not,
   plus_fixed, rfl, no_injection_tone_to_unit, Bridge.Alphabet.Kmin_eq⟩

#print axioms no_cloning
#print axioms noClone_admitted
#print axioms forced_ancilla
#print axioms lossless_floor

end Dictionary.NoClone
