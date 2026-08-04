import Orbit
import Canon
import Alphabet

/-!
# No-cloning — measurement dictionary companion

Branch / measurement no-go (T-12 companion), paired with `Orbit.Lossless`.
Not an I-4 K-certificate: the Bell≠product support inequality is the
measurement package's no-go component (entanglement witness), not a swap
acting as ¬ on a kernel locus filing clauses (a)–(c).

Born rule, probabilities, preferred basis, and Hilbert space are not
claimed in this module; the content is a finite support caricature.
-/

namespace Dictionary.NoClone

/-! ## Three-tone alphabet -/

inductive Tone where
  | b0 | b1 | plus
  deriving DecidableEq, Repr

/-- Computational-basis flip; `plus` fixed (superposition locus).
    Auxiliary structure — not K-cert admission. -/
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

def Fixed (t : Tone) : Prop := flip t = t

theorem plus_fixed : Fixed Tone.plus := rfl

theorem basis_unfixed :
    ¬ Fixed Tone.b0 ∧ ¬ Fixed Tone.b1 := by
  constructor <;> intro h <;> cases h

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

/-- **Admission (measurement package).** No-cloning support inequality
    paired with Lossless; not a `KernelCert` filing. -/
theorem noClone_admitted :
    (InProduct (Tone.b0, Tone.b1) ∧ ¬ InBell (Tone.b0, Tone.b1)) ∧
    (∀ {α : Type} (act : α → α),
      Canon.IsFundamental act → Orbit.Lossless act) ∧
    (¬ ∃ (f : Tone → Unit), ∀ x y, f x = f y → x = y) ∧
    Bridge.Alphabet.Kmin = 2 :=
  ⟨no_cloning, lossless_floor, no_injection_tone_to_unit,
   Bridge.Alphabet.Kmin_eq⟩

#print axioms no_cloning
#print axioms noClone_admitted
#print axioms forced_ancilla
#print axioms lossless_floor

end Dictionary.NoClone
