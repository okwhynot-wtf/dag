import Certificate
import Orbit
import Alphabet

/-!
# Kramers time reversal — third dictionary entry

Empty-fixed-set mode of clause (c): T² = −1 ⇒ no T-invariant state
(orthogonality caricature `ψ ≠ Tψ`), forced degeneracy ≥ 2 (Kramers
doublet = forced +1), and that floor equals `Bridge.Alphabet.Kmin`.

Kernel side: four-notch circle (T = +1, T² = +2 = central negation).
No QFT, no Mathlib ℂ, no ODEs. Physical payoff in `exhibits/kramers/`.

Complements RE/quintom (nonempty locus w = −1): this entry demonstrates
fixed-point-*freeness* — the void has no instances.
-/

namespace Dictionary.Kramers

open Dictionary.Certificate

/-! ## Discrete model: four-notch circle with T² = central negation -/

inductive Notch where
  | n0 | n1 | n2 | n3
  deriving DecidableEq, Repr

/-- Time-reversal caricature: advance one notch. -/
def T : Notch → Notch
  | .n0 => .n1
  | .n1 => .n2
  | .n2 => .n3
  | .n3 => .n0

/-- Central negation: T² (−1 on the circle of 4). -/
def neg : Notch → Notch
  | .n0 => .n2
  | .n1 => .n3
  | .n2 => .n0
  | .n3 => .n1

theorem T_sq (i : Notch) : T (T i) = neg i := by
  cases i <;> rfl

theorem neg_sq (i : Notch) : neg (neg i) = i := by
  cases i <;> rfl

/-- (c) empty mode: no T-fixed state. -/
theorem T_no_fixed (i : Notch) : T i ≠ i := by
  cases i <;> intro h <;> cases h

/-- Orthogonality caricature: ⟨ψ|Tψ⟩ = 0 ⇒ ψ ≠ Tψ. -/
theorem partner_ne (i : Notch) : T i ≠ i :=
  T_no_fixed i

/-- Negation is nontrivial (−1 ≠ 1). -/
theorem neg_ne_id (i : Notch) : neg i ≠ i := by
  cases i <;> intro h <;> cases h

/-! ## (b) Negation observable -/

def spin : Notch → Bool
  | .n0 => true
  | .n1 => false
  | .n2 => true
  | .n3 => false

theorem spin_T_as_not (i : Notch) : spin (T i) = !(spin i) := by
  cases i <;> rfl

/-! ## (d) Forced +1 / Kramers degeneracy -/

def TClosed (S : Notch → Prop) : Prop :=
  ∀ i, S i → S (T i)

/-- **Forced doublet.** Any nonempty T-closed set contains a distinct partner. -/
theorem forced_doublet {S : Notch → Prop} (hC : TClosed S)
    {i : Notch} (hi : S i) :
    ∃ j : Notch, S j ∧ j ≠ i :=
  ⟨T i, hC i hi, T_no_fixed i⟩

theorem degeneracy_ge_two {S : Notch → Prop} (hC : TClosed S)
    (hNon : ∃ i, S i) :
    ∃ a b : Notch, a ≠ b ∧ S a ∧ S b := by
  obtain ⟨i, hi⟩ := hNon
  obtain ⟨j, hj, hne⟩ := forced_doublet hC hi
  exact ⟨i, j, Ne.symm hne, hi, hj⟩

theorem degeneracy_eq_Kmin :
    Bridge.Alphabet.Kmin = 2 ∧
    (∀ {S : Notch → Prop}, TClosed S → (∃ i, S i) →
      ∃ a b : Notch, a ≠ b ∧ S a ∧ S b) :=
  ⟨Bridge.Alphabet.Kmin_eq, fun hC hN => degeneracy_ge_two hC hN⟩

theorem singleton_not_TClosed (i : Notch) :
    ¬ TClosed (fun j => j = i) := by
  intro hC
  exact T_no_fixed i (hC i rfl)

/-! ## Filed I-4 certificate (empty fixed-set mode) -/

def kramersCert : KernelCert Notch Bool where
  swap := T
  square := neg
  swap_sq := T_sq
  square_involutive := neg_sq
  observe := spin
  obsNeg := not
  swap_as_not := spin_T_as_not
  Fixed := fun i => T i = i
  fixed_iff := fun _ => Iff.rfl
  fixedMode := FixedMode.empty
  noSoloCross := fun i h => T_no_fixed i h.1

/-- **Admission.** Kramers satisfies (a)–(d) in empty-locus mode;
    forced +1 is the doublet with floor `Kmin`. -/
theorem kramers_admitted :
    (∀ i, kramersCert.swap (kramersCert.swap i) = kramersCert.square i) ∧
    (∀ i, kramersCert.square (kramersCert.square i) = i) ∧
    (¬ isStrictInvolution kramersCert) ∧
    (∀ i, kramersCert.observe (kramersCert.swap i) =
      kramersCert.obsNeg (kramersCert.observe i)) ∧
    (∀ i, ¬ kramersCert.Fixed i) ∧
    kramersCert.fixedMode = FixedMode.empty ∧
    (∀ i, ¬ TClosed (fun j => j = i)) ∧
    Bridge.Alphabet.Kmin = 2 := by
  refine ⟨kramersCert.swap_sq, kramersCert.square_involutive, ?_,
    kramersCert.swap_as_not, T_no_fixed, rfl, singleton_not_TClosed,
    Bridge.Alphabet.Kmin_eq⟩
  intro hstrict
  exact neg_ne_id Notch.n0 (hstrict Notch.n0)

theorem fixed_modes_exhaust :
    FixedMode.empty ≠ FixedMode.nonempty ∧
    kramersCert.fixedMode = FixedMode.empty :=
  ⟨(fun h => by cases h), rfl⟩

/-- Spine void exclusion wears this physical reading. -/
theorem void_reading :
    (∀ i : Notch, T i ≠ i) ∧
    (∀ i : Notch, T i ≠ i) :=
  ⟨T_no_fixed, Orbit.void_is_excluded_fixed_point T T_no_fixed⟩

/-- Together with quintom's nonempty mode, clause (c) is exhausted. -/
theorem clause_c_duality :
    kramersCert.fixedMode = FixedMode.empty ∧
    FixedMode.empty ≠ FixedMode.nonempty :=
  ⟨rfl, fun h => by cases h⟩

#print axioms kramers_admitted
#print axioms forced_doublet
#print axioms degeneracy_eq_Kmin
#print axioms singleton_not_TClosed
#print axioms void_reading
#print axioms clause_c_duality

end Dictionary.Kramers
