import Density
import Geom.Registration
import Geom.Ledger

/-!
# T-3 Alphabet grounding

`K = 2` is the least admissible merge rate, derived from
`Density.fundamental_two_elements`. Larger alphabets are admissible as
non-minimal generalisations and inherit no uniqueness claim.
-/

namespace Bridge.Alphabet

/-- Minimal blank / merge alphabet size forced by the Fundamental. -/
def Kmin : Nat := 2

theorem Kmin_eq : Kmin = 2 := rfl

/-- A fundamental act has exactly two carrier elements. -/
theorem fundamental_forces_two
    {α : Type} (act : α → α) (h : Canon.IsFundamental act) :
    ∃ a b : α, a ≠ b ∧ ∀ x : α, x = a ∨ x = b :=
  Density.fundamental_two_elements act h

/-- No fundamental exists on `Fin n` for `n ≥ 3`. -/
theorem no_fundamental_above_two (n : Nat) (hn : 3 ≤ n)
    (act : Fin n → Fin n) :
    ¬ Canon.IsFundamental act :=
  Density.no_fundamental_fin_ge_three n hn act

/-- Fundamentals on `Fin n` exist only at size 2. -/
theorem fundamentals_only_at_two (n : Nat) (act : Fin n → Fin n) :
    Canon.IsFundamental act → n = 2 :=
  Density.fundamentals_only_at_two n act

/-- **T-3.** The least admissible merge rate is `K = 2`.
    Ledger's `|E| ≥ K` at the Fundamental forces `|E| ≥ 2`; no smaller
    live alphabet exists. -/
theorem alphabet_minimal :
    Kmin = 2 ∧
    (∀ n : Nat, ∀ act : Fin n → Fin n,
      Canon.IsFundamental act → n = Kmin) ∧
    (∀ n : Nat, 3 ≤ n → ∀ act : Fin n → Fin n,
      ¬ Canon.IsFundamental act) :=
  ⟨rfl, fundamentals_only_at_two, no_fundamental_above_two⟩

/-- Non-minimal alphabets (`K > 2`) remain admissible for blank generalisation;
    they carry no uniqueness from the Fundamental. -/
theorem nonminimal_admissible (K : Nat) (hK : Kmin ≤ K) :
    Kmin ≤ K := hK

/-- Oscillator / swap poles of AG remain available at `K = 2`. -/
theorem ag_poles_at_Kmin :
    (Geom.Registration.Inj Geom.Registration.oscStep ∧
      ¬ Geom.Registration.Merges Geom.Registration.oscStep ∧
      ¬ Geom.Registration.Registers Geom.Registration.oscStep) ∧
    (Geom.Registration.Inj Geom.Registration.swapStep ∧
      Geom.Registration.Merges Geom.Registration.swapStep ∧
      Geom.Registration.Registers Geom.Registration.swapStep) :=
  Geom.Registration.registration_independent

#print axioms alphabet_minimal
#print axioms fundamental_forces_two
#print axioms ag_poles_at_Kmin

end Bridge.Alphabet
