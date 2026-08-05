import Geom.Registration
import Ladder
import Density
import Orbit
import RegistrationSpine
import Alphabet

/-!
# T-11 Archive monotonicity (combinatorial second-law shape)

Named corollary, not a construction. T-4 is Landauer-shaped:
what merges must register; erasure has a price. The ladder already proves
record monotonicity: `lift_injective` plus `no_retraction` mean the
archive never shrinks. Together: dissipation writes records, records
accumulate irreversibly, and the ledger arrow is the thermodynamic
arrow's combinatorial shadow.

Temperature, Boltzmann factors, and statistical mechanics proper are
not derived.
-/

namespace Bridge.ArchiveMonotone

/-- Merge-registers face (Landauer-shaped): injective merge forces a distinguishing record. -/
theorem merge_must_register {S E : Type} {U : S × E → S × E}
    (hU : Geom.Registration.Inj U)
    (hm : Geom.Registration.Merges U) :
    Geom.Registration.Registers U :=
  Bridge.RegistrationSpine.ag_merge_registers hU hm

/-- Records embed forward: prior archive injects into later archive. -/
theorem records_embed (k j : Nat) :
    ∀ x y : Ladder.Level k,
      Ladder.lift k j x = Ladder.lift k j y → x = y :=
  Ladder.lift_injective k j

/-- Archive never shrinks: no injective retraction onto a prior level. -/
theorem archive_irreversible (k : Nat) :
    ¬ ∃ (f : Ladder.Level (k + 1) → Ladder.Level k),
      ∀ x y, f x = f y → x = y :=
  Density.no_retraction k

/-- Erasure persists under iteration (priced forever once paid). -/
theorem erasure_priced {α : Type} (act : α → α) (h : Orbit.Erasing act) :
    ∃ x y : α, x ≠ y ∧
      ∀ n : Nat, Orbit.iter act (n + 1) x = Orbit.iter act (n + 1) y :=
  Bridge.RegistrationSpine.erasure_persists act h

/-- **T-11.** Combinatorial second law:
    (i) merge ⇒ record (Landauer);
    (ii) records embed up the ladder;
    (iii) no retraction (archive irreversible);
    (iv) Kmin = 2. -/
theorem T11_archive_monotonicity :
    (∀ {S E : Type} {U : S × E → S × E},
      Geom.Registration.Inj U →
      Geom.Registration.Merges U →
      Geom.Registration.Registers U) ∧
    (∀ k j : Nat, ∀ x y : Ladder.Level k,
      Ladder.lift k j x = Ladder.lift k j y → x = y) ∧
    (∀ k : Nat, ¬ ∃ (f : Ladder.Level (k + 1) → Ladder.Level k),
      ∀ x y, f x = f y → x = y) ∧
    Bridge.Alphabet.Kmin = 2 :=
  ⟨fun hU hm => merge_must_register hU hm,
   records_embed,
   archive_irreversible,
   Bridge.Alphabet.Kmin_eq⟩

#print axioms merge_must_register
#print axioms records_embed
#print axioms archive_irreversible
#print axioms T11_archive_monotonicity

end Bridge.ArchiveMonotone
