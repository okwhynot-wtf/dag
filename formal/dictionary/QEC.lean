import LCertificate
import Geom.Registration
import Alphabet

/-!
# QEC toy — ledger dictionary entry (quantum error correction)

Second L-domain (after Page): syndrome extraction ≅ merge⇒record;
stabilizer / codespace caricature ≅ Inj on the joint step.

Finite toy only — not a Hilbert-space code, not threshold theorems,
not holographic code duality as Lean gravity. The point is that a
genuinely different physical domain still fills the L-certificate
schema (Inj, merge, record, capacity/exhaustion).

Dictionary:
  Syndrome extraction          ↔ Registration (merge ⇒ record)
  Stabilizer / codespace       ↔ Inj(U) on joint system×syndrome
  Error support collapse       ↔ system-side merge (U_S)
  Syndrome register            ↔ environment E
  Distance / redundancy bound  ↔ |E| ≥ K (alphabet corollary)
-/

namespace Dictionary.QEC

open Dictionary.LCertificate
open Geom.Registration

/-! ## Finite stabilizer caricature

`S = Bool` = one data qubit (coarse); `E = Bool` = one syndrome bit.
`swapStep` is again the Registration witness: injective joint dynamics,
system merge, syndrome record. Same skeleton as Page, different gloss —
that is the dictionary point.
-/

/-- Joint encode/extract step (Registration witness). -/
def U : Bool × Bool → Bool × Bool := swapStep

theorem qec_inj : Inj U := swap_inj

theorem qec_syndrome_merge : Merges U := swap_registers.2.1

theorem qec_syndrome_record : Registers U := swap_registers.2.2

/-- Syndrome register holds at least Kmin distinctions. -/
theorem syndrome_alphabet :
    Bridge.Alphabet.Kmin = 2 ∧ Registers U :=
  ⟨Bridge.Alphabet.Kmin_eq, qec_syndrome_record⟩

/-- Registration reading: syndrome extraction is merge⇒record. -/
theorem syndrome_is_registration :
    Inj U ∧ Merges U ∧ Registers U :=
  ⟨qec_inj, qec_syndrome_merge, qec_syndrome_record⟩

/-! ## L-certificate filing -/

/-- L-certificate at a finite "decode horizon" (bounce Page time). -/
def qecCert (tTurn : Nat) : LedgerCert Bool Bool where
  U := U
  inj := qec_inj
  merges := qec_syndrome_merge
  registers := qec_syndrome_record
  K := 2
  hK := by decide
  prof := Geom.Profile.bounce tTurn
  tExh := tTurn
  alive_before := (bounceSchedule (by decide : 2 ≤ 2) tTurn).1
  is_exhaustion := (bounceSchedule (by decide : 2 ≤ 2) tTurn).2

/-- **Admission.** QEC toy fills an L-certificate (distinct domain from Page). -/
theorem qec_admitted :
    (∀ (_ : Nat), ∃ _c : LedgerCert Bool Bool, True) ∧
    (Inj U ∧ Merges U ∧ Registers U) ∧
    Bridge.Alphabet.Kmin = 2 :=
  ⟨fun t => ⟨qecCert t, True.intro⟩,
   syndrome_is_registration,
   Bridge.Alphabet.Kmin_eq⟩

/-- Dictionary extensibility: Page and QEC are two L-entries on one schema. -/
theorem two_L_domains :
    (∃ _c : LedgerCert Bool Bool, True) ∧
    Inj U ∧ Registers U :=
  ⟨⟨qecCert 0, True.intro⟩, qec_inj, qec_syndrome_record⟩

#print axioms qec_inj
#print axioms syndrome_is_registration
#print axioms qec_admitted
#print axioms two_L_domains

end Dictionary.QEC
