import Orbit
import Ladder
import Tower
import Cause
import Canon
import Geom.Registration
import Geom.Ledger

/-!
# T-4 Registration on the spine

A merging reading strictly above the lossless base forces named
compensation at the next level (Landauer-shaped): what merges must
register. Ingredients: `Orbit.erasing_forever`,
`Cause.erasure_breaks_transmission`, ladder naming extensions.
-/

namespace Bridge.RegistrationSpine

open Geom.Registration

/-- AG registration restated: injective joint merge writes a record. -/
theorem ag_merge_registers {S E : Type} {U : S × E → S × E}
    (hU : Inj U) : Merges U → Registers U :=
  Geom.Registration.merge_registers hU

/-- Spine: erasure (system-side merge) persists under iteration. -/
theorem erasure_persists {α : Type} (act : α → α) (h : Orbit.Erasing act) :
    ∃ x y : α, x ≠ y ∧ ∀ n : Nat, Orbit.iter act (n + 1) x = Orbit.iter act (n + 1) y :=
  Orbit.erasing_forever act h

/-- Spine: erasure breaks exact transmission of diagonal differences. -/
theorem erasure_breaks :
    ∃ (act : Bool → Bool) (f f' : Bool → Bool → Bool) (a : Bool),
      Orbit.Erasing act ∧
      f a a ≠ f' a a ∧ Cause.effectOf act f a = Cause.effectOf act f' a :=
  Cause.erasure_breaks_transmission

/-- At the Fundamental (lossless base), no erasure. -/
theorem fundamental_lossless {α : Type} (act : α → α)
    (h : Canon.IsFundamental act) : Orbit.Lossless act :=
  h.lossless

/-- Ladder step names the dodge: forced +1 compensation for the
    unrepresented predicate (emanation / blank adjunction gloss). -/
theorem ladder_names_compensation (k : Nat) :
    Tower.NamingExtension
      (Ladder.rep k) (Ladder.rep (k + 1)) some (Ladder.dodgeEscape k) :=
  Ladder.ladder_step k

/-- The namer is new — not in the image of the prior level. -/
theorem namer_outside_prior (k : Nat) :
    ∃ b : Ladder.Level (k + 1),
      (∀ a : Ladder.Level k, Ladder.rep (k + 1) b (some a) =
        Ladder.dodgeEscape k a) ∧
      (∀ a : Ladder.Level k, (some a : Ladder.Level (k + 1)) ≠ b) :=
  Tower.namer_is_new (Ladder.ladder_step k)

/-- System-side merge on a joint step forces an environment distinction. -/
theorem merge_forces_record_or_ascent {S E : Type}
    {U : S × E → S × E} (hU : Inj U) (hm : Merges U) :
    Registers U :=
  ag_merge_registers hU hm

/-- **T-4.** Registration on the spine package:
    (i) AG merge ⇒ record;
    (ii) Fundamental is lossless (no base erasure);
    (iii) ladder tick forces a new namer (compensation);
    (iv) erasure breaks transmission. -/
theorem registration_on_spine :
    (∀ {S E : Type} {U : S × E → S × E},
      Inj U → Merges U → Registers U) ∧
    (∀ {α : Type} (act : α → α),
      Canon.IsFundamental act → Orbit.Lossless act) ∧
    (∀ k : Nat, Tower.NamingExtension
      (Ladder.rep k) (Ladder.rep (k + 1)) some (Ladder.dodgeEscape k)) ∧
    (∃ (act : Bool → Bool) (f f' : Bool → Bool → Bool) (a : Bool),
      Orbit.Erasing act ∧ f a a ≠ f' a a ∧
      Cause.effectOf act f a = Cause.effectOf act f' a) :=
  ⟨fun hU hm => ag_merge_registers hU hm,
   fun act h => fundamental_lossless act h,
   ladder_names_compensation,
   erasure_breaks⟩

#print axioms registration_on_spine
#print axioms ladder_names_compensation
#print axioms ag_merge_registers

end Bridge.RegistrationSpine
