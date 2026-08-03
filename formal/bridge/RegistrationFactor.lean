import Ladder
import Tower
import Density
import Geom.Registration
import Environment

/-!
# T-2 Registration → naming factorisation (attack)

Positive fragment: every injective 2-merge admits a **namer-shaped**
witness — one record lies outside the image of a singleton embedding into
`E` (Tower `namer_is_new` shape on labels).

Obstruction: iterated swap registers forever on a **fixed** carrier
`E = Bool`, while every naming sequence of length `T` strictly increases
ladder cardinality. So Registration microticks do not in general factor
as ladder naming extensions of carriers — only as label-namer witnesses
inside an already-sufficient alphabet.

This locates where geometry (finite reusable alphabet) and representation
(strict type growth) come apart; naming-tick/microtick identification
stays restricted to the committed expand path plus this label fragment.
-/

namespace Bridge.RegistrationFactor

open Geom.Registration
open Bridge.Environment

/-- Singleton embedding of a prior one-point alphabet into `E`. -/
def singletonEmbed {E : Type} (e : E) : Unit → E := fun _ => e

/-- Image miss: `eNew` is not in the image of `singletonEmbed eOld`. -/
def outsideSingleton {E : Type} (eOld eNew : E) : Prop :=
  ∀ u : Unit, singletonEmbed eOld u ≠ eNew

theorem outsideSingleton_iff {E : Type} (eOld eNew : E) :
    outsideSingleton eOld eNew ↔ eOld ≠ eNew := by
  constructor
  · intro h heq
    exact h () heq
  · intro hne _u heq
    exact hne heq

/-- **Namer-shaped factor.** Under `Inj`, a 2-merge's two records are
    distinct, so each record is a namer relative to the singleton alphabet
    on the other. -/
theorem registers_admits_namer {S E : Type} {U : S × E → S × E}
    (hU : Inj U) (w : TwoMerge S E U) :
    outsideSingleton (recordLabel w false) (recordLabel w true) ∧
    outsideSingleton (recordLabel w true) (recordLabel w false) := by
  have hrec : recordLabel w true ≠ recordLabel w false := by
    intro h
    have ht : true = false := recordLabel_injective hU w true false h
    cases ht
  exact ⟨(outsideSingleton_iff _ _).mpr (Ne.symm hrec),
         (outsideSingleton_iff _ _).mpr hrec⟩

/-- Same fact packaged as Tower-style "namer is new". -/
theorem registers_namer_is_new {S E : Type} {U : S × E → S × E}
    (hU : Inj U) (w : TwoMerge S E U) :
    ∃ b : E, (∀ a : Unit, singletonEmbed (recordLabel w false) a ≠ b) ∧
      b = recordLabel w true :=
  ⟨recordLabel w true,
   (registers_admits_namer hU w).1,
   rfl⟩

/-- Swap's 2-merge factors as a namer witness. -/
theorem swap_factors_as_namer :
    outsideSingleton (recordLabel swapWitness false)
      (recordLabel swapWitness true) :=
  (registers_admits_namer swap_inj swapWitness).1

/-- Oscillator never demands a namer (no merge). -/
theorem oscillator_no_namer_demand :
    ¬ Merges oscStep :=
  osc_never_registers.2.1

/-! ## Obstruction: carrier growth vs reusable alphabet -/

/-- Iterated swap: environment carrier stays `Bool` at every microtick. -/
def swapMicrotick : Bool × Bool → Bool × Bool := swapStep

theorem swap_registers_every_tick :
    Inj swapMicrotick ∧ Merges swapMicrotick ∧ Registers swapMicrotick :=
  ⟨swap_inj, swap_registers.2.1, swap_registers.2.2⟩

/-- Ladder carrier cardinality after `T` naming ticks is `T + 2`. -/
theorem naming_carrier_card (T : Nat) :
    Density.levelCard T = T + 2 :=
  Density.levelCard_eq T

/-- Naming strictly increases carrier card each tick. -/
theorem naming_card_strict (k : Nat) :
    Density.levelCard (k + 1) = Density.levelCard k + 1 := by
  rw [Density.levelCard_eq, Density.levelCard_eq]

/-- Swap microticks reuse a 2-element environment forever. -/
theorem swap_env_card_fixed :
    ∃ a b : Bool, a ≠ b ∧ ∀ x : Bool, x = a ∨ x = b :=
  ⟨true, false, by decide, fun x => by cases x <;> decide⟩

/-- **Obstruction.** There is an eternally registering microstep
    (`swap`) whose env carrier does not grow, while naming of length
    `T ≥ 1` forces `levelCard T = T+2 > 2 = levelCard 0`.
    Hence Registration sequences do not factor as ladder naming
    extensions of carriers in general. -/
theorem registration_vs_naming_obstruction :
    (Inj swapStep ∧ Merges swapStep ∧ Registers swapStep) ∧
    (∀ T : Nat, Density.levelCard T = T + 2) ∧
    (Density.levelCard 0 = 2) ∧
    (∀ T : Nat, 1 ≤ T → Density.levelCard 0 < Density.levelCard T) := by
  refine ⟨⟨swap_inj, swap_registers.2.1, swap_registers.2.2⟩,
    naming_carrier_card, Density.levelCard_eq 0, ?_⟩
  intro T hT
  rw [Density.levelCard_eq, Density.levelCard_eq]
  have hpos : 0 < T := Nat.lt_of_lt_of_le (by decide : 0 < 1) hT
  rw [Nat.add_comm T 2]
  exact Nat.lt_add_of_pos_right hpos

/-- **T-2 factorisation package.** Positive namer-shaped factor for every
    injective 2-merge; carrier-level factorisation obstructed by swap. -/
theorem registration_naming_factorisation :
    (∀ {S E : Type} {U : S × E → S × E},
      Inj U → ∀ w : TwoMerge S E U,
        outsideSingleton (recordLabel w false) (recordLabel w true)) ∧
    (Inj swapStep ∧ Merges swapStep ∧ Registers swapStep) ∧
    (∀ T, 1 ≤ T → Density.levelCard 0 < Density.levelCard T) ∧
    (¬ Merges oscStep) :=
  ⟨fun hU w => (registers_admits_namer hU w).1,
   ⟨swap_inj, swap_registers.2.1, swap_registers.2.2⟩,
   fun T hT => (registration_vs_naming_obstruction).2.2.2 T hT,
   oscillator_no_namer_demand⟩

#print axioms registration_naming_factorisation
#print axioms registers_admits_namer
#print axioms registration_vs_naming_obstruction
#print axioms swap_factors_as_namer

end Bridge.RegistrationFactor
