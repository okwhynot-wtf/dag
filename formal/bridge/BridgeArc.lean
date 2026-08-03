import Alphabet
import Capacity
import OneZ2
import RegistrationSpine
import TickSimulation
import Environment
import RegistrationFactor
import ArchiveMustSpeak
import SecondLaw
import Measurement
import Expansion
import Forman
import Geom.Registration
import Geom.Profile
import Density
import Canon
import Orbit
import Cause
import Tower
import Ladder
import Branch
import Diagonal
import Limit

/-!
# Bridge arc — milestone weld
-/

namespace Bridge.Arc

theorem milestone_M1 :
    Bridge.Alphabet.Kmin = 2 ∧
    (∀ f : Bridge.OneZ2.Face, ∀ b : Bridge.OneZ2.Z2,
      Bridge.OneZ2.project f (Bridge.OneZ2.project f b) = b) ∧
    (∀ T, Bridge.Capacity.caps T = 2 ^ (T + 2)) :=
  ⟨Bridge.Alphabet.Kmin_eq,
   Bridge.OneZ2.project_involution,
   Bridge.Capacity.caps_eq⟩

theorem milestone_M2 :
    (∀ {S E : Type} {U : S × E → S × E},
      Geom.Registration.Inj U →
      Geom.Registration.Merges U →
      Geom.Registration.Registers U) ∧
    (∀ {α : Type} (act : α → α),
      Canon.IsFundamental act → Orbit.Lossless act) ∧
    (∀ k : Nat, Tower.NamingExtension
      (Ladder.rep k) (Ladder.rep (k + 1)) some (Ladder.dodgeEscape k)) ∧
    (∃ (act : Bool → Bool) (f f' : Bool → Bool → Bool) (a : Bool),
      Orbit.Erasing act ∧ f a a ≠ f' a a ∧
      Cause.effectOf act f a = Cause.effectOf act f' a) :=
  Bridge.RegistrationSpine.registration_on_spine

theorem milestone_M4 :
    (∀ T, Bridge.Capacity.caps T = 2 ^ (T + 2)) ∧
    (∀ T, Geom.Profile.Alive 2 Geom.Profile.expand T) ∧
    (∀ T, 2 ^ T ≤ Bridge.Capacity.caps T) ∧
    (∀ T, Geom.Profile.capacityOf 2 Geom.Profile.expand (T + 1) =
      2 * Geom.Profile.capacityOf 2 Geom.Profile.expand T) ∧
    (∀ T, Bridge.Capacity.caps (T + 1) = 2 * Bridge.Capacity.caps T) ∧
    (∀ k, Tower.NamingExtension
      (Ladder.rep k) (Ladder.rep (k + 1)) some (Ladder.dodgeEscape k)) ∧
    (∀ k, ∃ b : Ladder.Level (k + 1),
      ∀ a : Ladder.Level k, (some a : Ladder.Level (k + 1)) ≠ b) ∧
    (¬ Geom.Registration.Merges Geom.Registration.oscStep) ∧
    (Geom.Registration.Registers Geom.Registration.swapStep) :=
  Bridge.TickSimulation.tick_simulation

theorem milestone_M5 :
    (∀ {S E : Type} {U : S × E → S × E},
      Geom.Registration.Inj U →
      ∀ w : Bridge.Environment.TwoMerge S E U,
        ∀ i j, Bridge.Environment.recordLabel w i =
          Bridge.Environment.recordLabel w j → i = j) ∧
    (Geom.Registration.Inj Geom.Registration.swapStep ∧
      Geom.Registration.Merges Geom.Registration.swapStep ∧
      Geom.Registration.Registers Geom.Registration.swapStep) ∧
    (∀ T, Bridge.Environment.capCount T = 2 ^ (T + 2)) ∧
    (∀ T, Nonempty (Bridge.Environment.E T)) ∧
    (∀ k, ∃ b : Bridge.Environment.E (k + 1),
      ∀ a : Bridge.Environment.E k,
        (some a : Bridge.Environment.E (k + 1)) ≠ b) ∧
    Bridge.Alphabet.Kmin = 2 :=
  Bridge.Environment.environment_universality

/-- T-2 factorisation: namer-shaped positive + carrier obstruction. -/
theorem milestone_M4b :
    (∀ {S E : Type} {U : S × E → S × E},
      Geom.Registration.Inj U →
      ∀ w : Bridge.Environment.TwoMerge S E U,
        Bridge.RegistrationFactor.outsideSingleton
          (Bridge.Environment.recordLabel w false)
          (Bridge.Environment.recordLabel w true)) ∧
    (Geom.Registration.Inj Geom.Registration.swapStep ∧
      Geom.Registration.Merges Geom.Registration.swapStep ∧
      Geom.Registration.Registers Geom.Registration.swapStep) ∧
    (∀ T, 1 ≤ T → Density.levelCard 0 < Density.levelCard T) ∧
    (¬ Geom.Registration.Merges Geom.Registration.oscStep) :=
  Bridge.RegistrationFactor.registration_naming_factorisation

theorem milestone_T10 :
    (∀ {K : Nat}, 2 ≤ K → ∀ tTurn,
      Geom.Profile.IsExhaustionTick K (Geom.Profile.bounce tTurn) tTurn) ∧
    Bridge.Alphabet.Kmin = 2 :=
  ⟨fun hK tTurn => Bridge.ArchiveMustSpeak.page_time_is_exhaustion hK tTurn,
   Bridge.Alphabet.Kmin_eq⟩

theorem milestone_T11 :
    (∀ {S E : Type} {U : S × E → S × E},
      Geom.Registration.Inj U →
      Geom.Registration.Merges U →
      Geom.Registration.Registers U) ∧
    (∀ k : Nat, ¬ ∃ (f : Ladder.Level (k + 1) → Ladder.Level k),
      ∀ x y, f x = f y → x = y) ∧
    Bridge.Alphabet.Kmin = 2 :=
  ⟨fun hU hm => Bridge.SecondLaw.landauer hU hm,
   Bridge.SecondLaw.archive_irreversible,
   Bridge.Alphabet.Kmin_eq⟩

theorem milestone_T12 :
    (∀ k (f : Ladder.Level k → Ladder.Level k → Bool),
      ∃ e₁ e₂ : Branch.Predicate k,
        Branch.IsEscape k f e₁ ∧ Branch.IsEscape k f e₂ ∧
          ∃ x, e₁ x ≠ e₂ x) ∧
    Bridge.Alphabet.Kmin = 2 :=
  ⟨Bridge.Measurement.two_children, Bridge.Alphabet.Kmin_eq⟩

theorem milestone_T13 :
    (∀ T, Bridge.Expansion.countedVolume 2 (T + 1) =
      2 * Bridge.Expansion.countedVolume 2 T) ∧
    (∀ T, Bridge.Expansion.countedVolume Bridge.Alphabet.Kmin T = 2 ^ T) ∧
    Bridge.Expansion.NumberEqualsVolume ∧
    Bridge.Alphabet.Kmin = 2 :=
  ⟨Bridge.Expansion.discrete_Hubble_one_bit_per_tick,
   Bridge.Expansion.counted_deSitter_volume,
   Bridge.Expansion.number_equals_volume_flagged,
   Bridge.Alphabet.Kmin_eq⟩

theorem milestone_T14 :
    Bridge.Forman.StrictlyNegative
      (Bridge.Forman.internalDeg 2) (Bridge.Forman.internalDeg 2) ∧
    (∀ faces, Bridge.Forman.quantity faces <
      Bridge.Forman.quantity (faces + 1)) ∧
    ¬ Bridge.Forman.StrictlyNegativeFaced 3 3 2 ∧
    Bridge.Alphabet.Kmin = 2 :=
  ⟨Bridge.Forman.internal_edge_forman_neg,
   Bridge.Forman.recombination_raises_quantity,
   Bridge.Forman.internal_not_neg_at_two_faces,
   Bridge.Alphabet.Kmin_eq⟩

theorem bridge_arc :
    Bridge.Alphabet.Kmin = 2 ∧
    (∀ T, Bridge.Capacity.caps T = 2 ^ (T + 2)) ∧
    (∀ {S E : Type} {U : S × E → S × E},
      Geom.Registration.Inj U →
      Geom.Registration.Merges U →
      Geom.Registration.Registers U) ∧
    (∀ f : Bridge.OneZ2.Face, ∀ b : Bridge.OneZ2.Z2,
      Bridge.OneZ2.project f (Bridge.OneZ2.project f b) = b) ∧
    (∀ {S E : Type} {U : S × E → S × E},
      Geom.Registration.Inj U →
      ∀ w : Bridge.Environment.TwoMerge S E U,
        Bridge.RegistrationFactor.outsideSingleton
          (Bridge.Environment.recordLabel w false)
          (Bridge.Environment.recordLabel w true)) ∧
    (∀ T, 1 ≤ T → Density.levelCard 0 < Density.levelCard T) ∧
    (∀ {K : Nat}, 2 ≤ K → ∀ tTurn,
      Geom.Profile.IsExhaustionTick K (Geom.Profile.bounce tTurn) tTurn) ∧
    (∀ k : Nat, ¬ ∃ (f : Ladder.Level (k + 1) → Ladder.Level k),
      ∀ x y, f x = f y → x = y) ∧
    (∀ k (f : Ladder.Level k → Ladder.Level k → Bool),
      ∃ e₁ e₂ : Branch.Predicate k,
        Branch.IsEscape k f e₁ ∧ Branch.IsEscape k f e₂ ∧
          ∃ x, e₁ x ≠ e₂ x) ∧
    (∀ T, Bridge.Expansion.countedVolume 2 (T + 1) =
      2 * Bridge.Expansion.countedVolume 2 T) ∧
    Bridge.Forman.StrictlyNegative
      (Bridge.Forman.internalDeg 2) (Bridge.Forman.internalDeg 2) :=
  ⟨Bridge.Alphabet.Kmin_eq,
   Bridge.Capacity.caps_eq,
   fun hU hm => Bridge.RegistrationSpine.ag_merge_registers hU hm,
   Bridge.OneZ2.project_involution,
   fun hU w => (Bridge.RegistrationFactor.registers_admits_namer hU w).1,
   fun T hT =>
     (Bridge.RegistrationFactor.registration_vs_naming_obstruction).2.2.2 T hT,
   fun hK tTurn => Bridge.ArchiveMustSpeak.page_time_is_exhaustion hK tTurn,
   Bridge.SecondLaw.archive_irreversible,
   Bridge.Measurement.two_children,
   Bridge.Expansion.discrete_Hubble_one_bit_per_tick,
   Bridge.Forman.internal_edge_forman_neg⟩

#print axioms milestone_M1
#print axioms milestone_M4b
#print axioms milestone_T10
#print axioms milestone_T11
#print axioms milestone_T12
#print axioms milestone_T13
#print axioms milestone_T14
#print axioms bridge_arc

end Bridge.Arc
