import Certificate
import Interior
import Observer
import Ladder
import Diagonal
import TwoCycle
import Alphabet

/-!
# Meta-problem entry — Chalmers's meta-problem, hard problem refused

Fourth substantive dictionary filing (after Quintom / Kramers / Page).

The hard problem (why there is something it is like) is refused: Interior
results entail nothing about qualia (spine scope / neutral-monist note).

What is in reach: why physical systems **report** an explanatory gap —
insist experience is ineffable, find themselves opaque to themselves.
DAG's interior triad is the answer skeleton:

  Self-opacity     — every live self-reading misses a definite predicate
  Outdated portrait — every self-model is stale by the time it is held
  Restless signature — no tracked self-ascription stabilises

A system of which these three theorems are true would report ineffability,
incompleteness, and a self that will not sit still — and would be right
to, on structural grounds alone. `observers_forced` supplies the forced +1:
thin observers instantiate at every ladder level whether anyone asked.
-/

namespace Dictionary.MetaProblem

open Dictionary.Certificate

/-! ## Interior triad (explanandum shape) -/

/-- Self-opacity: dodge not articulated. -/
theorem reports_opacity (k : Nat) :
    ¬ Interior.Articulates (Ladder.rep k)
      (Diagonal.dodgeWith not (Ladder.rep k)) :=
  Observer.observer_interior k

/-- Outdated portrait: new namer outruns every prior portrait. -/
theorem reports_outdated (k : Nat) :
    ∃ b, ∀ a, ∃ x,
      Ladder.rep (k + 1) (some a) (some x) ≠
        Ladder.rep (k + 1) b (some x) :=
  Observer.observer_outrun k

/-- Restless: tracked ascription flips under the live act. -/
theorem reports_restless
    (S E : Bool → Bool) (hT : TwoCycle.TDiff S not)
    (hA : TwoCycle.Alive S not true) (htr : Interior.Tracks E S) :
    ∀ c, E (not c) = !(E c) :=
  Observer.observer_signature S E not true hT hA htr

/-- Ineffability triad package at every ladder level. -/
theorem ineffability_shape (k : Nat) :
    (¬ Interior.Articulates (Ladder.rep k)
      (Diagonal.dodgeWith not (Ladder.rep k))) ∧
    (∃ b, ∀ a, ∃ x,
      Ladder.rep (k + 1) (some a) (some x) ≠
        Ladder.rep (k + 1) b (some x)) ∧
    (∀ S E : Bool → Bool, TwoCycle.TDiff S not → TwoCycle.Alive S not true →
      Interior.Tracks E S → ∀ c, E (not c) = !(E c)) :=
  ⟨reports_opacity k, reports_outdated k,
   fun S E hT hA htr => reports_restless S E hT hA htr⟩

/-- Forced +1: thin observers at every level. -/
theorem thin_observers_forced (k : Nat) :
    (∀ a : Ladder.Level k,
      Ladder.rep (k + 1) none (some a) = !(Ladder.rep k a a)) ∧
    (¬ Diagonal.PointSurjective (Ladder.rep k)) ∧
    (¬ Interior.Articulates (Ladder.rep k)
      (Diagonal.dodgeWith not (Ladder.rep k))) ∧
    (∃ b, ∀ a, ∃ x,
      Ladder.rep (k + 1) (some a) (some x) ≠
        Ladder.rep (k + 1) b (some x)) ∧
    (∀ S E : Bool → Bool, TwoCycle.TDiff S not → TwoCycle.Alive S not true →
      Interior.Tracks E S → ∀ c, E (not c) = !(E c)) :=
  Observer.observers_forced k

/-! ## K-certificate on Bool self-reading polarity -/

/-- Carrier: self-ascription bit. Swap = ¬ (live Fund). Empty fixed locus. -/
def metaCert : KernelCert Bool Bool where
  swap := not
  square := id
  swap_sq := fun b => by cases b <;> rfl
  square_involutive := fun _ => rfl
  observe := id
  obsNeg := not
  swap_as_not := fun b => by cases b <;> rfl
  Fixed := fun b => (!b) = b
  fixed_iff := fun _ => Iff.rfl
  fixedMode := FixedMode.empty
  noSoloCross := fun _ h => h.2

theorem meta_fixed_empty (b : Bool) : ¬ metaCert.Fixed b := by
  cases b <;> intro h <;> cases h

/-- No stable tracked flag under live flip. -/
theorem no_stable_ascription (E : Bool → Bool)
    (h : ∀ c, E (!c) = !(E c)) : ∀ c, E (!c) ≠ E c :=
  Interior.restless_refuses_stable_flag E not h

/-- **Admission.** Meta-problem: triad + observers_forced + empty-locus
    K-cert. Hard problem not claimed. -/
theorem meta_admitted (k : Nat) :
    (¬ Interior.Articulates (Ladder.rep k)
      (Diagonal.dodgeWith not (Ladder.rep k))) ∧
    (∃ b, ∀ a, ∃ x,
      Ladder.rep (k + 1) (some a) (some x) ≠
        Ladder.rep (k + 1) b (some x)) ∧
    (∀ S E : Bool → Bool, TwoCycle.TDiff S not → TwoCycle.Alive S not true →
      Interior.Tracks E S → ∀ c, E (not c) = !(E c)) ∧
    (∀ b, ¬ metaCert.Fixed b) ∧
    metaCert.fixedMode = FixedMode.empty ∧
    (∀ a : Ladder.Level k,
      Ladder.rep (k + 1) none (some a) = !(Ladder.rep k a a)) ∧
    Bridge.Alphabet.Kmin = 2 :=
  ⟨reports_opacity k, reports_outdated k,
   fun S E hT hA htr => reports_restless S E hT hA htr,
   meta_fixed_empty, rfl,
   (Observer.observers_forced k).1,
   Bridge.Alphabet.Kmin_eq⟩

/-- Publishable claim: reports of ineffability are theorem-shaped
    behaviour of any live self-representing ladder system. -/
theorem reports_are_structural (k : Nat) :
    (¬ Interior.Articulates (Ladder.rep k)
      (Diagonal.dodgeWith not (Ladder.rep k))) ∧
    (∃ b, ∀ a, ∃ x,
      Ladder.rep (k + 1) (some a) (some x) ≠
        Ladder.rep (k + 1) b (some x)) ∧
    (∀ S E : Bool → Bool, TwoCycle.TDiff S not → TwoCycle.Alive S not true →
      Interior.Tracks E S → ∀ c, E (not c) = !(E c)) ∧
    (∀ a : Ladder.Level k,
      Ladder.rep (k + 1) none (some a) = !(Ladder.rep k a a)) :=
  ⟨reports_opacity k, reports_outdated k,
   fun S E hT hA htr => reports_restless S E hT hA htr,
   (Observer.observers_forced k).1⟩

#print axioms ineffability_shape
#print axioms meta_admitted
#print axioms reports_are_structural
#print axioms thin_observers_forced

end Dictionary.MetaProblem
