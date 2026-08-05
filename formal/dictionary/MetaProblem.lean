import Certificate
import KernelAdmit
import Interior
import Observer
import Ladder
import Diagonal
import TwoCycle
import Alphabet
import SelfReference

/-!
# Meta-problem entry — Chalmers's meta-problem

Dictionary filing for the meta-problem: why physical systems report an
explanatory gap (ineffability, self-opacity). Qualia / the hard problem
(why there is something it is like) are not claimed in this module;
Interior results entail nothing about phenomenal character.

The interior triad supplies the report skeleton:

  Self-opacity      — every live self-reading misses a definite predicate
  Outdated portrait — every self-model is stale by the time it is held
  Restless signature — no tracked self-ascription stabilises

Quantitative spine columns (`SelfReference`) — deficit count, lag theorem,
`corpus_not_universal` — give the triad at measure grade. Systems for
which these hold report ineffability and incompleteness on structural
grounds. `observers_forced` supplies forced +1: thin observers instantiate
at every ladder level.
-/

namespace Dictionary.MetaProblem

open Bridge.KernelAdmit
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
  fixedMode := FixedMode.emptyLocus
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
    metaCert.fixedMode = FixedMode.emptyLocus ∧
    (∀ a : Ladder.Level k,
      Ladder.rep (k + 1) none (some a) = !(Ladder.rep k a a)) ∧
    Bridge.Alphabet.Kmin = 2 :=
  ⟨reports_opacity k, reports_outdated k,
   fun S E hT hA htr => reports_restless S E hT hA htr,
   meta_fixed_empty, rfl,
   (Observer.observers_forced k).1,
   Bridge.Alphabet.Kmin_eq⟩

/-- Reports of ineffability are theorem-shaped behaviour of any live
    self-representing ladder system. -/
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

/-- MetaProblem triad columns filled quantitatively by `SelfReference`
    (deficit / lag / corpus_not_universal). -/
theorem meta_quantitative (k : Nat) :
    (¬ Interior.Articulates (Ladder.rep k)
      (Diagonal.dodge (Ladder.rep k))) ∧
    (SelfReference.unsayable (k + Density.predicateCount k) >
      Density.predicateCount k) ∧
    (SelfReference.unsayable k <
      SelfReference.unsayable (k + Density.predicateCount k)) ∧
    Density.levelCard k < Density.predicateCount k :=
  let m := SelfReference.meta_triad_quantitative k
  ⟨m.1, m.2.1, m.2.2.1, (SelfReference.deficit_count k).2.2.1⟩

/-- Corpus-level incompleteness as dictionary-facing fact. -/
theorem corpus_incomplete :
    (∀ k (r : SelfReference.SelfReading k),
      ¬ Diagonal.PointSurjective r) ∧
    (∀ k, SelfReference.unsayable k <
      SelfReference.unsayable (k + Density.predicateCount k)) ∧
    (∀ k, ¬ ∃ (f : Limit.LevelOmega → Ladder.Level k),
      ∀ x y, f x = f y → x = y) :=
  ⟨fun k r => SelfReference.incompleteness_unconditional k r,
   SelfReference.lag_recedes,
   OmegaDuration.omega_not_a_rung⟩

#print axioms ineffability_shape
#print axioms meta_admitted
#print axioms reports_are_structural
#print axioms thin_observers_forced
#print axioms meta_quantitative
#print axioms corpus_incomplete

end Dictionary.MetaProblem
