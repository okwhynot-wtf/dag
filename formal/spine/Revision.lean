import Ladder
import TwoCycle

/-!
# Revision — comparative bridge to revision theory

An exhibit in the register of `Faces`: the two-cycle is a period-2
revision sequence for the liar, and ladder ticks correspond to revision
stages with conservative lifts playing the role of persistence of settled
values. Nothing about truth is axiomatised.

* **Liar revision** (`LiarRevision`, `liar_revision_is_orbit`): sequences
  `s` with `s (n+1) = ¬ s n` are exactly the orbits of `not` on Bool.
* **Period two** (`revision_period_two`): every such sequence has period 2.
* **Ladder correspondence** (`tick_is_revision_step`,
  `settled_values_persist`): each naming tick is a revision stage; lifts
  conserve prior readings.
-/
namespace Revision

/-- A liar-revision sequence: each stage negates the previous. -/
def LiarRevision (s : Nat → Bool) : Prop :=
  ∀ n, s (n + 1) = !(s n)

/-- The orbit of a Bool under `not`. -/
def orbitOf (b : Bool) : Nat → Bool
  | 0 => b
  | n + 1 => !(orbitOf b n)

theorem orbitOf_revision (b : Bool) : LiarRevision (orbitOf b) := by
  intro n
  rfl

/-- Every liar-revision sequence is the `not`-orbit of its value at 0. -/
theorem liar_revision_is_orbit (s : Nat → Bool) (hs : LiarRevision s) :
    ∀ n, s n = orbitOf (s 0) n := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [hs n, ih]
    rfl

/-- Liar-revision sequences are exactly the orbits of the canonical
    fundamental act `not`. -/
theorem revision_iff_orbit (s : Nat → Bool) :
    LiarRevision s ↔ ∃ b, ∀ n, s n = orbitOf b n := by
  constructor
  · intro hs
    exact ⟨s 0, liar_revision_is_orbit s hs⟩
  · intro ⟨b, hb⟩
    intro n
    rw [hb (n + 1), hb n]
    rfl

/-- Period two: `s (n+2) = s n`. -/
theorem revision_period_two (s : Nat → Bool) (hs : LiarRevision s) :
    ∀ n, s (n + 2) = s n := by
  intro n
  rw [hs (n + 1), hs n]
  cases s n <;> rfl

/-- The two-cycle package specialises to revision period two on Bool. -/
theorem two_cycle_is_revision :
    LiarRevision (orbitOf false) ∧ LiarRevision (orbitOf true) ∧
      (∀ n, orbitOf false (n + 2) = orbitOf false n) ∧
      (∀ n, orbitOf true (n + 2) = orbitOf true n) :=
  ⟨orbitOf_revision false, orbitOf_revision true,
   revision_period_two _ (orbitOf_revision false),
   revision_period_two _ (orbitOf_revision true)⟩

/-! ## Ladder as revision stages -/

/-- At each tick the committed ladder names the negation of the present
    diagonal — one revision step relative to the prior self-reading. -/
theorem tick_is_revision_step (k : Nat) (a : Ladder.Level k) :
    Ladder.rep (k + 1) none (some a) = !(Ladder.rep k a a) :=
  rfl

/-- Settled (embedded) values persist under later lifts. -/
theorem settled_values_persist (k j : Nat) (x y : Ladder.Level k) :
    Ladder.rep (k + j) (Ladder.lift k j x) (Ladder.lift k j y) =
      Ladder.rep k x y :=
  Ladder.lift_conservative k j x y

/-- Comparative package: orbit identification and ladder correspondence. -/
theorem revision_package :
    (∀ s, LiarRevision s ↔ ∃ b, ∀ n, s n = orbitOf b n) ∧
    (∀ s, LiarRevision s → ∀ n, s (n + 2) = s n) ∧
    (∀ k a, Ladder.rep (k + 1) none (some a) = !(Ladder.rep k a a)) ∧
    (∀ k j x y, Ladder.rep (k + j) (Ladder.lift k j x) (Ladder.lift k j y) =
      Ladder.rep k x y) :=
  ⟨revision_iff_orbit, revision_period_two, tick_is_revision_step,
   settled_values_persist⟩

#print axioms Revision.liar_revision_is_orbit
#print axioms Revision.revision_iff_orbit
#print axioms Revision.revision_period_two
#print axioms Revision.two_cycle_is_revision
#print axioms Revision.tick_is_revision_step
#print axioms Revision.settled_values_persist
#print axioms Revision.revision_package

end Revision
