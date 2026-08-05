import Branch
import Cause
import Ladder
import Orbit
import Alphabet

/-!
# T-12 Branch nondeterminism (measurement shape)

The branch layer already has the uncanny shape of the measurement
problem: ascent is necessary and direction is free; every node has at
least two children; distinct escapes diverge histories; nothing in the
law selects among them. That is an Everett-flavoured object with
underdetermination as the formal statement of why no mechanism of
selection appears.

Born from multiplicity alone is a theorem
(`BranchMeasure.born_from_multiplicity_nogo`); continuum probability /
preferred basis are not derived (no Hilbert measure; density readings cut).
-/

namespace Bridge.BranchNondeterminism

/-- Every node has ≥2 distinct permitted escapes (children). -/
theorem two_children (k : Nat)
    (f : Ladder.Level k → Ladder.Level k → Bool) :
    ∃ e₁ e₂ : Branch.Predicate k,
      Branch.IsEscape k f e₁ ∧ Branch.IsEscape k f e₂ ∧
        ∃ x, e₁ x ≠ e₂ x :=
  Branch.branch_nonempty k f

/-- Ascent necessary, direction free. -/
theorem ascent_free (k : Nat)
    (f : Ladder.Level k → Ladder.Level k → Bool) :
    Branch.Nec ⟨f⟩ (fun n' => ¬ Diagonal.PointSurjective n'.reading) ∧
    ∃ e₁ e₂ : Branch.Predicate k,
      Branch.IsEscape k f e₁ ∧ Branch.IsEscape k f e₂ ∧
        (∃ x, e₁ x ≠ e₂ x) ∧
        Branch.Poss ⟨f⟩ (fun n' =>
          ∀ a, n'.reading none (some a) = e₁ a) ∧
        Branch.Poss ⟨f⟩ (fun n' =>
          ∀ a, n'.reading none (some a) = e₂ a) :=
  Branch.ascent_necessary_direction_free k f

/-- Distinct escapes diverge named history. -/
theorem histories_diverge (k : Nat)
    (f : Ladder.Level k → Ladder.Level k → Bool)
    (e₁ e₂ : Branch.Predicate k) (hne : ∃ x, e₁ x ≠ e₂ x) :
    ∃ x : Ladder.Level k,
      (Branch.childOf ⟨f⟩ e₁).reading none (some x) ≠
        (Branch.childOf ⟨f⟩ e₂).reading none (some x) :=
  Branch.paths_diverge k f e₁ e₂ hne

/-- No law selects: underdetermination supplies ≥2 escapes, both possible. -/
theorem no_selection_mechanism (k : Nat)
    (f : Ladder.Level k → Ladder.Level k → Bool) :
    ∃ e₁ e₂ : Branch.Predicate k,
      Branch.IsEscape k f e₁ ∧ Branch.IsEscape k f e₂ ∧
        (∃ x, e₁ x ≠ e₂ x) ∧
        Branch.Poss ⟨f⟩ (fun n' =>
          ∀ a, n'.reading none (some a) = e₁ a) ∧
        Branch.Poss ⟨f⟩ (fun n' =>
          ∀ a, n'.reading none (some a) = e₂ a) ∧
        Branch.Nec ⟨f⟩ (fun n' => ¬ Diagonal.PointSurjective n'.reading) := by
  obtain ⟨hNec, e₁, e₂, h₁, h₂, hne, p₁, p₂⟩ := ascent_free k f
  exact ⟨e₁, e₂, h₁, h₂, hne, p₁, p₂, hNec⟩

/-- **T-12.** Measurement / outcome-selection package (shape only). -/
theorem T12_branch_nondeterminism :
    (∀ k (f : Ladder.Level k → Ladder.Level k → Bool),
      ∃ e₁ e₂ : Branch.Predicate k,
        Branch.IsEscape k f e₁ ∧ Branch.IsEscape k f e₂ ∧
          ∃ x, e₁ x ≠ e₂ x) ∧
    (∀ k (f : Ladder.Level k → Ladder.Level k → Bool),
      Branch.Nec ⟨f⟩ (fun n' => ¬ Diagonal.PointSurjective n'.reading) ∧
      ∃ e₁ e₂ : Branch.Predicate k,
        Branch.IsEscape k f e₁ ∧ Branch.IsEscape k f e₂ ∧
          (∃ x, e₁ x ≠ e₂ x) ∧
          Branch.Poss ⟨f⟩ (fun n' =>
            ∀ a, n'.reading none (some a) = e₁ a) ∧
          Branch.Poss ⟨f⟩ (fun n' =>
            ∀ a, n'.reading none (some a) = e₂ a)) ∧
    Bridge.Alphabet.Kmin = 2 :=
  ⟨two_children, ascent_free, Bridge.Alphabet.Kmin_eq⟩

#print axioms two_children
#print axioms ascent_free
#print axioms histories_diverge
#print axioms no_selection_mechanism
#print axioms T12_branch_nondeterminism

end Bridge.BranchNondeterminism
