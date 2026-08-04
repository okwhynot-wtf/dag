import Alphabet
import Capacity
import Measurement
import Branch
import Forman

/-!
# T-12 measure fragment — uniform weight vs no asymmetric selector

T-12 supplies ≥2 escapes and no selection mechanism. Two Lean-shaped
successors:

1. **Positive.** Capacity / `Kmin` counting induces a uniform weight on the
   two children: each escape gets weight 1; total weight = `Kmin`.
2. **Negative.** No law-derived selector can pick a unique preferred escape
   for every reading (underdetermination always supplies another).

Born rule / continuum probability remain refused. The uniform weight is a
record-multiplicity caricature, not Hilbert-space amplitude.

Finite Ollivier-style trial (below): counting transport on the Kmin tree
with uniform child masses. Continuum / measure-theoretic Ollivier–Ricci
stays refused (Forman fence).
-/

namespace Bridge.BranchMeasure

open Bridge.Measurement

/-- Uniform escape weight from capacity counting (one unit per child). -/
def escapeWeight {k : Nat} (_e : Branch.Predicate k) : Nat := 1

/-- Total weight on the two T-12 children equals `Kmin`. -/
theorem uniform_total_is_Kmin (k : Nat)
    (f : Ladder.Level k → Ladder.Level k → Bool) :
    ∃ e₁ e₂ : Branch.Predicate k,
      Branch.IsEscape k f e₁ ∧ Branch.IsEscape k f e₂ ∧
        (∃ x, e₁ x ≠ e₂ x) ∧
        escapeWeight e₁ + escapeWeight e₂ = Bridge.Alphabet.Kmin := by
  obtain ⟨e₁, e₂, h₁, h₂, hne⟩ := two_children k f
  refine ⟨e₁, e₂, h₁, h₂, hne, ?_⟩
  simp only [escapeWeight, Bridge.Alphabet.Kmin_eq]

/-- Law-symmetric: uniform weights cannot break the T-12 tie. -/
theorem uniform_weights_equal {k : Nat}
    (e₁ e₂ : Branch.Predicate k) :
    escapeWeight e₁ = escapeWeight e₂ :=
  rfl

/-- A selector tries to return one preferred escape from the reading alone. -/
structure EscapeSelector where
  select : (k : Nat) → (Ladder.Level k → Ladder.Level k → Bool) →
    Branch.Predicate k
  is_escape :
    ∀ k f, Branch.IsEscape k f (select k f)

/-- **No-go.** No selector is unique: underdetermination always supplies a
    distinct second escape. -/
theorem no_unique_law_selector (σ : EscapeSelector) (k : Nat)
    (f : Ladder.Level k → Ladder.Level k → Bool) :
    ∃ e : Branch.Predicate k,
      Branch.IsEscape k f e ∧ ∃ x, e x ≠ (σ.select k f) x := by
  obtain ⟨e₁, e₂, h₁, h₂, x, hx⟩ := two_children k f
  by_cases h : e₁ x = σ.select k f x
  · refine ⟨e₂, h₂, x, ?_⟩
    intro h2
    exact hx (h.trans h2.symm)
  · exact ⟨e₁, h₁, x, h⟩

/-- Capacity schedule does not break branch symmetry: `|caps|` depends on
    `T` alone; escape weights stay equal. -/
theorem caps_blind_to_escape (T : Nat)
    (e₁ e₂ : Branch.Predicate T) :
    escapeWeight e₁ = escapeWeight e₂ ∧
    Bridge.Capacity.caps T = 2 ^ (T + 2) :=
  ⟨uniform_weights_equal e₁ e₂, Bridge.Capacity.caps_eq T⟩

/-- **T-12 measure package.** Uniform child weights from `Kmin`;
    no unique law-derived selector; caps blind to escape choice.
    Asymmetric Born-from-underdetermination alone remains refused. -/
theorem T12_measure_fragment :
    (∀ k f, ∃ e₁ e₂ : Branch.Predicate k,
      Branch.IsEscape k f e₁ ∧ Branch.IsEscape k f e₂ ∧
        (∃ x, e₁ x ≠ e₂ x) ∧
        escapeWeight e₁ + escapeWeight e₂ = Bridge.Alphabet.Kmin) ∧
    (∀ (σ : EscapeSelector) k f,
      ∃ e : Branch.Predicate k,
        Branch.IsEscape k f e ∧ ∃ x, e x ≠ (σ.select k f) x) ∧
    Bridge.Alphabet.Kmin = 2 :=
  ⟨uniform_total_is_Kmin,
   fun σ k f => no_unique_law_selector σ k f,
   Bridge.Alphabet.Kmin_eq⟩

/-! ## Finite Ollivier-style trial (counting transport) -/

/-- Combinatorial sibling distance via the parent (two edges). -/
def siblingDist : Nat := 2

/-- Parent–child distance on the branch tree. -/
def parentChildDist : Nat := 1

/-- Counting transport cost between two distinct uniform escape masses
    on the same parent: move mass 1 across `siblingDist`. -/
def siblingTransportCost {k : Nat}
    (e₁ e₂ : Branch.Predicate k) (_hne : ∃ x, e₁ x ≠ e₂ x) : Nat :=
  escapeWeight e₁ * siblingDist

theorem sibling_transport_cost_pos {k : Nat}
    (e₁ e₂ : Branch.Predicate k) (hne : ∃ x, e₁ x ≠ e₂ x) :
    1 ≤ siblingTransportCost e₁ e₂ hne := by
  simp [siblingTransportCost, escapeWeight, siblingDist]

/-- Ollivier-style curvature caricature on a parent–child edge:
    `κ ~ 1 - W/d` with `d = 1` and `W` at least the sibling-transport
    lower bound when comparing uniform child masses. With `W ≥ 2` and
    `d = 1` the Nat difference `d - W` underflows toward negativity —
    recorded as `W ≥ d` (non-positive curvature signal). -/
theorem ollivier_nonpos_signal {k : Nat}
    (e₁ e₂ : Branch.Predicate k) (hne : ∃ x, e₁ x ≠ e₂ x) :
    parentChildDist ≤ siblingTransportCost e₁ e₂ hne := by
  simp [parentChildDist, siblingTransportCost, escapeWeight, siblingDist]

/-- Uniform child masses do not flatten Forman negativity without faces. -/
theorem uniform_mass_preserves_forman_neg :
    Bridge.Forman.StrictlyNegative
      (Bridge.Forman.internalDeg Bridge.Alphabet.Kmin)
      (Bridge.Forman.internalDeg Bridge.Alphabet.Kmin) :=
  Bridge.Forman.internal_edge_forman_neg

/-- Continuum / measure-theoretic Ollivier remains refused. -/
def continuum_ollivier_refused : True := True.intro

/-- Two T-12 children with uniform mass and non-positive Ollivier signal. -/
theorem ollivier_children (k : Nat)
    (f : Ladder.Level k → Ladder.Level k → Bool) :
    ∃ e₁ e₂ : Branch.Predicate k,
      Branch.IsEscape k f e₁ ∧ Branch.IsEscape k f e₂ ∧
        (∃ x, e₁ x ≠ e₂ x) ∧
        escapeWeight e₁ + escapeWeight e₂ = Bridge.Alphabet.Kmin ∧
        parentChildDist ≤ escapeWeight e₁ * siblingDist := by
  obtain ⟨e₁, e₂, h₁, h₂, hne⟩ := two_children k f
  refine ⟨e₁, e₂, h₁, h₂, hne, ?_, ?_⟩
  · simp only [escapeWeight, Bridge.Alphabet.Kmin_eq]
  · simp [parentChildDist, escapeWeight, siblingDist]

/-- **Finite Ollivier trial.** Uniform T-12 child weights + counting
    sibling transport give a non-positive curvature signal on the Kmin
    tree; Forman negativity is unchanged without faces. Continuum
    Ollivier stays refused. -/
theorem ollivier_trial_fragment :
    (∀ k f, ∃ e₁ e₂ : Branch.Predicate k,
      Branch.IsEscape k f e₁ ∧ Branch.IsEscape k f e₂ ∧
        (∃ x, e₁ x ≠ e₂ x) ∧
        escapeWeight e₁ + escapeWeight e₂ = Bridge.Alphabet.Kmin ∧
        parentChildDist ≤ escapeWeight e₁ * siblingDist) ∧
    Bridge.Forman.StrictlyNegative
      (Bridge.Forman.internalDeg Bridge.Alphabet.Kmin)
      (Bridge.Forman.internalDeg Bridge.Alphabet.Kmin) ∧
    continuum_ollivier_refused = True.intro ∧
    Bridge.Alphabet.Kmin = 2 :=
  ⟨ollivier_children, uniform_mass_preserves_forman_neg,
   rfl, Bridge.Alphabet.Kmin_eq⟩

#print axioms uniform_total_is_Kmin
#print axioms no_unique_law_selector
#print axioms T12_measure_fragment
#print axioms ollivier_nonpos_signal
#print axioms ollivier_trial_fragment

end Bridge.BranchMeasure

