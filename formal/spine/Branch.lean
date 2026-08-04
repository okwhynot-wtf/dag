import Cause

/-!
# Branch — escape tree and derived modality

The committed ladder names the Lawvere dodge at every tick. Underdetermination
supplies at least two escapes at every level; this module organises the
permitted naming extensions as a tree and states necessity/possibility
extensionally over its children.

* **Escapes** (`IsEscape`, `escapeSet_two`, `branch_nonempty`): predicates
  omitted by a level's self-reading; at least two distinct witnesses.
* **Paths** (`Path`, `Path.rep`, `Path.WF`): infinite well-formed histories
  through the tree (escape choice only; free values fixed `false`).
* **Committed path** (`committed`, `committed_is_path`): the existing
  ladder recovered as the all-dodge path.
* **Nodes and children** (`Node`, `childOf`): a node is a reading at
  level `k`; a child names one escape via `Cause.stepEsc`.
* **Modality** (`Nec`, `Poss`): universal/existential quantification over
  children, stated extensionally.
* **Package** (`seal_along_every_path`, `ascent_necessary_direction_free`,
  `paths_diverge`, `branch_package`).
-/
namespace Branch

/-- Predicate valued in Bool on `Ladder.Level k`. -/
abbrev Predicate (k : Nat) := Ladder.Level k → Bool

/-- `e` is an escape of reading `f`: no row of `f` equals `e`. -/
def IsEscape (k : Nat) (f : Ladder.Level k → Ladder.Level k → Bool)
    (e : Predicate k) : Prop :=
  ∀ a, ∃ x, f a x ≠ e x

/-- Escape set of `f`, as a predicate on predicates (extensional set). -/
def EscapeSet (k : Nat) (f : Ladder.Level k → Ladder.Level k → Bool)
    (e : Predicate k) : Prop :=
  IsEscape k f e

/-- Every reading at every level has at least two distinct escapes. -/
theorem escapeSet_two (k : Nat)
    (f : Ladder.Level k → Ladder.Level k → Bool) :
    ∃ e₁ e₂ : Predicate k,
      EscapeSet k f e₁ ∧ EscapeSet k f e₂ ∧ ∃ x, e₁ x ≠ e₂ x := by
  obtain ⟨e₁, e₂, hne, h₁, h₂⟩ := Ladder.underdetermined_at_level k f
  exact ⟨e₁, e₂, h₁, h₂, hne⟩

/-- Every node has at least two children (two distinct permitted escapes). -/
theorem branch_nonempty (k : Nat)
    (f : Ladder.Level k → Ladder.Level k → Bool) :
    ∃ e₁ e₂ : Predicate k,
      IsEscape k f e₁ ∧ IsEscape k f e₂ ∧ ∃ x, e₁ x ≠ e₂ x :=
  escapeSet_two k f

/-! ## Paths through the tree -/

/-- An infinite path: at each tick, a choice of escape of the present
    reading. Free values are fixed `false`. -/
structure Path where
  escape : (k : Nat) → (Ladder.Level k → Ladder.Level k → Bool) →
    Predicate k

/-- Underlying `Cause.Policy` (false frees). -/
def Path.toPolicy (π : Path) : Cause.Policy where
  oldOnNew := fun _ _ => false
  selfVal := fun _ => false
  escape := π.escape

/-- Reading along a path. -/
def Path.rep (π : Path) : (k : Nat) → Ladder.Level k → Ladder.Level k → Bool :=
  Cause.repP π.toPolicy

/-- Well-formedness: each chosen escape misses every row of the induced
    reading. -/
def Path.WF (π : Path) : Prop :=
  π.toPolicy.WF

/-- Every tick of a well-formed path is a naming extension. -/
theorem Path.step (π : Path) (hwf : π.WF) (k : Nat) :
    Tower.NamingExtension (π.rep k) (π.rep (k + 1)) some
      (π.escape k (π.rep k)) :=
  Cause.repP_step π.toPolicy hwf k

/-- The committed (all-dodge) path. -/
def committed : Path where
  escape := fun _ f x => !(f x x)

theorem committed_is_path : committed.WF :=
  Cause.dodgePolicy_wf

/-- The committed path reproduces `Ladder.rep`. -/
theorem committed_rep (k : Nat) :
    ∀ x y, committed.rep k x y = Ladder.rep k x y := by
  intro x y
  exact (Cause.ladder_is_default k x y).symm

/-- A history is a well-formed path through the escape tree. -/
def History := { π : Path // π.WF }

/-- The committed history. -/
def committedHistory : History := ⟨committed, committed_is_path⟩

/-! ## Nodes, children, modality -/

/-- A node at depth `k` is a Bool-valued self-reading of that level. -/
structure Node (k : Nat) where
  reading : Ladder.Level k → Ladder.Level k → Bool

/-- Node along a path at depth `k`. -/
def Path.node (π : Path) (k : Nat) : Node k :=
  ⟨π.rep k⟩

/-- Child of a node obtained by naming escape `e`. -/
def childOf {k : Nat} (n : Node k) (e : Predicate k) : Node (k + 1) where
  reading := Cause.stepEsc n.reading e

/-- Necessity at a node: `P` holds of every child naming a permitted
    escape. -/
def Nec {k : Nat} (n : Node k) (P : Node (k + 1) → Prop) : Prop :=
  ∀ e : Predicate k, IsEscape k n.reading e → P (childOf n e)

/-- Possibility at a node: `P` holds of some child naming a permitted
    escape. -/
def Poss {k : Nat} (n : Node k) (P : Node (k + 1) → Prop) : Prop :=
  ∃ e : Predicate k, IsEscape k n.reading e ∧ P (childOf n e)

/-! ## Theorems -/

/-- The seal holds at every depth of every well-formed path. -/
theorem seal_along_every_path (π : Path) (k : Nat) :
    ¬ Diagonal.PointSurjective (π.rep k) :=
  Diagonal.seal_bool (π.rep k)

/-- Modal form: at every node, every child is sealed (ascent necessary). -/
theorem nec_seal (k : Nat) (n : Node k) :
    Nec n (fun n' => ¬ Diagonal.PointSurjective n'.reading) := by
  intro e _he
  exact Diagonal.seal_bool (childOf n e).reading

/-- For each permitted escape there is a child naming it. -/
theorem escape_choice_possible (k : Nat)
    (f : Ladder.Level k → Ladder.Level k → Bool)
    (e : Predicate k) (he : IsEscape k f e) :
    Poss ⟨f⟩ (fun n' => ∀ a, n'.reading none (some a) = e a) :=
  ⟨e, he, fun _ => rfl⟩

theorem escape_not_necessary (k : Nat)
    (f : Ladder.Level k → Ladder.Level k → Bool)
    (e : Predicate k) :
    ¬ Nec ⟨f⟩ (fun n' => ∀ a, n'.reading none (some a) = e a) := by
  intro h
  obtain ⟨e₁, e₂, h₁, h₂, x, hx⟩ := branch_nonempty k f
  exact hx ((h e₁ h₁ x).trans (h e₂ h₂ x).symm)

theorem poss_without_nec (k : Nat)
    (f : Ladder.Level k → Ladder.Level k → Bool) :
    ∃ e₁ e₂ : Predicate k,
      IsEscape k f e₁ ∧ IsEscape k f e₂ ∧ (∃ x, e₁ x ≠ e₂ x) ∧
      Poss ⟨f⟩ (fun n' => ∀ a, n'.reading none (some a) = e₁ a) ∧
      ¬ Nec ⟨f⟩ (fun n' => ∀ a, n'.reading none (some a) = e₁ a) ∧
      Poss ⟨f⟩ (fun n' => ∀ a, n'.reading none (some a) = e₂ a) ∧
      ¬ Nec ⟨f⟩ (fun n' => ∀ a, n'.reading none (some a) = e₂ a) := by
  obtain ⟨e₁, e₂, h₁, h₂, hne⟩ := branch_nonempty k f
  exact ⟨e₁, e₂, h₁, h₂, hne,
    escape_choice_possible k f e₁ h₁,
    escape_not_necessary k f e₁,
    escape_choice_possible k f e₂ h₂,
    escape_not_necessary k f e₂⟩

/-- Ascent is necessary and direction is free: every child is sealed, and
    at least two distinct escapes are each possible. -/
theorem ascent_necessary_direction_free (k : Nat)
    (f : Ladder.Level k → Ladder.Level k → Bool) :
    Nec ⟨f⟩ (fun n' => ¬ Diagonal.PointSurjective n'.reading) ∧
    ∃ e₁ e₂ : Predicate k,
      IsEscape k f e₁ ∧ IsEscape k f e₂ ∧ (∃ x, e₁ x ≠ e₂ x) ∧
      Poss ⟨f⟩ (fun n' => ∀ a, n'.reading none (some a) = e₁ a) ∧
      Poss ⟨f⟩ (fun n' => ∀ a, n'.reading none (some a) = e₂ a) := by
  refine ⟨nec_seal k ⟨f⟩, ?_⟩
  obtain ⟨e₁, e₂, h₁, h₂, hne⟩ := branch_nonempty k f
  exact ⟨e₁, e₂, h₁, h₂, hne,
    escape_choice_possible k f e₁ h₁,
    escape_choice_possible k f e₂ h₂⟩

/-- Distinct escapes at a node yield successor readings that disagree on
    named content at `none` over the common past embedding `some`. -/
theorem paths_diverge (k : Nat)
    (f : Ladder.Level k → Ladder.Level k → Bool)
    (e₁ e₂ : Predicate k) (hne : ∃ x, e₁ x ≠ e₂ x) :
    ∃ x : Ladder.Level k,
      (childOf ⟨f⟩ e₁).reading none (some x) ≠
        (childOf ⟨f⟩ e₂).reading none (some x) := by
  obtain ⟨x, hx⟩ := hne
  exact ⟨x, hx⟩

/-- Stronger divergence: the successor readings are unequal as functions
    on the embedded past (named content), so no identification of the two
    children that preserves named values over `some` can hold. -/
theorem paths_diverge_no_past_agree (k : Nat)
    (f : Ladder.Level k → Ladder.Level k → Bool)
    (e₁ e₂ : Predicate k) (hne : ∃ x, e₁ x ≠ e₂ x) :
    ¬ (∀ x : Ladder.Level k,
        (childOf ⟨f⟩ e₁).reading none (some x) =
          (childOf ⟨f⟩ e₂).reading none (some x)) := by
  intro h
  obtain ⟨x, hx⟩ := paths_diverge k f e₁ e₂ hne
  exact hx (h x)

/-- Two well-formed paths diverge at tick `k+1` (rephrasing
    `Cause.escapes_differ_at` in path vocabulary). -/
theorem paths_from_underdetermination (k : Nat) :
    ∃ π π' : Cause.Policy, π.WF ∧ π'.WF ∧
      ∃ x : Ladder.Level k,
        Cause.repP π (k + 1) none (some x) ≠
          Cause.repP π' (k + 1) none (some x) :=
  Cause.escapes_differ_at k

/-! ## Summary -/

/-- Branch package: nonempty branching, committed path, seal on all paths,
    ascent necessary and direction free, and divergent children. -/
theorem branch_package :
    (∀ k f, ∃ e₁ e₂ : Predicate k,
      IsEscape k f e₁ ∧ IsEscape k f e₂ ∧ ∃ x, e₁ x ≠ e₂ x) ∧
    committed.WF ∧
    (∀ π : Path, ∀ k, ¬ Diagonal.PointSurjective (π.rep k)) ∧
    (∀ k f, Nec ⟨f⟩ (fun n' => ¬ Diagonal.PointSurjective n'.reading) ∧
      ∃ e₁ e₂ : Predicate k,
        IsEscape k f e₁ ∧ IsEscape k f e₂ ∧ (∃ x, e₁ x ≠ e₂ x) ∧
        Poss ⟨f⟩ (fun n' => ∀ a, n'.reading none (some a) = e₁ a) ∧
        Poss ⟨f⟩ (fun n' => ∀ a, n'.reading none (some a) = e₂ a)) ∧
    (∀ k f e₁ e₂, (∃ x, e₁ x ≠ e₂ x) →
      ∃ x : Ladder.Level k,
        (childOf ⟨f⟩ e₁).reading none (some x) ≠
          (childOf ⟨f⟩ e₂).reading none (some x)) :=
  ⟨branch_nonempty, committed_is_path, fun π k => seal_along_every_path π k,
   ascent_necessary_direction_free, fun k f e₁ e₂ h => paths_diverge k f e₁ e₂ h⟩

#print axioms Branch.escapeSet_two
#print axioms Branch.branch_nonempty
#print axioms Branch.committed_is_path
#print axioms Branch.committed_rep
#print axioms Branch.seal_along_every_path
#print axioms Branch.nec_seal
#print axioms Branch.escape_choice_possible
#print axioms Branch.escape_not_necessary
#print axioms Branch.poss_without_nec
#print axioms Branch.ascent_necessary_direction_free
#print axioms Branch.paths_diverge
#print axioms Branch.paths_diverge_no_past_agree
#print axioms Branch.paths_from_underdetermination
#print axioms Branch.branch_package

end Branch
