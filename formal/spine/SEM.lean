import Cause

/-!
# SEM — toy structural-equation image of the ladder

A minimal Bool-valued SCM image of the first `n` ladder ticks, sufficient
to check that intervention and asymmetry on the ladder match the
`do`-operator and acyclicity of the image. Full generality over SCMs is
out of scope.

* **Toy SCM** (`ToySCM`): finite variable set `Fin (n+1)`, Bool values,
  parent relation from the Option-tower, mechanisms from naming.
* **Image** (`ladderToSCM`): first `n` ticks as a toy SCM.
* **Commutation** (`intervention_commutes`): `Cause.step` agrees with
  the image `do`-operator on named content.
* **Asymmetry** (`asymmetry_is_acyclicity`): causal asymmetry on the
  ladder maps to acyclicity of the parent relation.
-/
namespace SEM

/-- Variables of the n-tick image: one per level `0..n`. -/
abbrev Var (n : Nat) := Fin (n + 1)

/-- Parent relation: variable `j` is a parent of `i` when `j < i`
    (earlier levels feed later namers). -/
def parent (n : Nat) (j i : Var n) : Prop :=
  j.val < i.val

/-- Acyclicity: the parent relation is a strict order on indices. -/
theorem acyclic (n : Nat) :
    ∀ i j : Var n, parent n i j → ¬ parent n j i := by
  intro i j hij hji
  exact Nat.lt_irrefl _ (Nat.lt_trans hij hji)

/-- Mechanism at variable `i`: for `i = 0`, the fundamental reading `f₀`;
    for `i = k+1`, the dodge step of the prior reading. Stated as the
    ladder reading at level `i` under the committed policy. -/
def mechanism (n : Nat) (i : Var n) :
    Ladder.Level i.val → Ladder.Level i.val → Bool :=
  Ladder.rep i.val

/-- Toy SCM for the first `n` ticks. -/
structure ToySCM (n : Nat) where
  parent_rel : Var n → Var n → Prop := parent n
  mech : (i : Var n) → Ladder.Level i.val → Ladder.Level i.val → Bool :=
    mechanism n

/-- Image of the first `n` ladder ticks. -/
def ladderToSCM (n : Nat) : ToySCM n where
  parent_rel := parent n
  mech := mechanism n

/-- Soft `do`-operator on the image: replace the reading at level `k`
    and take one naming step (same as `Cause.step`). -/
def doOp {A : Type} (f : A → A → Bool) : Option A → Option A → Bool :=
  Cause.step f

/-- Intervention on the ladder agrees with the image `do`-operator. -/
theorem intervention_commutes (k : Nat) :
    ∀ x y : Ladder.Level (k + 1),
      Ladder.rep (k + 1) x y = doOp (Ladder.rep k) x y :=
  Cause.ladder_is_iterated_step k

/-- Distinct diagonals change the `do`-effect at `none`, matching
    `Cause.intervention_changes_dodge`. -/
theorem do_changes_on_diagonal {A : Type} (f f' : A → A → Bool) (a : A)
    (h : f a a ≠ f' a a) :
    doOp f none (some a) ≠ doOp f' none (some a) :=
  Cause.intervention_changes_dodge f f' a h

/-- Causal asymmetry on the ladder: forward naming is the dodge; backward
    lifts conserve. This is the content that maps to acyclicity
    (parents are strictly earlier). -/
theorem asymmetry_is_acyclicity (n : Nat) :
    (∀ k : Var n, k.val < n →
      ∀ a : Ladder.Level k.val,
        Ladder.rep (k.val + 1) none (some a) =
          !(Ladder.rep k.val a a)) ∧
    (∀ i j : Var n, parent n i j → ¬ parent n j i) := by
  refine ⟨?_, acyclic n⟩
  intro k hk a
  have : k.val + 1 ≤ n := Nat.succ_le_of_lt hk
  exact rfl

/-- Toy SEM package. -/
theorem sem_package (n : Nat) :
    (∀ x y : Ladder.Level (n + 1),
      Ladder.rep (n + 1) x y = doOp (Ladder.rep n) x y) ∧
    (∀ i j : Var (n + 1), parent (n + 1) i j → ¬ parent (n + 1) j i) ∧
    (∀ (k : Nat) (a : Ladder.Level k),
      Ladder.rep (k + 1) none (some a) = !(Ladder.rep k a a)) :=
  ⟨intervention_commutes n, acyclic (n + 1), fun _ _ => rfl⟩

#print axioms SEM.acyclic
#print axioms SEM.intervention_commutes
#print axioms SEM.do_changes_on_diagonal
#print axioms SEM.asymmetry_is_acyclicity
#print axioms SEM.sem_package

end SEM
