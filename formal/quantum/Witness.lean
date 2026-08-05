import Orthoset
import Axiom

/-!
# Witness — a proper independence model for superposition

`Ortho.superposition_is_independent` is not enough on its own. An independence
witness for a clause must satisfy **every other clause**, and the classical bit
fails rank as well as superposition, so it cannot show that superposition is
underivable from the rest. This module supplies the missing model.

The model is the classical orthoset on `Nat`: distinguishability, `x ≠ y`. It
satisfies irredundancy, orthomodularity and the normed infinite orthogonal
family — hence also rank of every order — and fails superposition
(`Axiom.discrete_no_superposition`). So superposition is not a consequence of
the other three clauses of `Axiom.Orthoframe`.

* **Transposition** (`swap`, `swap_swap`, `swap_injective`): the symmetry used
  to witness equal size.
* **The model satisfies** (`discrete_irredundant`,
  `discrete_orthomodular`, `discrete_normed`).
* **The model fails** (`discrete_not_orthoframe_by_superposition`).
* **Conclusion** (`superposition_independent_of_the_rest`).

## Logical strength

`discrete_orthomodular` uses excluded middle: the orthomodular law asks whether
a state lies in a subspace `S` or in its orthocomplement, and for an arbitrary
`S : Nat → Prop` that is exactly `S x ∨ ¬ S x`. The module therefore does not
meet the corpus's zero-axiom target, and the audit records `Classical.choice`
and `propext` against the affected results. This is a countermodel, and the
metatheorem it supports — "superposition is not derivable from the rest" — is
classical anyway; nothing elsewhere in the package inherits the footprint.
-/
namespace Quantum.Witness

open Quantum.Orthoset
open Quantum.Axiom

/-! ## Transposition -/

/-- Exchange `a` and `b`, fixing everything else. -/
def swap (a b n : Nat) : Nat :=
  if n = a then b else if n = b then a else n

theorem swap_left (a b : Nat) : swap a b a = b := by
  unfold swap; rw [if_pos rfl]

theorem swap_swap (a b n : Nat) : swap a b (swap a b n) = n := by
  unfold swap
  by_cases h1 : n = a
  · rw [if_pos h1]
    by_cases h2 : b = a
    · rw [if_pos h2, h1, h2]
    · rw [if_neg h2, if_pos rfl, h1]
  · rw [if_neg h1]
    by_cases h2 : n = b
    · rw [if_pos h2, if_pos rfl, h2]
    · rw [if_neg h2, if_neg h1, if_neg h2]

theorem swap_injective (a b x y : Nat) (h : swap a b x = swap a b y) : x = y := by
  have := congrArg (swap a b) h
  rwa [swap_swap, swap_swap] at this

/-- `swap` fixes anything distinct from both transposed points. -/
theorem swap_fixes (a b n : Nat) (ha : n ≠ a) (hb : n ≠ b) : swap a b n = n := by
  unfold swap; rw [if_neg ha, if_neg hb]

/-- The transposition as a symmetry of the classical orthoset. -/
def swapAuto (a b : Nat) : Auto (discrete Nat) where
  map := swap a b
  inv := swap a b
  left_inv := swap_swap a b
  right_inv := swap_swap a b
  perp_iff := fun x y => by
    constructor
    · intro h hxy; exact h (congrArg (swap a b) hxy)
    · intro h hs; exact h (swap_injective a b x y hs)

/-! ## What the model satisfies -/

/-- Distinguishability separates points: `y` is orthogonal to `x` but not to
    itself. -/
theorem discrete_irredundant : Irredundant (discrete Nat) := by
  intro x y hxy
  exact ⟨y, Or.inl ⟨fun h => hxy h.symm, fun h => h rfl⟩⟩

/-- The classical orthoset is orthomodular. Uses excluded middle on `S x`; see
    the module docstring. -/
theorem discrete_orthomodular : OrthomodularO (discrete Nat) := by
  intro S T _hS _hT hST x hTx y hy heq
  refine hy x ?_ heq.symm
  by_cases hSx : S x
  · exact Or.inl hSx
  · refine Or.inr ⟨hTx, ?_⟩
    intro z hSz hxz
    exact hSx (hxz ▸ hSz)

/-- The identity family is pairwise orthogonal and of constant size: the
    transposition exchanging any two of its members fixes everything orthogonal
    to both. -/
theorem discrete_normed : HasNormedOrthogonalSequence (discrete Nat) := by
  refine ⟨fun n => n, fun i j hij => hij, fun i j => ?_⟩
  refine ⟨swapAuto i j, swap_left i j, ?_⟩
  intro z hzi hzj
  exact swap_fixes i j z (fun h => hzi h) (fun h => hzj h)

/-- Hence rank of every finite order. -/
theorem discrete_rank (n : Nat) : HasRankN (discrete Nat) n :=
  rank_of_normed (discrete Nat) discrete_normed n

/-! ## What the model fails -/

/-- The model is not an `Orthoframe`, and the clause it fails is
    superposition. -/
theorem discrete_not_orthoframe_by_superposition :
    ¬ SuperpositionO (discrete Nat) :=
  discrete_no_superposition ⟨0, 1, fun h => Nat.noConfusion h⟩

/-! ## Conclusion -/

/-- **Superposition is independent of the rest.** One model satisfies
    irredundancy, orthomodularity, the normed infinite orthogonal family and
    rank of every order, and fails superposition. So superposition is not a
    consequence of the other clauses of `Axiom.Orthoframe`, and it cannot be
    dropped from the hypothesis. -/
theorem superposition_independent_of_the_rest :
    Irredundant (discrete Nat) ∧
    OrthomodularO (discrete Nat) ∧
    HasNormedOrthogonalSequence (discrete Nat) ∧
    (∀ n, HasRankN (discrete Nat) n) ∧
    ¬ SuperpositionO (discrete Nat) :=
  ⟨discrete_irredundant, discrete_orthomodular, discrete_normed,
   discrete_rank, discrete_not_orthoframe_by_superposition⟩

#print axioms Quantum.Witness.swap_swap
#print axioms Quantum.Witness.swap_injective
#print axioms Quantum.Witness.swap_fixes
#print axioms Quantum.Witness.discrete_irredundant
#print axioms Quantum.Witness.discrete_orthomodular
#print axioms Quantum.Witness.discrete_normed
#print axioms Quantum.Witness.discrete_rank
#print axioms Quantum.Witness.discrete_not_orthoframe_by_superposition
#print axioms Quantum.Witness.superposition_independent_of_the_rest

end Quantum.Witness
