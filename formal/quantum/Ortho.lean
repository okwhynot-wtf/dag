/-!
# Ortho — ortholattice vocabulary and the classical-bit model

Mathlib-free vocabulary for the lattice side of a Hilbert reconstruction, and
the one model that settles which hypotheses are doing the work: the classical
bit.

Everything is bundled as data (`Ortho P`) rather than as type classes, so no
instance machinery is needed and every law is visible at the use site. The
classical bit's order is Bool-valued, so all four-element checks are decidable.

* **Vocabulary** (`Ortho`, `IsAtom`, `Atomistic`, `Covers`, `CoveringLaw`,
  `Orthomodular`, `Distributive`, `Superposition`).
* **Classical bit** (`bit`): the four-element Boolean algebra of subsets of the
  two-element carrier, with pointwise operations and set complement.
* **What the bit satisfies** (`bit_distributive`, `bit_orthomodular`,
  `bit_atomistic`, `bit_covering_law`).
* **What the bit fails** (`bit_no_superposition`): its only atoms are the two
  pure states, so no third atom lies below their join.

The last two together are the independence result this module exists for: the
superposition principle is **not** a consequence of orthomodularity, atomicity,
or the covering law, even taken together. Used by `Axiom.lean`.
-/
namespace Quantum.Ortho

/-! ## Vocabulary -/

/-- A bounded ortholattice on `P`, bundled as data: a partial order with binary
    meets and joins, top and bottom, and an order-reversing involution `comp`
    whose join and meet with the identity are trivial. -/
structure Ortho (P : Type) where
  /-- The order. -/
  le : P → P → Prop
  /-- Binary join. -/
  sup : P → P → P
  /-- Binary meet. -/
  inf : P → P → P
  /-- Least element. -/
  bot : P
  /-- Greatest element. -/
  top : P
  /-- Orthocomplement. -/
  comp : P → P
  le_refl : ∀ x, le x x
  le_trans : ∀ {x y z}, le x y → le y z → le x z
  le_antisymm : ∀ {x y}, le x y → le y x → x = y
  bot_le : ∀ x, le bot x
  le_top : ∀ x, le x top
  le_sup_left : ∀ x y, le x (sup x y)
  le_sup_right : ∀ x y, le y (sup x y)
  sup_le : ∀ {x y z}, le x z → le y z → le (sup x y) z
  inf_le_left : ∀ x y, le (inf x y) x
  inf_le_right : ∀ x y, le (inf x y) y
  le_inf : ∀ {x y z}, le z x → le z y → le z (inf x y)
  comp_comp : ∀ x, comp (comp x) = x
  comp_le : ∀ {x y}, le x y → le (comp y) (comp x)
  sup_comp : ∀ x, sup x (comp x) = top
  inf_comp : ∀ x, inf x (comp x) = bot

variable {P : Type}

/-- `a` is an atom: nonzero, with nothing strictly between it and `bot`. -/
def IsAtom (L : Ortho P) (a : P) : Prop :=
  a ≠ L.bot ∧ ∀ x, L.le x a → x = L.bot ∨ x = a

/-- Every nonzero element dominates an atom. -/
def Atomistic (L : Ortho P) : Prop :=
  ∀ x, x ≠ L.bot → ∃ a, IsAtom L a ∧ L.le a x

/-- `y` covers `x`: `x ≤ y`, `x ≠ y`, and nothing lies strictly between. -/
def Covers (L : Ortho P) (y x : P) : Prop :=
  L.le x y ∧ x ≠ y ∧ ∀ z, L.le x z → L.le z y → z = x ∨ z = y

/-- Piron's covering law: joining an atom disjoint from `x` moves up exactly
    one step. The lattice form of "adding one sharp alternative". -/
def CoveringLaw (L : Ortho P) : Prop :=
  ∀ a x, IsAtom L a → L.inf a x = L.bot → Covers L (L.sup x a) x

/-- Orthomodularity: below `y`, the relative complement of `x` reconstructs
    `y`. Every distributive ortholattice satisfies it — `bit` is the instance
    recorded here — and the converse fails in general, though no
    non-distributive orthomodular example is constructed in this package. -/
def Orthomodular (L : Ortho P) : Prop :=
  ∀ x y, L.le x y → L.sup x (L.inf y (L.comp x)) = y

/-- Distributivity — the classical (Boolean) law. -/
def Distributive (L : Ortho P) : Prop :=
  ∀ x y z, L.inf x (L.sup y z) = L.sup (L.inf x y) (L.inf x z)

/-- The superposition principle: any two distinct atoms have a third atom
    strictly below their join. The lattice statement that a system has states
    which are neither of two given alternatives and are not mixtures of them. -/
def Superposition (L : Ortho P) : Prop :=
  ∀ a b, IsAtom L a → IsAtom L b → a ≠ b →
    ∃ c, IsAtom L c ∧ L.le c (L.sup a b) ∧ c ≠ a ∧ c ≠ b

/-! ## The classical bit

Propositions of a two-state classical system are the subsets of its carrier,
encoded as a pair of membership bits: `(contains false?, contains true?)`.
-/

/-- Carrier of the classical bit's proposition lattice: four elements. -/
abbrev Bit := Bool × Bool

/-- Pointwise implication, Bool-valued so that all checks are decidable. -/
def leB (x y : Bit) : Bool := (!x.1 || y.1) && (!x.2 || y.2)

/-- Pointwise implication order on subsets. -/
def bitLe (x y : Bit) : Prop := leB x y = true

instance (x y : Bit) : Decidable (bitLe x y) := inferInstanceAs (Decidable (_ = _))

/-- The four-element Boolean algebra of subsets of a two-element set, as an
    ortholattice: union, intersection, and set complement. -/
def bit : Ortho Bit where
  le := bitLe
  sup := fun x y => (x.1 || y.1, x.2 || y.2)
  inf := fun x y => (x.1 && y.1, x.2 && y.2)
  bot := (false, false)
  top := (true, true)
  comp := fun x => (!x.1, !x.2)
  le_refl := by intro ⟨a, b⟩; cases a <;> cases b <;> decide
  le_trans := by
    intro ⟨a, b⟩ ⟨c, d⟩ ⟨e, f⟩
    cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> cases f <;> decide
  le_antisymm := by
    intro ⟨a, b⟩ ⟨c, d⟩
    cases a <;> cases b <;> cases c <;> cases d <;> decide
  bot_le := by intro ⟨a, b⟩; cases a <;> cases b <;> decide
  le_top := by intro ⟨a, b⟩; cases a <;> cases b <;> decide
  le_sup_left := by
    intro ⟨a, b⟩ ⟨c, d⟩; cases a <;> cases b <;> cases c <;> cases d <;> decide
  le_sup_right := by
    intro ⟨a, b⟩ ⟨c, d⟩; cases a <;> cases b <;> cases c <;> cases d <;> decide
  sup_le := by
    intro ⟨a, b⟩ ⟨c, d⟩ ⟨e, f⟩
    cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> cases f <;> decide
  inf_le_left := by
    intro ⟨a, b⟩ ⟨c, d⟩; cases a <;> cases b <;> cases c <;> cases d <;> decide
  inf_le_right := by
    intro ⟨a, b⟩ ⟨c, d⟩; cases a <;> cases b <;> cases c <;> cases d <;> decide
  le_inf := by
    intro ⟨a, b⟩ ⟨c, d⟩ ⟨e, f⟩
    cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> cases f <;> decide
  comp_comp := by intro ⟨a, b⟩; cases a <;> cases b <;> rfl
  comp_le := by
    intro ⟨a, b⟩ ⟨c, d⟩; cases a <;> cases b <;> cases c <;> cases d <;> decide
  sup_comp := by intro ⟨a, b⟩; cases a <;> cases b <;> rfl
  inf_comp := by intro ⟨a, b⟩; cases a <;> cases b <;> rfl

/-- The bit's order is decidable through the structure projection, so all
    four-element checks below can be discharged by `decide`. -/
instance decBitLe (x y : Bit) : Decidable (bit.le x y) :=
  inferInstanceAs (Decidable (bitLe x y))

/-! ## What the classical bit satisfies -/

/-- The bit's lattice is distributive — it is a Boolean algebra. -/
theorem bit_distributive : Distributive bit := by
  intro ⟨a, b⟩ ⟨c, d⟩ ⟨e, f⟩
  cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> cases f <;> rfl

/-- The bit's lattice is orthomodular (as every Boolean algebra is). -/
theorem bit_orthomodular : Orthomodular bit := by
  intro ⟨a, b⟩ ⟨c, d⟩
  cases a <;> cases b <;> cases c <;> cases d <;> decide

/-- The singleton `{false-slot}` is an atom. -/
theorem bit_atom_left : IsAtom bit (true, false) :=
  ⟨by decide, by intro ⟨a, b⟩; cases a <;> cases b <;> decide⟩

/-- The singleton `{true-slot}` is an atom. -/
theorem bit_atom_right : IsAtom bit (false, true) :=
  ⟨by decide, by intro ⟨a, b⟩; cases a <;> cases b <;> decide⟩

/-- The two singletons are the ONLY atoms: `bot` is excluded by definition and
    `top` is not minimal. -/
theorem bit_atoms_are_two (x : Bit) (h : IsAtom bit x) :
    x = (true, false) ∨ x = (false, true) := by
  obtain ⟨a, b⟩ := x
  cases a <;> cases b
  · exact absurd rfl h.1
  · exact Or.inr rfl
  · exact Or.inl rfl
  · exact absurd (h.2 (true, false) (by decide)) (by decide)

/-- The bit's lattice is atomistic. -/
theorem bit_atomistic : Atomistic bit := by
  intro ⟨a, b⟩ h
  cases a <;> cases b
  · exact absurd rfl h
  · exact ⟨(false, true), bit_atom_right, by decide⟩
  · exact ⟨(true, false), bit_atom_left, by decide⟩
  · exact ⟨(true, false), bit_atom_left, by decide⟩

/-- The bit's lattice satisfies the covering law. -/
theorem bit_covering_law : CoveringLaw bit := by
  intro a x ha hinf
  obtain ⟨c, d⟩ := x
  rcases bit_atoms_are_two a ha with rfl | rfl <;>
    cases c <;> cases d <;>
    first
      | exact absurd hinf (by decide)
      | exact ⟨by decide, by decide,
               by intro ⟨e, f⟩ h₁ h₂; cases e <;> cases f <;> revert h₁ h₂ <;> decide⟩

/-! ## What the classical bit fails -/

/-- **Independence.** The classical bit has no superposition: its two atoms
    join to the top, and no third atom lies below. Together with
    `bit_orthomodular`, `bit_atomistic` and `bit_covering_law` this shows the
    superposition principle is not a consequence of orthomodularity, atomicity,
    or the covering law. -/
theorem bit_no_superposition : ¬ Superposition bit := by
  intro hsup
  obtain ⟨c, hc, _, hca, hcb⟩ :=
    hsup (true, false) (false, true) bit_atom_left bit_atom_right (by decide)
  rcases bit_atoms_are_two c hc with rfl | rfl
  · exact hca rfl
  · exact hcb rfl

/-- Summary of the independence argument: a single model satisfies every
    standard lattice hypothesis of the Piron programme except superposition. -/
theorem superposition_is_independent :
    Orthomodular bit ∧ Atomistic bit ∧ CoveringLaw bit ∧
    Distributive bit ∧ ¬ Superposition bit :=
  ⟨bit_orthomodular, bit_atomistic, bit_covering_law, bit_distributive,
   bit_no_superposition⟩

#print axioms Quantum.Ortho.bit
#print axioms Quantum.Ortho.bit_distributive
#print axioms Quantum.Ortho.bit_orthomodular
#print axioms Quantum.Ortho.bit_atom_left
#print axioms Quantum.Ortho.bit_atom_right
#print axioms Quantum.Ortho.bit_atoms_are_two
#print axioms Quantum.Ortho.bit_atomistic
#print axioms Quantum.Ortho.bit_covering_law
#print axioms Quantum.Ortho.bit_no_superposition
#print axioms Quantum.Ortho.superposition_is_independent

end Quantum.Ortho
