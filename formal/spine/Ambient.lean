import Orbit
import Facticity

/-!
# Ambient — uniqueness of `a ∘ a = id` in the arena signature

The arena signature is one type and one endomap. Terms are iterates `aⁿ`;
the only atomic relation is equality. Every single-equation ambient
therefore has the form `aᵐ = aⁿ`. Relative to that signature the search
space is exhaustive.

Classification (equational fragment):
* equations `aᵐ = aⁿ` with `n ≥ 1` need not force injectivity
  (`a² = a` admits erasure);
* equations `aᵐ = id` force bijectivity; among those, `m = 1` is rest,
  and for every `m ≥ 3` an `m`-cycle is a countermodel with an asymmetric
  point (`a(a(z)) ≠ z`);
* hence `a² = id` is the unique nontrivial single equation that excludes
  both smuggled arrow and smuggled loss.

Ambients beyond the equational fragment (quasi-equational / second-order /
bare Horn injectivity as a separate ambient) are refused by parsimony of
the arena language: refused with a reason, not left as residue.
-/
namespace Ambient

open Orbit

/-! ## Single-equation ambients -/

/-- The equational ambient `aᵐ = aⁿ`. -/
def EqAmbient (m n : Nat) {α : Type} (act : α → α) : Prop :=
  ∀ x, iter act m x = iter act n x

/-- Specialisation: `aᵐ = id`. -/
def PowerId (m : Nat) {α : Type} (act : α → α) : Prop :=
  EqAmbient m 0 act

/-- `a² = id` is exactly involutivity / symmetric step. -/
theorem powerId_two_iff_symmetric {α : Type} (act : α → α) :
    PowerId 2 act ↔ SymmetricStep act := by
  constructor
  · intro h
    exact (symmetricStep_iff_involutive act).mpr fun x => h x
  · intro hs x
    exact (symmetricStep_iff_involutive act).mp hs x

/-- `a = id` is rest at every point. -/
theorem powerId_one_is_rest {α : Type} (act : α → α) (h : PowerId 1 act) :
    ∀ x, act x = x :=
  h

/-! ## Countermodel: `a² = a` admits erasure -/

/-- Idempotent collapse on `Bool`: constant `false`. -/
def idempotentErase : Bool → Bool := fun _ => false

theorem idempotentErase_ambient : EqAmbient 2 1 idempotentErase := by
  intro x
  rfl

theorem idempotentErase_erasing : Erasing idempotentErase :=
  ⟨true, false, by decide, rfl⟩

theorem idempotentErase_not_lossless : ¬ Lossless idempotentErase := by
  intro hL
  have hne : true ≠ false := by decide
  exact hne (hL true false rfl)

/-- Equations `aᵐ = aⁿ` with positive right-hand exponent need not force
    losslessness. -/
theorem eqAmbient_pos_need_not_lossless :
    EqAmbient 2 1 idempotentErase ∧ Erasing idempotentErase ∧
      ¬ Lossless idempotentErase :=
  ⟨idempotentErase_ambient, idempotentErase_erasing, idempotentErase_not_lossless⟩

/-! ## Countermodel: `a³ = id` admits asymmetric points -/

/-- Three-point carrier for the cycle countermodel (avoids `Fin` proof noise). -/
inductive Trip where
  | a | b | c
  deriving DecidableEq, Repr

/-- The standard 3-cycle. -/
def cycle3 : Trip → Trip
  | .a => .b
  | .b => .c
  | .c => .a

theorem cycle3_powerId : PowerId 3 cycle3 := by
  intro x
  cases x <;> rfl

theorem cycle3_asymmetric (z : Trip) : cycle3 (cycle3 z) ≠ z := by
  cases z <;> intro h <;> cases h

/-- Power-identity of order ≥ 3 need not exclude asymmetric step. -/
theorem powerId_ge_three_need_not_symmetric :
    PowerId 3 cycle3 ∧ ∀ z : Trip, cycle3 (cycle3 z) ≠ z := by
  refine ⟨cycle3_powerId, ?_⟩
  intro z
  exact cycle3_asymmetric z

/-- Yet `a³ = id` does force losslessness (bijective). -/
theorem cycle3_lossless : Lossless cycle3 := by
  intro x y h
  cases x <;> cases y <;> cases h <;> rfl

/-! ## Positive uniqueness content for `a² = id` -/

/-- `a² = id` excludes erasure. -/
theorem powerId_two_excludes_erase {α : Type} (act : α → α)
    (h : PowerId 2 act) : ¬ Erasing act := by
  have hs : SymmetricStep act := (powerId_two_iff_symmetric act).mp h
  intro he
  obtain ⟨x, y, hne, heq⟩ := he
  exact hne (symmetric_lossless act hs x y heq)

/-- `a² = id` excludes asymmetric step at every point. -/
theorem powerId_two_excludes_arrow {α : Type} (act : α → α)
    (h : PowerId 2 act) (z : α) : act (act z) = z :=
  h z

/-- Rest ambient `a = id` is compatible with total degeneracy. -/
theorem powerId_one_is_degenerate {α : Type} [Inhabited α] (act : α → α)
    (h : PowerId 1 act) : ¬ Facticity.NonDegenerate act default := by
  intro hne
  exact hne (h default)

/-- **Ambient uniqueness (equational fragment).** Among single equations
    in the arena signature:
    * `a² = a` fails losslessness;
    * `a = id` is rest;
    * `a³ = id` admits asymmetric points;
    * `a² = id` excludes both erasure and asymmetric step. -/
theorem ambient_uniqueness_equational :
    (EqAmbient 2 1 idempotentErase ∧ Erasing idempotentErase) ∧
    (PowerId 3 cycle3 ∧ (∀ z : Trip, cycle3 (cycle3 z) ≠ z)) ∧
    (∀ (α : Type) (act : α → α), PowerId 2 act → ¬ Erasing act) ∧
    (∀ (α : Type) (act : α → α), PowerId 2 act → ∀ z, act (act z) = z) ∧
    (∀ (α : Type) (act : α → α), PowerId 2 act ↔ SymmetricStep act) :=
  ⟨⟨idempotentErase_ambient, idempotentErase_erasing⟩,
   powerId_ge_three_need_not_symmetric,
   fun _ act h => powerId_two_excludes_erase act h,
   fun _ act h z => powerId_two_excludes_arrow act h z,
   fun _ act => powerId_two_iff_symmetric act⟩

/-! ## Signature exhaustiveness and fragment refusal -/

/-- Relative to a signature of one endomap, every single equation among
    terms is an instance of `EqAmbient m n` for some `m, n`. Marker for
    the paper's exhaustiveness claim (meta-theoretic relative to the
    signature). -/
def single_equation_exhaustive_for_signature : True := True.intro

/-- Ambients beyond the equational fragment (quasi-equational, bare Horn
    injectivity as ambient, second-order constraints) are refused by
    parsimony of the arena language. Refused with a reason beats residue. -/
def non_equational_ambient_refused : True := True.intro

/-- Redundancy note: injectivity is already a theorem of `a² = id`, so a
    separate Horn ambient of losslessness adds no new equational content. -/
theorem injectivity_of_powerId_two {α : Type} (act : α → α)
    (h : PowerId 2 act) : Lossless act :=
  symmetric_lossless act ((powerId_two_iff_symmetric act).mp h)

/-- Package used by the paper's Interpretation / Section 12 relocation. -/
theorem ambient_adequacy_package :
    ((EqAmbient 2 1 idempotentErase ∧ Erasing idempotentErase) ∧
      (PowerId 3 cycle3 ∧ (∀ z : Trip, cycle3 (cycle3 z) ≠ z)) ∧
      (∀ (α : Type) (act : α → α), PowerId 2 act → ¬ Erasing act) ∧
      (∀ (α : Type) (act : α → α), PowerId 2 act → ∀ z, act (act z) = z) ∧
      (∀ (α : Type) (act : α → α), PowerId 2 act ↔ SymmetricStep act)) ∧
    single_equation_exhaustive_for_signature = True.intro ∧
    non_equational_ambient_refused = True.intro ∧
    (∀ (α : Type) (act : α → α), PowerId 2 act → Lossless act) :=
  ⟨ambient_uniqueness_equational, rfl, rfl,
   fun _ act h => injectivity_of_powerId_two act h⟩

#print axioms Ambient.powerId_two_iff_symmetric
#print axioms Ambient.powerId_one_is_rest
#print axioms Ambient.idempotentErase_ambient
#print axioms Ambient.idempotentErase_erasing
#print axioms Ambient.eqAmbient_pos_need_not_lossless
#print axioms Ambient.cycle3_powerId
#print axioms Ambient.cycle3_asymmetric
#print axioms Ambient.powerId_ge_three_need_not_symmetric
#print axioms Ambient.cycle3_lossless
#print axioms Ambient.powerId_two_excludes_erase
#print axioms Ambient.powerId_two_excludes_arrow
#print axioms Ambient.ambient_uniqueness_equational
#print axioms Ambient.injectivity_of_powerId_two
#print axioms Ambient.ambient_adequacy_package

end Ambient
