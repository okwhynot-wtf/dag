import Orbit
import Facticity

/-!
# Ambient — uniqueness of `a ∘ a = id` in the arena signature

The arena signature is one type and one endomap. Terms in one free
variable are iterates `aⁿ(x)`; the only atomic relation is equality.
Every single equation in one free variable therefore has the form
`aᵐ(x) = aⁿ(x)`. Relative to that fragment the search space is exhaustive.

Multi-variable single equations over the same signature (e.g.
`∀ x y, a(x) = a(y)`) force constancy on the image and are erasing on any
carrier with two or more points; they die immediately as ambients for
fundamentality. Ambients beyond the one-variable equational fragment are
refused by parsimony of the arena language (status inventory, not a
theorem clause).

Classification (one-variable equational fragment):
* equations `aᵐ = aⁿ` with `n ≥ 1` need not force injectivity
  (`a² = a` admits erasure);
* equations `aᵐ = id` force bijectivity; among those, `m = 1` is rest,
  and for every `m ≥ 3` an `m`-cycle is a countermodel with an asymmetric
  point (`a(a(z)) ≠ z`);
* hence `a² = id` is the unique nontrivial one-variable single equation
  that excludes both smuggled arrow and smuggled loss.
-/
namespace Ambient

open Orbit

/-! ## One-variable single-equation ambients -/

/-- The one-variable equational ambient `∀ x, aᵐ(x) = aⁿ(x)`. -/
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

/-! ## Multi-variable single equations die by constancy -/

/-- The multi-variable equation `∀ x y, a(x) = a(y)` (constancy). -/
def ConstantEquation {α : Type} (act : α → α) : Prop :=
  ∀ x y, act x = act y

/-- Constancy is erasing whenever the carrier has two distinct points. -/
theorem constantEquation_erasing {α : Type} (act : α → α)
    (h : ConstantEquation act) {x y : α} (hne : x ≠ y) : Erasing act :=
  ⟨x, y, hne, h x y⟩

/-- On `Bool`, the constancy equation is erasing — so it fails as an ambient
    for lossless fundamentality. -/
theorem constantEquation_bool_erasing :
    ConstantEquation (fun _ : Bool => false) ∧
    Erasing (fun _ : Bool => false) :=
  ⟨fun _ _ => rfl, ⟨true, false, by decide, rfl⟩⟩

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

/-- One-variable equations `aᵐ = aⁿ` with positive right-hand exponent need
    not force losslessness. -/
theorem eqAmbient_pos_need_not_lossless :
    EqAmbient 2 1 idempotentErase ∧ Erasing idempotentErase ∧
      ¬ Lossless idempotentErase :=
  ⟨idempotentErase_ambient, idempotentErase_erasing, idempotentErase_not_lossless⟩

/-! ## Countermodel family: `aᵐ = id` for `m ≥ 3` admits asymmetric points -/

/-- Three-point carrier for the concrete `m = 3` cycle. -/
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

theorem powerId_ge_three_need_not_symmetric :
    PowerId 3 cycle3 ∧ ∀ z : Trip, cycle3 (cycle3 z) ≠ z := by
  refine ⟨cycle3_powerId, ?_⟩
  intro z
  exact cycle3_asymmetric z

theorem cycle3_lossless : Lossless cycle3 := by
  intro x y h
  cases x <;> cases y <;> cases h <;> rfl

/-- Carrier of the length-`m` cycle: naturals strictly below `m`. -/
abbrev CycleCarrier (m : Nat) : Type :=
  { k : Nat // k < m }

/-- `(x % m + 1) % m = (x + 1) % m` for `m > 0`. -/
private theorem mod_succ_mod (x m : Nat) (hm : 0 < m) :
    (x % m + 1) % m = (x + 1) % m := by
  have h := (Nat.add_mod x 1 m).symm
  -- h : (x % m + 1 % m) % m = (x + 1) % m
  cases Nat.lt_or_ge 1 m with
  | inl h1m =>
    -- m > 1 ⇒ 1 % m = 1
    rw [← h, Nat.mod_eq_of_lt h1m]
  | inr h1m =>
    -- 0 < m ≤ 1 ⇒ m = 1; both sides are 0
    have hm1 : m = 1 := Nat.le_antisymm h1m hm
    subst hm1
    -- x % 1 = 0, (0+1)%1 = 0, (x+1)%1 = 0
    have hx : x % 1 = 0 := Nat.mod_one x
    simp [hx, Nat.mod_one]

/-- Wrap-around successor on `CycleCarrier m`. -/
def cycleM (m : Nat) (hm : 0 < m) : CycleCarrier m → CycleCarrier m :=
  fun i => ⟨(i.val + 1) % m, Nat.mod_lt (i.val + 1) hm⟩

private theorem iter_cycleM_val (m : Nat) (hm : 0 < m) (k : Nat)
    (i : CycleCarrier m) :
    (iter (cycleM m hm) k i).val = (i.val + k) % m := by
  induction k with
  | zero =>
    simp [iter, Nat.add_zero, Nat.mod_eq_of_lt i.property]
  | succ k ih =>
    change ((iter (cycleM m hm) k i).val + 1) % m = (i.val + (k + 1)) % m
    rw [ih]
    have hassoc : i.val + (k + 1) = i.val + k + 1 := (Nat.add_assoc _ _ _).symm
    rw [hassoc, mod_succ_mod (i.val + k) m hm]

/-- On `CycleCarrier m`, the wrap-around cycle satisfies `aᵐ = id`. -/
theorem cycleM_powerId (m : Nat) (hm : 0 < m) :
    PowerId m (cycleM m hm) := by
  intro i
  apply Subtype.ext
  have h := iter_cycleM_val m hm m i
  have hcancel : (i.val + m) % m = i.val := by
    have hself : m % m = 0 := Nat.mod_self m
    calc
      (i.val + m) % m = (i.val % m + m % m) % m := by rw [Nat.add_mod]
      _ = (i.val % m + 0) % m := by rw [hself]
      _ = i.val % m % m := by rw [Nat.add_zero]
      _ = i.val % m := Nat.mod_mod _ _
      _ = i.val := Nat.mod_eq_of_lt i.property
  -- PowerId: iter m i = iter 0 i, i.e. vals equal
  change (iter (cycleM m hm) m i).val = i.val
  rw [h, hcancel]

/-- For every `m ≥ 3`, an `m`-cycle is a countermodel with an asymmetric point. -/
theorem exists_asymmetric_m_cycle (m : Nat) (hm : 3 ≤ m) :
    ∃ act : CycleCarrier m → CycleCarrier m,
      PowerId m act ∧ ∃ z : CycleCarrier m, act (act z) ≠ z := by
  have hm0 : 0 < m := Nat.lt_of_lt_of_le (by decide : 0 < 3) hm
  refine ⟨cycleM m hm0, cycleM_powerId m hm0, ?_⟩
  refine ⟨⟨0, hm0⟩, ?_⟩
  intro h
  have hv := congrArg Subtype.val h
  change ((0 + 1) % m + 1) % m = 0 at hv
  have h2lt : 2 < m := Nat.lt_of_lt_of_le (by decide : 2 < 3) hm
  have h1m : 1 % m = 1 :=
    Nat.mod_eq_of_lt (Nat.lt_trans (by decide : 1 < 2) h2lt)
  have h2m : 2 % m = 2 := Nat.mod_eq_of_lt h2lt
  have : ((0 + 1) % m + 1) % m = 2 := by
    rw [Nat.zero_add, h1m]
    change (1 + 1) % m = 2
    rw [show (1 + 1 : Nat) = 2 from rfl, h2m]
  rw [this] at hv
  exact (by decide : ¬ (2 = 0)) hv

/-! ## Positive uniqueness content for `a² = id` -/

theorem powerId_two_excludes_erase {α : Type} (act : α → α)
    (h : PowerId 2 act) : ¬ Erasing act := by
  have hs : SymmetricStep act := (powerId_two_iff_symmetric act).mp h
  intro he
  obtain ⟨x, y, hne, heq⟩ := he
  exact hne (symmetric_lossless act hs x y heq)

theorem powerId_two_excludes_arrow {α : Type} (act : α → α)
    (h : PowerId 2 act) (z : α) : act (act z) = z :=
  h z

theorem powerId_one_is_degenerate {α : Type} [Inhabited α] (act : α → α)
    (h : PowerId 1 act) : ¬ Facticity.NonDegenerate act default := by
  intro hne
  exact hne (h default)

/-- **Ambient uniqueness (one-variable equational fragment).** Among
    one-variable single equations in the arena signature:
    * `a² = a` fails losslessness;
    * `a = id` is rest;
    * for every `m ≥ 3`, `aᵐ = id` admits asymmetric points;
    * `a² = id` excludes both erasure and asymmetric step. -/
theorem ambient_uniqueness_equational :
    (EqAmbient 2 1 idempotentErase ∧ Erasing idempotentErase) ∧
    (∀ m : Nat, 3 ≤ m →
      ∃ act : CycleCarrier m → CycleCarrier m,
        PowerId m act ∧ ∃ z, act (act z) ≠ z) ∧
    (∀ (α : Type) (act : α → α), PowerId 2 act → ¬ Erasing act) ∧
    (∀ (α : Type) (act : α → α), PowerId 2 act → ∀ z, act (act z) = z) ∧
    (∀ (α : Type) (act : α → α), PowerId 2 act ↔ SymmetricStep act) :=
  ⟨⟨idempotentErase_ambient, idempotentErase_erasing⟩,
   exists_asymmetric_m_cycle,
   fun _ act h => powerId_two_excludes_erase act h,
   fun _ act h z => powerId_two_excludes_arrow act h z,
   fun _ act => powerId_two_iff_symmetric act⟩

/-! ## Signature exhaustiveness markers (status / meta, not theorem clauses) -/

/-- Relative to one free variable over a signature of one endomap, every
    single equation among terms is an instance of `EqAmbient m n`. -/
def single_equation_one_var_exhaustive : True := True.intro

/-- Ambients beyond the one-variable equational fragment (multi-variable
    equations treated as separate ambients, quasi-equational / Horn /
    second-order constraints) are refused by parsimony of the arena
    language. Status marker only. -/
def non_equational_ambient_refused : True := True.intro

theorem injectivity_of_powerId_two {α : Type} (act : α → α)
    (h : PowerId 2 act) : Lossless act :=
  symmetric_lossless act ((powerId_two_iff_symmetric act).mp h)

/-- Package used by the paper's Interpretation / Section 12 relocation. -/
theorem ambient_adequacy_package :
    ((EqAmbient 2 1 idempotentErase ∧ Erasing idempotentErase) ∧
      (∀ m : Nat, 3 ≤ m →
        ∃ act : CycleCarrier m → CycleCarrier m,
          PowerId m act ∧ ∃ z, act (act z) ≠ z) ∧
      (∀ (α : Type) (act : α → α), PowerId 2 act → ¬ Erasing act) ∧
      (∀ (α : Type) (act : α → α), PowerId 2 act → ∀ z, act (act z) = z) ∧
      (∀ (α : Type) (act : α → α), PowerId 2 act ↔ SymmetricStep act)) ∧
    ConstantEquation (fun _ : Bool => false) ∧
      Erasing (fun _ : Bool => false) ∧
    single_equation_one_var_exhaustive = True.intro ∧
    non_equational_ambient_refused = True.intro ∧
    (∀ (α : Type) (act : α → α), PowerId 2 act → Lossless act) :=
  ⟨ambient_uniqueness_equational, constantEquation_bool_erasing.1,
   constantEquation_bool_erasing.2, rfl, rfl,
   fun _ act h => injectivity_of_powerId_two act h⟩

#print axioms Ambient.powerId_two_iff_symmetric
#print axioms Ambient.powerId_one_is_rest
#print axioms Ambient.constantEquation_erasing
#print axioms Ambient.constantEquation_bool_erasing
#print axioms Ambient.idempotentErase_ambient
#print axioms Ambient.idempotentErase_erasing
#print axioms Ambient.eqAmbient_pos_need_not_lossless
#print axioms Ambient.cycle3_powerId
#print axioms Ambient.cycle3_asymmetric
#print axioms Ambient.powerId_ge_three_need_not_symmetric
#print axioms Ambient.cycle3_lossless
#print axioms Ambient.cycleM_powerId
#print axioms Ambient.exists_asymmetric_m_cycle
#print axioms Ambient.powerId_two_excludes_erase
#print axioms Ambient.powerId_two_excludes_arrow
#print axioms Ambient.ambient_uniqueness_equational
#print axioms Ambient.injectivity_of_powerId_two
#print axioms Ambient.ambient_adequacy_package

end Ambient
