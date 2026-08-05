import Orthoset

/-!
# Composite — the two-act orthoset on the composite carrier

All results in this module are axiom-free or propext-only.
-/
namespace Quantum.Composite

open Quantum.Orthoset

/-- The composite carrier: two fundamentals side by side. -/
abbrev Q : Type := Bool × Bool

/-- First componentwise flip. -/
def a1 (x : Q) : Q := (!x.1, x.2)

/-- Second componentwise flip. -/
def a2 (x : Q) : Q := (x.1, !x.2)

/-- The joint flip, the composite's global act. -/
def act (x : Q) : Q := (!x.1, !x.2)

/-- The quarter-turn of `SpineFacts.sqrt_model_exists`. -/
def J (x : Q) : Q := (!x.2, x.1)

/-! ## Basic algebra of the two acts -/

theorem a1_involution : ∀ x : Q, a1 (a1 x) = x := by
  intro ⟨a, b⟩; cases a <;> rfl

theorem a2_involution : ∀ x : Q, a2 (a2 x) = x := by
  intro ⟨a, b⟩; cases b <;> rfl

theorem a1_live : ∀ x : Q, a1 x ≠ x := by
  intro ⟨a, b⟩ h; cases a <;> exact Bool.noConfusion (congrArg Prod.fst h)

theorem a2_live : ∀ x : Q, a2 x ≠ x := by
  intro ⟨a, b⟩ h; cases b <;> exact Bool.noConfusion (congrArg Prod.snd h)

theorem act_eq_comp : ∀ x : Q, act x = a1 (a2 x) := fun _ => rfl

theorem act_live : ∀ x : Q, act x ≠ x := by
  intro ⟨a, b⟩ h; cases a <;> exact Bool.noConfusion (congrArg Prod.fst h)

theorem a1_act : ∀ x : Q, a1 (act x) = a2 x := by
  intro ⟨a, b⟩; cases a <;> rfl

theorem a2_act : ∀ x : Q, a2 (act x) = a1 x := by
  intro ⟨a, b⟩; cases b <;> rfl

theorem act_involution : ∀ x : Q, act (act x) = x := by
  intro ⟨a, b⟩; cases a <;> cases b <;> rfl

theorem act_a1 : ∀ x : Q, act (a1 x) = a2 x := by
  intro ⟨a, b⟩; cases a <;> cases b <;> rfl

theorem act_a2 : ∀ x : Q, act (a2 x) = a1 x := by
  intro ⟨a, b⟩; cases a <;> cases b <;> rfl

/-! ## The two-act orthoset -/

/-- Orthogonality generated jointly by the two componentwise acts. -/
def tperp (x y : Q) : Prop := y = a1 x ∨ y = a2 x

instance (x y : Q) : Decidable (tperp x y) :=
  inferInstanceAs (Decidable (_ ∨ _))

theorem tperp_symm : ∀ x y : Q, tperp x y → tperp y x := by
  intro x y h
  cases h with
  | inl h => exact Or.inl (by rw [h, a1_involution])
  | inr h => exact Or.inr (by rw [h, a2_involution])

theorem tperp_irrefl : ∀ x : Q, ¬ tperp x x := by
  intro x h
  cases h with
  | inl h => exact a1_live x h.symm
  | inr h => exact a2_live x h.symm

/-- The composite's two-act orthogonality space. -/
def twoActs : Orthoset Q where
  perp := tperp
  symm := tperp_symm
  irrefl := tperp_irrefl

/-- **Composition does not open rank.** No three states of the
    composite are pairwise orthogonal under the two-act reading. -/
theorem rank_cap_two :
    ∀ x y z : Q, tperp x y → tperp y z → tperp x z → False := by
  intro ⟨a, b⟩ ⟨c, d⟩ ⟨e, f⟩
  cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> cases f <;>
    decide

theorem not_rank3 : ¬ HasRank3 twoActs := by
  intro ⟨x, y, z, h1, h2, h3⟩
  exact rank_cap_two x y z h1 h2 h3

/-! ## Phase invisibility -/

/-- **The joint flip is orthogonally invisible.** Every state has
    exactly the orthogonality neighbourhood of its joint flip. -/
theorem flip_indiscernible :
    ∀ x y : Q, tperp y x ↔ tperp y (act x) := by
  intro x y
  constructor
  · intro h
    cases h with
    | inl h => exact Or.inr (by rw [h, act_a1])
    | inr h => exact Or.inl (by rw [h, act_a2])
  · intro h
    cases h with
    | inl h =>
      refine Or.inr ?_
      have hx := congrArg act h
      rw [act_involution, act_a1] at hx
      exact hx
    | inr h =>
      refine Or.inl ?_
      have hx := congrArg act h
      rw [act_involution, act_a2] at hx
      exact hx

/-- **Irredundancy fails on the composite.** The state and its joint
    flip are distinct and orthogonally indiscernible: the third
    failure direction, beside the spine's rank failure and the
    discrete reading's superposition failure. -/
theorem irredundancy_fails : ¬ Irredundant twoActs := by
  intro hirr
  have hne : ((false, false) : Q) ≠ (true, true) := by
    intro h; exact Bool.noConfusion (congrArg Prod.fst h)
  refine (hirr (false, false) (true, true) hne).elim ?_
  intro z hz
  have hiff := flip_indiscernible (false, false) z
  cases hz with
  | inl h => exact h.2 (hiff.mp h.1)
  | inr h => exact h.2 (hiff.mpr h.1)

/-! ## Rays -/

/-- Two states span the same ray when they agree up to the joint
    flip. -/
def SameRay (x y : Q) : Prop := y = x ∨ y = act x

/-- The ray class: the xor of the components. Constant on rays,
    complete as an invariant. -/
def rayClass (x : Q) : Bool := x.1 ^^ x.2

theorem rayClass_const : ∀ x y : Q, SameRay x y →
    rayClass x = rayClass y := by
  intro ⟨a, b⟩ y h
  cases h with
  | inl h => rw [h]
  | inr h => rw [h]; cases a <;> cases b <;> rfl

/-- **Ray structure.** Orthogonality under the two-act reading holds
    exactly between opposite ray classes: at ray grade the composite
    is the fundamental again. -/
theorem perp_iff_ray_negation :
    ∀ x y : Q, tperp x y ↔ rayClass y = !(rayClass x) := by
  intro ⟨a, b⟩ ⟨c, d⟩
  cases a <;> cases b <;> cases c <;> cases d <;> decide

/-- The joint flip descends to the identity on rays: a global phase. -/
theorem act_ray_trivial : ∀ x : Q, rayClass (act x) = rayClass x := by
  intro ⟨a, b⟩; cases a <;> cases b <;> rfl

/-! ## The quarter-turn on the composite -/

theorem J_squared : ∀ x : Q, J (J x) = act x := by
  intro ⟨a, b⟩; cases b <;> rfl

theorem J_comm_act : ∀ x : Q, J (act x) = act (J x) := by
  intro ⟨a, b⟩; cases a <;> cases b <;> rfl

/-- **The returned arrow.** Every point of the quarter-turn is an
    asymmetric-step point, case (iii) of the pointwise
    classification. -/
theorem J_asymmetric_everywhere : ∀ x : Q, J (J x) ≠ x := by
  intro x h
  exact act_live x ((J_squared x).symm.trans h)

/-- The quarter-turn respects rays. -/
theorem J_respects_rays : ∀ x y : Q, SameRay x y →
    SameRay (J x) (J y) := by
  intro x y h
  cases h with
  | inl h => exact Or.inl (by rw [h])
  | inr h => exact Or.inr (by rw [h, J_comm_act])

/-- **The quarter-turn descends to ray negation.** On rays, `J` is the
    fundamental's own act. -/
theorem J_is_ray_negation :
    ∀ x : Q, rayClass (J x) = !(rayClass x) := by
  intro ⟨a, b⟩; cases a <;> cases b <;> rfl

/-! ## The package -/

/-- **Composite classicality.** (I) The two-act reading has rank two.
    (II) The joint flip is orthogonally invisible and irredundancy
    fails: the composite carries a phase. (III) At ray grade,
    orthogonality is ray negation, the joint flip is trivial, and the
    quarter-turn is the fundamental's act: the composite collapses
    onto the classical bit. (IV) The quarter-turn exists, commutes
    with the joint flip, squares to it, and is asymmetric at every
    point. Superposition is absent at both grades: it remains the
    sole quantum clause after composition. -/
theorem composite_classicality :
    (∀ x y z : Q, tperp x y → tperp y z → tperp x z → False) ∧
    (∀ x y : Q, tperp y x ↔ tperp y (act x)) ∧
    (¬ Irredundant twoActs) ∧
    (∀ x y : Q, tperp x y ↔ rayClass y = !(rayClass x)) ∧
    (∀ x : Q, rayClass (act x) = rayClass x) ∧
    (∀ x : Q, J (J x) = act x) ∧
    (∀ x : Q, J (J x) ≠ x) ∧
    (∀ x : Q, rayClass (J x) = !(rayClass x)) :=
  ⟨rank_cap_two, flip_indiscernible, irredundancy_fails,
   perp_iff_ray_negation, act_ray_trivial, J_squared,
   J_asymmetric_everywhere, J_is_ray_negation⟩

#print axioms Quantum.Composite.rank_cap_two
#print axioms Quantum.Composite.flip_indiscernible
#print axioms Quantum.Composite.irredundancy_fails
#print axioms Quantum.Composite.perp_iff_ray_negation
#print axioms Quantum.Composite.act_ray_trivial
#print axioms Quantum.Composite.J_asymmetric_everywhere
#print axioms Quantum.Composite.J_is_ray_negation
#print axioms Quantum.Composite.composite_classicality

end Quantum.Composite
