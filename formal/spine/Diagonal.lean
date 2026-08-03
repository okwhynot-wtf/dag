import TwoCycle

/-!
# Diagonal — Lawvere diagonal from liveness

Given a live act `act : α → α`, Lawvere's fixed-point theorem yields a
representational limit: no `f : A → A → α` is point-surjective. Predicates
are valued in the fundamental carrier; `TwoCycle.reading` supplies the Bool
instance, and `dodgeWith act f` is an unrepresented predicate built from the
act and diagonal self-application.

* **Lawvere** (`lawvere`): point-surjectivity of `f : A → A → B` forces a
  fixed point of any `g : B → B`.
* **Seal on the fundamental** (`seal_on_fundamental`): a live act forbids
  point-surjection onto `A → α`.
* **Cantor on the fundamental** (`cantor_fundamental`, `cantor`): every representation
  omits some predicate; `dodgeWith` witnesses omission.

No declared axioms.
-/
namespace Diagonal

/-- `f : A → A → B` is point-surjective if every `g : A → B` equals `f a`
    for some `a`. -/
def PointSurjective {A B : Type} (f : A → A → B) : Prop :=
  ∀ g : A → B, ∃ a, f a = g

/-- Lawvere: point-surjectivity of `f` implies every endomap of `B` has a
    fixed point. -/
theorem lawvere {A B : Type} (f : A → A → B) (hf : PointSurjective f)
    (g : B → B) : ∃ b, g b = b := by
  obtain ⟨a, ha⟩ := hf (fun x => g (f x x))
  refine ⟨f a a, ?_⟩
  have h : f a a = g (f a a) := congrFun ha a
  exact h.symm

/-- If `g` has no fixed point, then no `f : A → A → B` is point-surjective. -/
theorem no_point_surjection {A B : Type} (g : B → B)
    (hg : ∀ b, g b ≠ b) (f : A → A → B) : ¬ PointSurjective f := by
  intro hf
  obtain ⟨b, hb⟩ := lawvere f hf g
  exact hg b hb

/-! ## Fundamental-valued predicates -/

/-- A live act forbids point-surjection onto predicates valued in its
    carrier. -/
theorem seal_on_fundamental {α A : Type} (act : α → α) (hl : Orbit.Live act)
    (f : A → A → α) : ¬ PointSurjective f :=
  no_point_surjection act hl f

/-- Predicate omitted by `f`: apply `act` to the diagonal term `f x x`. -/
def dodgeWith {α A : Type} (act : α → α) (f : A → A → α) : A → α :=
  fun x => act (f x x)

theorem dodgeWith_unrepresented {α A : Type} (act : α → α)
    (hl : Orbit.Live act) (f : A → A → α) :
    ∀ a, f a ≠ dodgeWith act f := by
  intro a h
  have hd : f a a = act (f a a) := congrFun h a
  exact hl (f a a) hd.symm

/-- For every `f : A → A → α`, some fundamental-valued predicate is not of the form
    `f a`. -/
theorem cantor_fundamental {α A : Type} (act : α → α) (hl : Orbit.Live act)
    (f : A → A → α) : ∃ g : A → α, ∀ a, f a ≠ g :=
  ⟨dodgeWith act f, dodgeWith_unrepresented act hl f⟩

/-! ## Bool reading -/

/-- On Bool, `not` has no fixed point (`TwoCycle.bool_fundamental`). -/
theorem not_restless : ∀ b : Bool, (!b) ≠ b :=
  TwoCycle.bool_fundamental.1

/-- No `f : A → A → Bool` is point-surjective. -/
theorem seal_bool {A : Type} (f : A → A → Bool) : ¬ PointSurjective f :=
  seal_on_fundamental not TwoCycle.bool_fundamental.1 f

/-- Bool instance of `dodgeWith` for `not`. -/
def dodge {A : Type} (f : A → A → Bool) : A → Bool :=
  dodgeWith not f

theorem dodge_unrepresented {A : Type} (f : A → A → Bool) :
    ∀ a, f a ≠ dodge f :=
  dodgeWith_unrepresented not TwoCycle.bool_fundamental.1 f

/-- Classical Cantor: no surjection onto `A → Bool`. -/
theorem cantor {A : Type} (f : A → A → Bool) :
    ∃ g : A → Bool, ∀ a, f a ≠ g :=
  cantor_fundamental not TwoCycle.bool_fundamental.1 f

/-! ## Necessity of liveness -/

/-- If `g` has a fixed point, then fixed points exist; liveness is required
    for the contrapositive in `no_point_surjection`. -/
theorem resting_law_permits_fixed_point {B : Type} (g : B → B) (b : B)
    (hb : g b = b) : ∃ b', g b' = b' :=
  ⟨b, hb⟩

theorem resting_law_dodge_realised {α : Type} (act : α → α) (b : α)
    (hb : act b = b) :
    ∃ (A : Type) (f : A → A → α) (a : A), ∀ x, f a x = dodgeWith act f x :=
  ⟨Unit, fun _ _ => b, (), fun _ => hb.symm⟩

/-! ## Summary -/

/-- From liveness: no fixed points of `act`, no point-surjective
    representation, and an explicit omitted predicate. -/
theorem diagonal_package {α A : Type} (act : α → α)
    (hl : Orbit.Live act) (f : A → A → α) :
    (∀ x, act x ≠ x) ∧
    (¬ PointSurjective f) ∧
    (∃ g : A → α, ∀ a, f a ≠ g) :=
  ⟨hl, seal_on_fundamental act hl f, cantor_fundamental act hl f⟩

#print axioms Diagonal.lawvere
#print axioms Diagonal.no_point_surjection
#print axioms Diagonal.seal_on_fundamental
#print axioms Diagonal.dodgeWith_unrepresented
#print axioms Diagonal.cantor_fundamental
#print axioms Diagonal.resting_law_dodge_realised
#print axioms Diagonal.seal_bool
#print axioms Diagonal.cantor
#print axioms Diagonal.diagonal_package

end Diagonal
