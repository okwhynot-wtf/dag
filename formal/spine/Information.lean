import Canon

/-!
# Information — unit, conservation, capacity, growth

Information-theoretic restatements of spine results on the fundamental,
losslessness, diagonal seal, and ladder ascent.

* **Unit** (`fundamental_is_one_bit`): `Bool` has two states and one
  distinction; every fundamental reads bijectively as `Bool`.
* **Conservation** (`conservation`, `fundamental_conserves`): losslessness
  preserves distinct iterates; symmetric step implies conservation;
  erasure merges iterates (`erasure_destroys`).
* **Capacity** (`capacity_deficit`): self-readings underdetermine
  predicates at the fundamental and in general (`Diagonal.seal_bool`).
* **Growth** (`information_grows`): strict ladder gain at each tick with
  injective lifting and conservative embedding.

No declared axioms.
-/
namespace Information

/-! ## The unit -/

/-- `Bool` has two elements and one distinction; any `IsFundamental` act
    reads bijectively as `Bool` at any seed. -/
theorem fundamental_is_one_bit :
    (∀ b : Bool, b = true ∨ b = false) ∧
    (true ≠ false) ∧
    (∀ {α : Type} (act : α → α), Canon.IsFundamental act → ∀ z : α,
      (∀ x, ∃ b, TwoCycle.reading act z b = x) ∧
      (∀ b b', TwoCycle.reading act z b = TwoCycle.reading act z b' →
        b = b')) := by
  refine ⟨?_, by decide, ?_⟩
  · intro b
    cases b
    · exact Or.inr rfl
    · exact Or.inl rfl
  · intro α act h z
    exact ⟨TwoCycle.reading_surjective act h.exhaustive z,
           TwoCycle.reading_injective act h.live z⟩

/-! ## Conservation -/

/-- Lossless acts preserve inequality under iteration. -/
theorem conservation {α : Type} (act : α → α) (hL : Orbit.Lossless act)
    {x y : α} (h : x ≠ y) :
    ∀ n, Orbit.iter act n x ≠ Orbit.iter act n y := by
  intro n he
  exact h (Orbit.iter_lossless act hL n x y he)

/-- Symmetric-step acts are lossless and conserve distinctions under
    iteration. -/
theorem fundamental_conserves {α : Type} (act : α → α)
    (hs : Orbit.SymmetricStep act) {x y : α} (h : x ≠ y) :
    ∀ n, Orbit.iter act n x ≠ Orbit.iter act n y :=
  conservation act (Orbit.symmetric_lossless act hs) h

/-- Erasing acts merge some distinct pair from the first iterate onward. -/
theorem erasure_destroys {α : Type} (act : α → α)
    (h : Orbit.Erasing act) :
    ∃ x y : α, x ≠ y ∧ ∀ n,
      Orbit.iter act (n + 1) x = Orbit.iter act (n + 1) y :=
  Orbit.erasing_forever act h

/-! ## Capacity -/

/-- At the fundamental, some predicate pair escapes every self-reading; in
    general, no `Bool`-valued map is point-surjective. -/
theorem capacity_deficit :
    (∀ f : Bool → Bool → Bool,
      ∃ g h : Bool → Bool,
        (∃ x, g x ≠ h x) ∧
        (∀ a, ∃ x, f a x ≠ g x) ∧
        (∀ a, ∃ x, f a x ≠ h x)) ∧
    (∀ (A : Type) (f : A → A → Bool), ¬ Diagonal.PointSurjective f) :=
  ⟨Tower.underdetermined_at_fundamental, fun _ f => Diagonal.seal_bool f⟩

/-! ## Growth -/

/-- Each ladder step adds a new element; lifting is injective and
    representation-preserving. -/
theorem information_grows :
    (∀ k, ∀ a : Ladder.Level k,
      (some a : Ladder.Level (k + 1)) ≠ none) ∧
    (∀ k j, ∀ x y : Ladder.Level k, x ≠ y →
      Ladder.lift k j x ≠ Ladder.lift k j y) ∧
    (∀ k j, ∀ x y : Ladder.Level k,
      Ladder.rep (k + j) (Ladder.lift k j x) (Ladder.lift k j y) =
        Ladder.rep k x y) := by
  refine ⟨Ladder.none_is_new, ?_, Ladder.lift_conservative⟩
  intro k j x y hxy he
  exact hxy (Ladder.lift_injective k j x y he)

/-! ## Summary -/

/-- Collected information-theoretic restatements. -/
theorem information_package :
    (∀ b : Bool, b = true ∨ b = false) ∧
    (∀ {α : Type} (act : α → α), Orbit.SymmetricStep act →
      ∀ {x y : α}, x ≠ y →
        ∀ n, Orbit.iter act n x ≠ Orbit.iter act n y) ∧
    (∀ (A : Type) (f : A → A → Bool), ¬ Diagonal.PointSurjective f) ∧
    (∀ k, ∀ a : Ladder.Level k,
      (some a : Ladder.Level (k + 1)) ≠ none) :=
  ⟨fundamental_is_one_bit.1,
   fun {_α} act hs {_x _y} h => fundamental_conserves act hs h,
   fun _ f => Diagonal.seal_bool f,
   Ladder.none_is_new⟩

#print axioms Information.fundamental_is_one_bit
#print axioms Information.conservation
#print axioms Information.fundamental_conserves
#print axioms Information.erasure_destroys
#print axioms Information.capacity_deficit
#print axioms Information.information_grows
#print axioms Information.information_package

end Information
