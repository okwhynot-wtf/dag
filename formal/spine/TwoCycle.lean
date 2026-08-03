import Orbit

/-!
# TwoCycle — canonical Bool coordinates for a live symmetric act

From `Orbit.two_cycle`, a live act with symmetric steps is a fixed-point-free
involution with two-point orbits. This file constructs canonical Bool
coordinates, proves uniqueness, and records standard models.

* **Reading** (`reading`, `reading_injective`, `reading_surjective`): injective
  Bool-indexed naming of the two orbit sides from a seed; surjective when
  `Generated act` holds.
* **Negation law** (`act_reads_as_not`): under `reading act z`, the act is
  Boolean negation.
* **Uniqueness** (`reading_unique`, `two_readings`): the pointed equivariant
  map is unique; unpointed, exactly two labelings differ by swapping sides.
* **Bool law** (`bool_live_is_not`): on Bool, liveness forces `f = not`.
* **Models** (`bool_fundamental`, `coproduct_fundamental`): `(Bool, not)` and
  `(Unit ⊕ Unit, swapU)` satisfy live, symmetric, and generated hypotheses.
* **Witness recovery** (`witnessed_fundamental`): `TDiff` and `Alive` for the
  identity Bool witness.

Prelude only; no declared axioms.
-/
namespace TwoCycle

open Orbit

variable {α : Type}

/-- Every state is the seed or its image under the act. -/
def Generated (act : α → α) : Prop :=
  ∀ x y : α, y = x ∨ y = act x

/-! ## Canonical coordinates -/

/-- Bool-indexed naming from seed `z`: `true` maps to `z`, `false` to `act z`. -/
def reading (act : α → α) (z : α) : Bool → α
  | true => z
  | false => act z

theorem reading_equivariant (act : α → α) (hs : SymmetricStep act)
    (z : α) : ∀ b, reading act z (!b) = act (reading act z b) := by
  intro b
  cases b with
  | true => rfl
  | false =>
    show z = act (act z)
    exact (((symmetricStep_iff_involutive act).mp hs) z).symm

/-- Under `reading act z`, the act acts as Boolean negation on indices. -/
theorem act_reads_as_not (act : α → α) (hs : SymmetricStep act) (z : α) :
    ∀ b, act (reading act z b) = reading act z (!b) := by
  intro b
  exact (reading_equivariant act hs z b).symm

theorem reading_injective (act : α → α) (hl : Live act) (z : α) :
    ∀ b b', reading act z b = reading act z b' → b = b' := by
  intro b b' h
  cases b with
  | true =>
    cases b' with
    | true => rfl
    | false => exact absurd h.symm (hl z)
  | false =>
    cases b' with
    | true => exact absurd h (hl z)
    | false => rfl

theorem reading_surjective (act : α → α) (hgen : Generated act) (z : α) :
    ∀ x, ∃ b, reading act z b = x := by
  intro x
  cases hgen z x with
  | inl h => exact ⟨true, h.symm⟩
  | inr h => exact ⟨false, h.symm⟩

/-! ## Uniqueness -/

/-- An equivariant map `e : Bool → α` with `e true = z` agrees with
    `reading act z` on every index. -/
theorem reading_unique (act : α → α) (z : α) (e : Bool → α)
    (he : e true = z) (heq : ∀ b, e (!b) = act (e b)) :
    ∀ b, e b = reading act z b := by
  intro b
  cases b with
  | true => exact he
  | false =>
    show e false = act z
    have h1 : e false = act (e true) := heq true
    rw [h1, he]

/-- An equivariant map on a generated carrier equals `reading act z` or its
    side swap by negation of indices. -/
theorem two_readings (act : α → α) (hs : SymmetricStep act) (z : α)
    (e : Bool → α) (heq : ∀ b, e (!b) = act (e b))
    (hgen : Generated act) :
    (∀ b, e b = reading act z b) ∨ (∀ b, e b = reading act z (!b)) := by
  have hinv := (symmetricStep_iff_involutive act).mp hs
  cases hgen z (e true) with
  | inl h =>
    exact Or.inl (reading_unique act z e h heq)
  | inr h =>
    apply Or.inr
    intro b
    cases b with
    | true => exact h
    | false =>
      show e false = z
      have h1 : e false = act (e true) := heq true
      rw [h1, h]
      exact hinv z

/-! ## Pole swap and indiscernibility -/

/-- Negation is an equivariant bijection of the canon onto itself, swapping
    the two poles. Equivariance is the intertwining `e (!b) = !(e b)`. -/
theorem pole_swap_automorphism :
    (∀ b : Bool, not (!b) = !(not b)) ∧
    (∀ b b' : Bool, not b = not b' → b = b') ∧
    (∀ b : Bool, ∃ b' : Bool, not b' = b) := by
  refine ⟨?_, ?_, ?_⟩
  · intro b; cases b <;> rfl
  · intro b b' h; cases b <;> cases b' <;> first | rfl | cases h
  · intro b; exact ⟨!b, by cases b <;> rfl⟩

/-- Any Bool-predicate invariant under the pole swap takes the same value at
    both poles. A pole-distinguishing fact must break that invariance. -/
theorem poles_indiscernible (P : Bool → Bool)
    (hP : ∀ x, P (not x) = P x) :
    P true = P false :=
  (hP true).symm

/-! ## Law on the reading -/

/-- On Bool, a live endomap equals `not` at every point. -/
theorem bool_live_is_not (f : Bool → Bool) (hl : Live f) :
    ∀ b, f b = !b := by
  intro b
  cases b with
  | false =>
    cases hf : f false with
    | false => exact absurd hf (hl false)
    | true => rfl
  | true =>
    cases ht : f true with
    | false => rfl
    | true => exact absurd ht (hl true)

/-! ## Models -/

/-- `(Bool, not)` is live, symmetric, and generated. -/
theorem bool_fundamental :
    Live not ∧ SymmetricStep not ∧ Generated not := by
  refine ⟨?_, ?_, ?_⟩
  · intro b; cases b <;> decide
  · intro x y h
    subst h
    show x = !(!x)
    cases x <;> rfl
  · intro x y
    cases x <;> cases y
    · exact Or.inl rfl
    · exact Or.inr rfl
    · exact Or.inr rfl
    · exact Or.inl rfl

/-- Involution swapping the two components of `Unit ⊕ Unit`. -/
def swapU : Unit ⊕ Unit → Unit ⊕ Unit
  | .inl _ => .inr ()
  | .inr _ => .inl ()

/-- `(Unit ⊕ Unit, swapU)` is live, symmetric, and generated. -/
theorem coproduct_fundamental :
    Live swapU ∧ SymmetricStep swapU ∧ Generated swapU := by
  refine ⟨?_, ?_, ?_⟩
  · intro s
    cases s with
    | inl u =>
      intro h
      have h' : Sum.inr () = Sum.inl u := h
      cases h'
    | inr u =>
      intro h
      have h' : Sum.inl () = Sum.inr u := h
      cases h'
  · intro x y h
    subst h
    cases x with
    | inl u => cases u; rfl
    | inr u => cases u; rfl
  · intro x y
    cases x with
    | inl u =>
      cases u
      cases y with
      | inl v => cases v; exact Or.inl rfl
      | inr v => cases v; exact Or.inr rfl
    | inr u =>
      cases u
      cases y with
      | inl v => cases v; exact Or.inr rfl
      | inr v => cases v; exact Or.inl rfl

/-! ## Witness predicates -/

/-- Context-free witness: the xor of summaries is invariant under the act. -/
def TDiff (summ : α → Bool) (act : α → α) : Prop :=
  ∀ z w : α, (summ (act z) ^^ summ z) = (summ (act w) ^^ summ w)

/-- Alive witness: the xor at the base point is `true`. -/
def Alive (summ : α → Bool) (act : α → α) (z₀ : α) : Prop :=
  (summ (act z₀) ^^ summ z₀) = true

/-- For the identity Bool witness and `not`, `TDiff` and `Alive` hold at
    `true`. -/
theorem witnessed_fundamental :
    TDiff (fun b : Bool => b) not ∧ Alive (fun b : Bool => b) not true :=
  ⟨fun z w => by cases z <;> cases w <;> rfl, rfl⟩

/-! ## Summary -/

/-- A live symmetric generated act admits canonical Bool coordinates with
    negation equivariance, injectivity, surjectivity, pointed uniqueness, and
    `bool_live_is_not`. -/
theorem fundamental_package (act : α → α) (hl : Live act)
    (hs : SymmetricStep act) (hgen : Generated act) (z : α) :
    (∀ b, act (reading act z b) = reading act z (!b)) ∧
    (∀ b b', reading act z b = reading act z b' → b = b') ∧
    (∀ x, ∃ b, reading act z b = x) ∧
    (∀ e : Bool → α, e true = z → (∀ b, e (!b) = act (e b)) →
      ∀ b, e b = reading act z b) ∧
    (∀ f : Bool → Bool, Live f → ∀ b, f b = !b) :=
  ⟨act_reads_as_not act hs z,
   reading_injective act hl z,
   reading_surjective act hgen z,
   fun e he heq => reading_unique act z e he heq,
   fun f hf => bool_live_is_not f hf⟩

#print axioms TwoCycle.reading_equivariant
#print axioms TwoCycle.act_reads_as_not
#print axioms TwoCycle.reading_injective
#print axioms TwoCycle.reading_surjective
#print axioms TwoCycle.reading_unique
#print axioms TwoCycle.two_readings
#print axioms TwoCycle.pole_swap_automorphism
#print axioms TwoCycle.poles_indiscernible
#print axioms TwoCycle.bool_live_is_not
#print axioms TwoCycle.bool_fundamental
#print axioms TwoCycle.coproduct_fundamental
#print axioms TwoCycle.witnessed_fundamental
#print axioms TwoCycle.fundamental_package

end TwoCycle
