/-!
# Orbit — classification of iteration by a self-map

For `act : α → α`, the step relation `Step act x y` holds when `y = act x`.
The file classifies local and global orbit behaviour: rest, two-cycle,
asymmetric step, erased pair, and collision-free embedding of ℕ.

* **Erasing** (`Erasing`, `erasing_forever`): distinct states with a common
  successor coincide under all positive iterates.
* **Collision-free embedding** (`nat_embedding_of_no_collision`): from a seed
  with no collision, iteration is injective and matches the successor law on ℕ.
* **Asymmetric step** (`arrow_of_not_involutive`): non-involutivity at `z`
  yields `Step act z (act z)` and not `Step act (act z) z`.
* **Two-cycle** (`two_cycle`): a live act with symmetric steps is a
  fixed-point-free involution with two-point orbits.

`symmetricStep_iff_involutive` identifies symmetry of the step relation with
involutivity. A live symmetric act collides in two steps
(`symmetric_live_collides`); non-involutivity at the seed follows from a
collision-free orbit (`no_collision_forces_arrow`) without a finiteness
hypothesis.

Prelude only; no imports; no declared axioms.
-/
namespace Orbit

variable {α : Type}

/-! ## Step relation and predicates -/

/-- The step relation of an act: `y` is the immediate successor of `x`. -/
def Step (act : α → α) (x y : α) : Prop := y = act x

/-- The step relation is symmetric: each step admits a reverse step. -/
def SymmetricStep (act : α → α) : Prop :=
  ∀ x y, Step act x y → Step act y x

/-- The act has no fixed point. -/
def Live (act : α → α) : Prop := ∀ x, act x ≠ x

/-- Distinct states have distinct successors. -/
def Lossless (act : α → α) : Prop := ∀ x y, act x = act y → x = y

/-- Some distinct states share a successor. -/
def Erasing (act : α → α) : Prop := ∃ x y, x ≠ y ∧ act x = act y

/-- Iterate the act. -/
def iter (act : α → α) : Nat → α → α
  | 0, x => x
  | n + 1, x => act (iter act n x)

/-- The orbit from `z` revisits a state. -/
def Collides (act : α → α) (z : α) : Prop :=
  ∃ i j : Nat, i < j ∧ iter act i z = iter act j z

/-! ## Symmetry and involutivity -/

/-- Symmetry of the step relation is equivalent to involutivity of the act. -/
theorem symmetricStep_iff_involutive (act : α → α) :
    SymmetricStep act ↔ ∀ x, act (act x) = x := by
  constructor
  · intro h x
    have hx : Step act (act x) x := h x (act x) rfl
    exact hx.symm
  · intro h x y hxy
    subst hxy
    show x = act (act x)
    exact (h x).symm

/-! ## Orientation -/

/-- If `act` is not involutive at `z`, then `Step act z (act z)` holds and
    `Step act (act z) z` does not. -/
theorem arrow_of_not_involutive (act : α → α) (z : α)
    (h : act (act z) ≠ z) :
    Step act z (act z) ∧ ¬ Step act (act z) z :=
  ⟨rfl, fun hs => h hs.symm⟩

/-- On a decidable carrier, at each `z` the act rests, closes a two-cycle at
    `z`, or fails to be involutive at `z`. -/
theorem trichotomy [DecidableEq α] (act : α → α) (z : α) :
    act z = z ∨
    (act z ≠ z ∧ act (act z) = z) ∨
    act (act z) ≠ z :=
  if h1 : act (act z) = z then
    if h0 : act z = z then Or.inl h0
    else Or.inr (Or.inl ⟨h0, h1⟩)
  else Or.inr (Or.inr h1)

/-! ## Rest -/

/-- From a fixed point, every iterate remains at that point. -/
theorem rest_is_stagnation (act : α → α) {z : α} (hz : act z = z) :
    ∀ n, iter act n z = z := by
  intro n
  induction n with
  | zero => rfl
  | succ k ih =>
    show act (iter act k z) = z
    rw [ih, hz]

/-- If `act (act z) = z`, then every iterate from `z` is `z` or `act z`. -/
theorem two_cycle_at (act : α → α) {z : α} (hinv : act (act z) = z) :
    ∀ n, iter act n z = z ∨ iter act n z = act z := by
  intro n
  induction n with
  | zero => exact Or.inl rfl
  | succ k ih =>
    cases ih with
    | inl h =>
      apply Or.inr
      show act (iter act k z) = act z
      rw [h]
    | inr h =>
      apply Or.inl
      show act (iter act k z) = z
      rw [h]
      exact hinv

/-- Pointwise classification on a decidable carrier: at `z` the orbit rests,
    is a two-cycle, or has an asymmetric step; the three cases are disjoint.
    Mixed global behaviour is classified state by state. Erasure is treated
    separately (`erasing_forever`); a collision-free seed yields an asymmetric
    step (`no_collision_forces_arrow`). -/
theorem classification_at [DecidableEq α] (act : α → α) (z : α) :
    (act z = z ∧ ∀ n, iter act n z = z) ∨
    (act z ≠ z ∧ act (act z) = z ∧
      ∀ n, iter act n z = z ∨ iter act n z = act z) ∨
    (act (act z) ≠ z ∧
      Step act z (act z) ∧ ¬ Step act (act z) z) := by
  cases trichotomy act z with
  | inl h => exact Or.inl ⟨h, rest_is_stagnation act h⟩
  | inr h =>
    cases h with
    | inl h =>
      exact Or.inr (Or.inl ⟨h.1, h.2, two_cycle_at act h.2⟩)
    | inr h =>
      exact Or.inr (Or.inr ⟨h, arrow_of_not_involutive act z h⟩)

/-- The three cases of `classification_at` are pairwise incompatible. -/
theorem classification_exclusive (act : α → α) (z : α) :
    ¬ ((act z = z) ∧ (act z ≠ z ∧ act (act z) = z)) ∧
    ¬ ((act z = z) ∧ (act (act z) ≠ z)) ∧
    ¬ ((act z ≠ z ∧ act (act z) = z) ∧ (act (act z) ≠ z)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro ⟨hrest, hne, _⟩; exact hne hrest
  · intro ⟨hrest, harrow⟩
    exact harrow (by rw [hrest, hrest])
  · intro ⟨⟨_, hinv⟩, harrow⟩; exact harrow hinv

/-! ## Erasure -/

theorem erased_pair_forever (act : α → α) {x y : α} (h : act x = act y) :
    ∀ n, iter act (n + 1) x = iter act (n + 1) y := by
  intro n
  induction n with
  | zero =>
    show act (iter act 0 x) = act (iter act 0 y)
    exact h
  | succ k ih =>
    show act (iter act (k + 1) x) = act (iter act (k + 1) y)
    rw [ih]

/-- Some distinct pair with a common successor agrees under all positive
    iterates. -/
theorem erasing_forever (act : α → α) (h : Erasing act) :
    ∃ x y, x ≠ y ∧ ∀ n, iter act (n + 1) x = iter act (n + 1) y :=
  let ⟨x, y, hxy, hact⟩ := h
  ⟨x, y, hxy, erased_pair_forever act hact⟩

/-! ## Collision-free orbit -/

/-- From a seed with no collision, iteration is injective and satisfies
    `iter act (n + 1) z = act (iter act n z)`. -/
theorem nat_embedding_of_no_collision (act : α → α) (z : α)
    (h : ¬ Collides act z) :
    (∀ i j : Nat, iter act i z = iter act j z → i = j) ∧
    (∀ n, iter act (n + 1) z = act (iter act n z)) := by
  constructor
  · intro i j hij
    cases Nat.lt_or_ge i j with
    | inl hlt => exact absurd ⟨i, j, hlt, hij⟩ h
    | inr hge =>
      cases Nat.eq_or_lt_of_le hge with
      | inl he => exact he.symm
      | inr hgt => exact absurd ⟨j, i, hgt, hij.symm⟩ h
  · intro n
    rfl

/-- On a collision-free orbit, distinct indices yield distinct iterates. -/
theorem iter_lt_of_no_collision (act : α → α) (z : α)
    (h : ¬ Collides act z) {i j : Nat} (hij : i < j) :
    iter act i z ≠ iter act j z :=
  fun he => Nat.ne_of_lt hij ((nat_embedding_of_no_collision act z h).1 i j he)

/-- Successor on a collision-free orbit is the act. -/
theorem iter_succ_of_no_collision (act : α → α) (z : α)
    (h : ¬ Collides act z) (n : Nat) :
    iter act (n + 1) z = act (iter act n z) :=
  (nat_embedding_of_no_collision act z h).2 n

/-- A collision-free orbit from `z` is not involutive at `z`. -/
theorem no_collision_forces_arrow (act : α → α) (z : α)
    (h : ¬ Collides act z) : act (act z) ≠ z := by
  intro h2
  exact h ⟨0, 2, by decide, show z = act (act z) from h2.symm⟩

/-! ## Recurrence under losslessness -/

/-- Iteration of a lossless act is lossless. -/
theorem iter_lossless (act : α → α) (h : Lossless act) (n : Nat) :
    ∀ x y, iter act n x = iter act n y → x = y := by
  induction n with
  | zero => intro x y e; exact e
  | succ k ih =>
    intro x y e
    exact ih x y (h _ _ e)

theorem iter_add (act : α → α) (m n : Nat) (x : α) :
    iter act (m + n) x = iter act m (iter act n x) := by
  induction m with
  | zero =>
    rw [Nat.zero_add]
    rfl
  | succ k ih =>
    rw [Nat.succ_add]
    show act (iter act (k + n) x) = act (iter act k (iter act n x))
    rw [ih]

def Reaches (act : α → α) (x y : α) : Prop :=
  ∃ k, iter act k x = y

theorem reaches_iff_le_of_no_collision (act : α → α) (z : α)
    (h : ¬ Collides act z) (i j : Nat) :
    Reaches act (iter act i z) (iter act j z) ↔ i ≤ j := by
  constructor
  · intro ⟨k, hk⟩
    rw [← iter_add] at hk
    have hkij : k + i = j :=
      (nat_embedding_of_no_collision act z h).1 (k + i) j hk
    exact hkij ▸ Nat.le_add_left i k
  · intro hij
    obtain ⟨k, hk⟩ := Nat.le.dest hij
    refine ⟨k, ?_⟩
    rw [← iter_add, Nat.add_comm k i, hk]

/-- Under losslessness, any collision yields a positive period returning to the
    seed. -/
theorem collision_returns (act : α → α) (hL : Lossless act) (z : α)
    (h : Collides act z) : ∃ p : Nat, 0 < p ∧ iter act p z = z := by
  obtain ⟨i, j, hij, he⟩ := h
  obtain ⟨k, hk⟩ := Nat.le.dest hij
  refine ⟨k + 1, Nat.zero_lt_succ k, ?_⟩
  have hd : i + (k + 1) = j :=
    ((Nat.add_succ i k).trans (Nat.succ_add i k).symm).trans hk
  have key : iter act i (iter act (k + 1) z) = iter act i z := by
    rw [← iter_add, hd]
    exact he.symm
  exact iter_lossless act hL i _ _ key

/-! ## Symmetric live act -/

/-- A live act with symmetric steps is involutive without fixed points, and
    every orbit from any seed is a two-point cycle. -/
theorem two_cycle (act : α → α) (hs : SymmetricStep act) (hl : Live act) :
    ∀ z, act (act z) = z ∧ act z ≠ z ∧
      (∀ n, iter act n z = z ∨ iter act n z = act z) := by
  have hinv := (symmetricStep_iff_involutive act).mp hs
  intro z
  refine ⟨hinv z, hl z, ?_⟩
  intro n
  induction n with
  | zero => exact Or.inl rfl
  | succ k ih =>
    cases ih with
    | inl h =>
      apply Or.inr
      show act (iter act k z) = act z
      rw [h]
    | inr h =>
      apply Or.inl
      show act (iter act k z) = z
      rw [h]
      exact hinv z

/-- A symmetric act collides at the seed in two steps. -/
theorem symmetric_live_collides (act : α → α) (hs : SymmetricStep act)
    (z : α) : Collides act z := by
  have hinv := (symmetricStep_iff_involutive act).mp hs
  exact ⟨0, 2, by decide, show z = act (act z) from (hinv z).symm⟩

/-- A symmetric act is lossless. -/
theorem symmetric_lossless (act : α → α) (hs : SymmetricStep act) :
    Lossless act := by
  have hinv := (symmetricStep_iff_involutive act).mp hs
  intro x y h
  have : act (act x) = act (act y) := by rw [h]
  rw [hinv x, hinv y] at this
  exact this

/-! ## Void as excluded fixed point

Naming lemmas for the fixed-point reading of liveness. The interpretive
overlay (ex nihilo as substrate-denial) lives in the paper; these theorems
assert only the mathematics. -/

/-- Liveness is fixed-point-freeness: under a live act, no state is fixed. -/
theorem void_is_excluded_fixed_point (act : α → α) (h : Live act) :
    ∀ x, act x ≠ x :=
  h

/-- A fixed point at any state refutes liveness. -/
theorem fixed_point_refutes_liveness (act : α → α) (x : α)
    (h : act x = x) : ¬ Live act :=
  fun hl => hl x h

/-! ## Summary -/

/-- Global consequences: rest implies stagnation; non-involutivity yields an
    asymmetric step; erasure persists; collision-free seeds embed ℕ and are
    non-involutive at the seed; a live symmetric act is a two-cycle. Pointwise
    detail is in `classification_at`. -/
theorem classification (act : α → α) :
    (∀ z, act z = z → ∀ n, iter act n z = z) ∧
    (∀ z, act (act z) ≠ z →
      Step act z (act z) ∧ ¬ Step act (act z) z) ∧
    (Erasing act →
      ∃ x y, x ≠ y ∧ ∀ n, iter act (n + 1) x = iter act (n + 1) y) ∧
    (∀ z, ¬ Collides act z →
      (∀ i j : Nat, iter act i z = iter act j z → i = j) ∧
      act (act z) ≠ z) ∧
    (SymmetricStep act → Live act →
      ∀ z, act (act z) = z ∧ act z ≠ z ∧
        (∀ n, iter act n z = z ∨ iter act n z = act z)) :=
  ⟨fun _z h => rest_is_stagnation act h,
   fun z h => arrow_of_not_involutive act z h,
   fun h => erasing_forever act h,
   fun z h => ⟨(nat_embedding_of_no_collision act z h).1,
               no_collision_forces_arrow act z h⟩,
   fun hs hl => two_cycle act hs hl⟩

#print axioms Orbit.symmetricStep_iff_involutive
#print axioms Orbit.arrow_of_not_involutive
#print axioms Orbit.trichotomy
#print axioms Orbit.rest_is_stagnation
#print axioms Orbit.two_cycle_at
#print axioms Orbit.classification_at
#print axioms Orbit.erased_pair_forever
#print axioms Orbit.erasing_forever
#print axioms Orbit.reaches_iff_le_of_no_collision
#print axioms Orbit.nat_embedding_of_no_collision
#print axioms Orbit.no_collision_forces_arrow
#print axioms Orbit.collision_returns
#print axioms Orbit.two_cycle
#print axioms Orbit.symmetric_live_collides
#print axioms Orbit.symmetric_lossless
#print axioms Orbit.classification
#print axioms Orbit.void_is_excluded_fixed_point
#print axioms Orbit.fixed_point_refutes_liveness

end Orbit
