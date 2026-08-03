import Ladder
import Cause

/-!
# Limit — ω-colimit and ω+1 extension

The finite ladder is the ω-chain of naming extensions. Its colimit is
represented without quotients by first-appearance normal forms: each
element is either a fundamental bit or the namer introduced at a definite
stage. The limit carries a coherent self-reading; the seal applies; the
successor `Option` construction yields level ω+1.

* **Representation** (`LevelOmega`): `base b` | `stage k` (the `none`
  introduced at level `k+1`), with decidable equality.
* **Embeddings** (`embed`, `embed_injective`, `realize_embed`,
  `limit_conservative`, `limit_reading_conservative`): each finite level
  embeds injectively; realizing an embedded element recovers it; the
  limit reading agrees with the finite reading on embedded pairs.
* **Seal** (`limit_sealed`, `repOmega`): Lawvere on the limit reading.
* **Successor** (`LevelOmegaPlusOne`, `omega_plus_one_step`): naming
  extension past ω.
* **No settling** (`no_ordinal_settling`): every finite stage of the
  ω-tail still ascends.

No declared axioms; no `Quot`.
-/
namespace Limit

/-! ## First-appearance colimit -/

/-- Colimit carrier: fundamental bits, or the namer first appearing at stage
    `k+1` (i.e. `none` at `Ladder.Level (k+1)`). -/
inductive LevelOmega where
  | base : Bool → LevelOmega
  | stage : Nat → LevelOmega

open LevelOmega

theorem base_inj {a b : Bool} (h : base a = base b) : a = b :=
  LevelOmega.base.inj h

theorem stage_inj {m n : Nat} (h : stage m = stage n) : m = n :=
  LevelOmega.stage.inj h

instance : DecidableEq LevelOmega
  | base a, base b =>
    match decEq a b with
    | isTrue h => isTrue (congrArg base h)
    | isFalse n => isFalse fun h => n (base_inj h)
  | stage m, stage n =>
    match decEq m n with
    | isTrue h => isTrue (congrArg stage h)
    | isFalse n => isFalse fun h => n (stage_inj h)
  | base _, stage _ => isFalse fun h => by cases h
  | stage _, base _ => isFalse fun h => by cases h

/-- Stage at which an element first appears. -/
def appearsBy : LevelOmega → Nat
  | base _ => 0
  | stage k => k + 1

/-- Embed a finite level into the colimit by erasing `some` wrappers. -/
def embed : (k : Nat) → Ladder.Level k → LevelOmega
  | 0, b => base b
  | k + 1, none => stage k
  | k + 1, some x => embed k x

theorem embed_appears (k : Nat) (x : Ladder.Level k) :
    appearsBy (embed k x) ≤ k := by
  induction k with
  | zero => cases x <;> exact Nat.zero_le _
  | succ n ih =>
    match x with
    | none => exact Nat.le_refl _
    | some a => exact Nat.le_trans (ih a) (Nat.le_succ n)

theorem embed_ne_stage (k : Nat) (x : Ladder.Level k) :
    embed k x ≠ stage k := by
  intro h
  have hab := embed_appears k x
  rw [h, appearsBy] at hab
  exact Nat.not_succ_le_self k hab

/-- `embed` is injective at each level. -/
theorem embed_injective (k : Nat) :
    ∀ x y : Ladder.Level k, embed k x = embed k y → x = y := by
  induction k with
  | zero =>
    intro x y h
    cases x <;> cases y <;> first
      | rfl
      | cases h
  | succ n ih =>
    intro x y h
    match x, y with
    | none, none => rfl
    | none, some b => exact absurd h (embed_ne_stage n b).symm
    | some a, none => exact absurd h.symm (embed_ne_stage n a).symm
    | some a, some b => exact congrArg some (ih a b h)

/-- Realize a colimit element as a finite-level element by padding with
    `some`. Meaningful when `appearsBy x ≤ k`. -/
def realize : (k : Nat) → LevelOmega → Ladder.Level k
  | 0, base b => b
  | 0, stage _ => false
  | k + 1, base b => some (realize k (base b))
  | k + 1, stage n =>
      match decEq n k with
      | isTrue _ => none
      | isFalse _ => some (realize k (stage n))

/-- Realizing an element already present at level `n` as level `n+1`
    wraps with `some`. -/
theorem realize_succ_of_embed (n : Nat) (a : Ladder.Level n) :
    realize (n + 1) (embed n a) = some (realize n (embed n a)) := by
  cases h : embed n a with
  | base b => rfl
  | stage m =>
    dsimp [realize]
    cases hd : decEq m n with
    | isTrue heq =>
      have h' : embed n a = stage n := heq ▸ h
      exact absurd h' (embed_ne_stage n a)
    | isFalse _ => rfl

/-- Realizing an embedded element at its own level recovers it. -/
theorem realize_embed (k : Nat) (x : Ladder.Level k) :
    realize k (embed k x) = x := by
  induction k with
  | zero => cases x <;> rfl
  | succ n ih =>
    cases x with
    | none =>
      dsimp [embed, realize]
      cases h : decEq n n with
      | isTrue _ => rfl
      | isFalse ne => exact absurd rfl ne
    | some a =>
      dsimp [embed]
      rw [realize_succ_of_embed n a, ih a]

theorem realize_succ_of_appears (j : Nat) (u : LevelOmega)
    (h : appearsBy u ≤ j) :
    realize (j + 1) u = some (realize j u) := by
  cases u with
  | base b => rfl
  | stage n =>
    dsimp [realize]
    cases hd : decEq n j with
    | isTrue heq =>
      subst heq
      exact absurd h (Nat.not_succ_le_self n)
    | isFalse _ => rfl

theorem rep_realize_stable (m : Nat) (u v : LevelOmega)
    (hu : appearsBy u ≤ m) (hv : appearsBy v ≤ m) :
    ∀ j, m ≤ j →
      Ladder.rep j (realize j u) (realize j v) =
        Ladder.rep m (realize m u) (realize m v) := by
  intro j
  induction j with
  | zero =>
    intro hj
    have hm : m = 0 := Nat.le_zero.mp hj
    subst hm
    rfl
  | succ i ih =>
    intro hj
    cases Nat.eq_or_lt_of_le hj with
    | inl heq =>
      subst heq
      rfl
    | inr hlt =>
      have hmi : m ≤ i := Nat.le_of_lt_succ hlt
      rw [realize_succ_of_appears i u (Nat.le_trans hu hmi),
          realize_succ_of_appears i v (Nat.le_trans hv hmi)]
      show Ladder.rep i (realize i u) (realize i v) =
        Ladder.rep m (realize m u) (realize m v)
      exact ih hmi

/-- Limit self-reading via realization at a common late stage. -/
def repOmega (x y : LevelOmega) : Bool :=
  let k := Nat.max (appearsBy x) (appearsBy y)
  Ladder.rep k (realize k x) (realize k y)

/-- Reading the stage-`k` realizations of an embedded pair with `rep k`
    recovers the finite reading. -/
theorem limit_conservative (k : Nat) (x y : Ladder.Level k) :
    Ladder.rep k (realize k (embed k x)) (realize k (embed k y)) =
      Ladder.rep k x y := by
  rw [realize_embed, realize_embed]

theorem nat_max_le {a b k : Nat} (ha : a ≤ k) (hb : b ≤ k) :
    Nat.max a b ≤ k := by
  show max a b ≤ k
  rw [Nat.max_def]
  split <;> assumption

theorem nat_le_max_left (a b : Nat) : a ≤ Nat.max a b := by
  show a ≤ max a b
  rw [Nat.max_def]
  split
  · assumption
  · exact Nat.le_refl a

theorem nat_le_max_right (a b : Nat) : b ≤ Nat.max a b := by
  show b ≤ max a b
  rw [Nat.max_def]
  split
  · exact Nat.le_refl b
  · next h => exact Nat.le_of_lt (Nat.gt_of_not_le h)

theorem limit_reading_conservative (k : Nat) (x y : Ladder.Level k) :
    repOmega (embed k x) (embed k y) = Ladder.rep k x y := by
  have hM : Nat.max (appearsBy (embed k x)) (appearsBy (embed k y)) ≤ k :=
    nat_max_le (embed_appears k x) (embed_appears k y)
  show Ladder.rep (Nat.max (appearsBy (embed k x)) (appearsBy (embed k y)))
      (realize (Nat.max (appearsBy (embed k x)) (appearsBy (embed k y)))
        (embed k x))
      (realize (Nat.max (appearsBy (embed k x)) (appearsBy (embed k y)))
        (embed k y)) =
    Ladder.rep k x y
  rw [← rep_realize_stable
        (Nat.max (appearsBy (embed k x)) (appearsBy (embed k y)))
        (embed k x) (embed k y)
        (nat_le_max_left _ _) (nat_le_max_right _ _) k hM,
      realize_embed, realize_embed]

/-- Canonical dodge of the limit reading. -/
def dodgeOmega : LevelOmega → Bool :=
  fun x => !(repOmega x x)

/-- The limit reading is sealed. -/
theorem limit_sealed : ¬ Diagonal.PointSurjective repOmega :=
  Diagonal.seal_bool repOmega

/-! ## ω+1 -/

/-- Level ω+1: one new namer for the limit dodge. -/
def LevelOmegaPlusOne := Option LevelOmega

/-- Successor reading at ω+1. -/
def repOmegaPlusOne : LevelOmegaPlusOne → LevelOmegaPlusOne → Bool
  | some a, some x => repOmega a x
  | none, some x => dodgeOmega x
  | _, none => false

/-- The ω+1 step is a naming extension of the limit reading. -/
theorem omega_plus_one_step :
    Tower.NamingExtension repOmega repOmegaPlusOne some dodgeOmega :=
  Tower.of_dodge not TwoCycle.bool_fundamental.1
    (fun _ _ => rfl)
    ⟨none, fun _ => rfl⟩

/-- The namer at ω+1 is new. -/
theorem omega_plus_one_grows :
    ∃ b : LevelOmegaPlusOne, ∀ a : LevelOmega, (some a : LevelOmegaPlusOne) ≠ b :=
  Tower.strict_growth omega_plus_one_step

/-- Finite stages past ω: `Option` towers on the limit. -/
def OmegaTail : Nat → Type
  | 0 => LevelOmega
  | n + 1 => Option (OmegaTail n)

def repTail : (n : Nat) → OmegaTail n → OmegaTail n → Bool
  | 0 => repOmega
  | n + 1 => fun b x =>
    match b, x with
    | some a, some x' => repTail n a x'
    | none, some x' => !(repTail n x' x')
    | _, none => false

theorem repTail_step (n : Nat) :
    Tower.NamingExtension (repTail n) (repTail (n + 1)) some
      (fun x => !(repTail n x x)) :=
  Tower.of_dodge not TwoCycle.bool_fundamental.1
    (fun _ _ => rfl) ⟨none, fun _ => rfl⟩

/-- Every stage of the ω-tail still ascends. -/
theorem no_ordinal_settling (n : Nat) :
    ∃ b : OmegaTail (n + 1), ∀ a : OmegaTail n,
      (some a : OmegaTail (n + 1)) ≠ b :=
  Tower.strict_growth (repTail_step n)

/-- The ω-tail never settles (seal at each stage). -/
theorem tail_sealed (n : Nat) :
    ¬ Diagonal.PointSurjective (repTail n) :=
  Diagonal.seal_bool (repTail n)

/-! ## Summary -/

theorem limit_package :
    (∀ k, ∀ x y : Ladder.Level k, embed k x = embed k y → x = y) ∧
    (∀ k (x y : Ladder.Level k),
      Ladder.rep k (realize k (embed k x)) (realize k (embed k y)) =
        Ladder.rep k x y) ∧
    (∀ k (x y : Ladder.Level k),
      repOmega (embed k x) (embed k y) = Ladder.rep k x y) ∧
    (¬ Diagonal.PointSurjective repOmega) ∧
    Tower.NamingExtension repOmega repOmegaPlusOne some dodgeOmega ∧
    (∀ n, ∃ b : OmegaTail (n + 1), ∀ a : OmegaTail n,
      (some a : OmegaTail (n + 1)) ≠ b) ∧
    (∀ n, ¬ Diagonal.PointSurjective (repTail n)) :=
  ⟨embed_injective, limit_conservative, limit_reading_conservative,
   limit_sealed, omega_plus_one_step, no_ordinal_settling, tail_sealed⟩

#print axioms Limit.embed_injective
#print axioms Limit.realize_embed
#print axioms Limit.limit_conservative
#print axioms Limit.limit_reading_conservative
#print axioms Limit.limit_sealed
#print axioms Limit.omega_plus_one_step
#print axioms Limit.omega_plus_one_grows
#print axioms Limit.no_ordinal_settling
#print axioms Limit.tail_sealed
#print axioms Limit.limit_package

end Limit
