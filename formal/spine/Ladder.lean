import Tower

/-!
# Ladder — explicit ω-chain of naming extensions

Builds an ω-sequence of levels: each tick adjoins one namer for the
predecessor's dodge (`Tower.NamingExtension`). Escape-parameterised
histories that vary which unrepresented predicate is named live in
`Cause`.

* **Construction** (`Level`, `rep`, `ladder_step`): `Level 0` is `Bool`;
  `Level (k+1)` is `Option (Level k)`; `rep k` conserves `rep (k-1)` and
  `none` names the predecessor's dodge.
* **Growth** (`ladder_grows`, `none_is_new`): the namer is new at each
  tick (`Tower.strict_growth`).
* **No settling** (`ladder_never_settles`): no level is point-surjective
  (`Diagonal.seal_bool`).
* **Embeddings** (`lift`, `lift_injective`, `lift_conservative`): each
  level embeds injectively and conservatively into every later level.
* **Strict increase** (`ladder_ascends`): no earlier level exhausts a
  later one.
* **Underdetermination** (`underdetermined_at_level`): every level's
  reading omits at least two distinct predicates.

Free values on new points are left `false`; the committed ladder names
the dodge at each tick.
-/
namespace Ladder

/-- Carriers: `Bool` at level 0, then `Option` of the predecessor. -/
def Level : Nat → Type
  | 0 => Bool
  | k + 1 => Option (Level k)

/-- Self-reading at each level; successor conserves predecessor and
    `none` names the predecessor's dodge. -/
def rep : (k : Nat) → Level k → Level k → Bool
  | 0 => Tower.f₀
  | k + 1 => fun b x =>
    match b, x with
    | some a, some x' => rep k a x'
    | none, some x' => !(rep k x' x')
    | _, none => false

/-- Canonical escape at level `k`: the Lawvere dodge of `rep k`. -/
def dodgeEscape (k : Nat) : Level k → Bool :=
  fun x => !(rep k x x)

/-- `rep (k+1)` is a naming extension of `rep k` naming the dodge. -/
theorem ladder_step (k : Nat) :
    Tower.NamingExtension (rep k) (rep (k + 1)) some (dodgeEscape k) :=
  Tower.of_dodge not TwoCycle.bool_fundamental.1
    (fun _ _ => rfl) ⟨none, fun _ => rfl⟩

/-- The namer is new at each tick (`Tower.strict_growth`). -/
theorem ladder_grows (k : Nat) :
    ∃ b : Level (k + 1), ∀ a : Level k, (some a : Level (k + 1)) ≠ b :=
  Tower.strict_growth (ladder_step k)

/-- The new element is `none`. -/
theorem none_is_new (k : Nat) :
    ∀ a : Level k, (some a : Level (k + 1)) ≠ none := by
  intro a h
  have h' : (some a : Option (Level k)) = none := h
  cases h'

/-- No level is point-surjective. -/
theorem ladder_never_settles (k : Nat) :
    ¬ Diagonal.PointSurjective (rep k) :=
  Diagonal.seal_bool (rep k)

/-! ## Embeddings along the ladder -/

/-- Embed `Level k` into `Level (k+j)`. -/
def lift : (k j : Nat) → Level k → Level (k + j)
  | _, 0, x => x
  | k, j + 1, x => some (lift k j x)

/-- `lift` is injective. -/
theorem lift_injective (k j : Nat) :
    ∀ x y : Level k, lift k j x = lift k j y → x = y := by
  induction j with
  | zero => intro x y h; exact h
  | succ i ih =>
    intro x y h
    exact ih x y (Option.some.inj h)

/-- `lift` preserves readings: `rep (k+j)` agrees with `rep k` on
    embedded pairs. -/
theorem lift_conservative (k j : Nat) :
    ∀ x y : Level k, rep (k + j) (lift k j x) (lift k j y) = rep k x y := by
  induction j with
  | zero => intro x y; rfl
  | succ i ih =>
    intro x y
    show rep (k + i) (lift k i x) (lift k i y) = rep k x y
    exact ih x y

/-- No earlier level exhausts a later one: some element lies outside the
    image of `lift`. -/
theorem ladder_ascends (k j : Nat) :
    ∃ b : Level (k + (j + 1)), ∀ a : Level k, lift k (j + 1) a ≠ b := by
  refine ⟨none, ?_⟩
  intro a h
  have h' : (some (lift k j a) : Option (Level (k + j))) = none := h
  cases h'

/-! ## Underdetermination at each level -/

/-- Decidable equality of ladder levels. -/
instance decidableEqLevel : (k : Nat) → DecidableEq (Level k)
  | 0 => inferInstanceAs (DecidableEq Bool)
  | k + 1 => fun x y =>
    match x, y with
    | none, none => isTrue rfl
    | none, some _ => isFalse (fun h => by cases h)
    | some _, none => isFalse (fun h => by cases h)
    | some a, some b =>
      match decidableEqLevel k a b with
      | isTrue h => isTrue (congrArg some h)
      | isFalse n => isFalse (fun h => n (Option.some.inj h))

/-- Two distinguished points at each level. -/
def pt₀ : (k : Nat) → Level k
  | 0 => false
  | _ + 1 => none

def pt₁ : (k : Nat) → Level k
  | 0 => true
  | k + 1 => some (pt₀ k)

theorem pts_ne (k : Nat) : pt₀ k ≠ pt₁ k := by
  cases k with
  | zero => exact Bool.false_ne_true
  | succ _ => intro h; cases h

/-- Every level reading omits at least two distinct predicates. -/
theorem underdetermined_at_level (k : Nat) (f : Level k → Level k → Bool) :
    ∃ g h : Level k → Bool,
      (∃ x, g x ≠ h x) ∧
      (∀ a, ∃ x, f a x ≠ g x) ∧
      (∀ a, ∃ x, f a x ≠ h x) :=
  Tower.underdetermined_at_two (pt₀ k) (pt₁ k) (pts_ne k) f

/-! ## Summary -/

/-- Summary: naming steps, new namers, no settling, injective conservative
    lifts, strict increase, and underdetermination at each level. -/
theorem ladder_package :
    (∀ k, Tower.NamingExtension (rep k) (rep (k + 1)) some (dodgeEscape k)) ∧
    (∀ k, ∀ a : Level k, (some a : Level (k + 1)) ≠ none) ∧
    (∀ k, ¬ Diagonal.PointSurjective (rep k)) ∧
    (∀ k j, ∀ x y : Level k, lift k j x = lift k j y → x = y) ∧
    (∀ k j, ∀ x y : Level k,
      rep (k + j) (lift k j x) (lift k j y) = rep k x y) ∧
    (∀ k j, ∃ b : Level (k + (j + 1)), ∀ a : Level k,
      lift k (j + 1) a ≠ b) ∧
    (∀ k (f : Level k → Level k → Bool), ∃ g h : Level k → Bool,
      (∃ x, g x ≠ h x) ∧
      (∀ a, ∃ x, f a x ≠ g x) ∧
      (∀ a, ∃ x, f a x ≠ h x)) :=
  ⟨ladder_step, none_is_new, ladder_never_settles,
   lift_injective, lift_conservative, ladder_ascends,
   underdetermined_at_level⟩

#print axioms Ladder.ladder_step
#print axioms Ladder.ladder_grows
#print axioms Ladder.none_is_new
#print axioms Ladder.ladder_never_settles
#print axioms Ladder.lift_injective
#print axioms Ladder.lift_conservative
#print axioms Ladder.ladder_ascends
#print axioms Ladder.underdetermined_at_level
#print axioms Ladder.ladder_package

end Ladder
