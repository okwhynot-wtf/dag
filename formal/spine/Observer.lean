import Monism

/-!
# Observer — forced self-representation on the ladder

Minimal formal notion of observer: a carrier with a self-reading
`Carrier → Carrier → Bool`. From ladder construction alone, each level
self-represents, holds portraits of prior states, and satisfies seal,
interior, and outrun properties.

* **Level observer** (`levelObserver`): `Ladder.Level k` with `rep k`.
* **Portrait** (`namer_represents_the_past`): the new `none` element's
  reading over prior vocabulary is determined by prior state.
* **Seal** (`observer_sealed`): `rep k` is not point-surjective.
* **Interior** (`observer_interior`): the dodge is not articulated.
* **Outrun** (`observer_outrun`): no prior element matches the new
  element's portrait on the old vocabulary.
* **Signature** (`observer_signature`): tracked ascription flips under
  the act when hypotheses hold.

These results characterize self-representing carriers. A `RichObserver`
carries additional stored structure; the package applies to its
self-reading (`rich_inherits`), while the existence of rich observers is
not derived here.
-/
namespace Observer

/-- Minimal observer: carrier with a binary self-reading. -/
structure SelfRepresenter where
  Carrier : Type
  read : Carrier → Carrier → Bool

/-- Every ladder level is an observer. -/
def levelObserver (k : Nat) : SelfRepresenter :=
  ⟨Ladder.Level k, Ladder.rep k⟩

/-- The new `none` element's reading over level `k` is `¬` of the
    diagonal reading at `a` (definitional). -/
theorem namer_represents_the_past (k : Nat) :
    ∀ a : Ladder.Level k,
      Ladder.rep (k + 1) none (some a) = !(Ladder.rep k a a) :=
  fun _ => rfl

/-- `Ladder.rep k` is not point-surjective. -/
theorem observer_sealed (k : Nat) :
    ¬ Diagonal.PointSurjective (Ladder.rep k) :=
  Ladder.ladder_never_settles k

/-- The dodge for `rep k` is not articulated by `rep k`. -/
theorem observer_interior (k : Nat) :
    ¬ Interior.Articulates (Ladder.rep k)
      (Diagonal.dodgeWith not (Ladder.rep k)) :=
  Interior.self_opacity not TwoCycle.bool_fundamental.1 (Ladder.rep k)

/-- Some portrait at level `k + 1` is not realized on the old
    vocabulary by any element at level `k`. -/
theorem observer_outrun (k : Nat) :
    ∃ b, ∀ a, ∃ x,
      Ladder.rep (k + 1) (some a) (some x) ≠
        Ladder.rep (k + 1) b (some x) :=
  Interior.outdated_portrait (Ladder.ladder_step k)

/-- Tracked ascription flips under `act` when `TDiff`, `Alive`, and
    `Tracks` hold (re-export of
    `Interior.self_modeling_forces_restless`). -/
theorem observer_signature {α : Type} (S E : α → Bool) (act : α → α)
    (z₀ : α) (hT : TwoCycle.TDiff S act) (hA : TwoCycle.Alive S act z₀)
    (htr : Interior.Tracks E S) : ∀ c, E (act c) = !(E c) :=
  Interior.self_modeling_forces_restless S E act z₀ hT hA htr

structure RichObserver extends SelfRepresenter where
  store : Carrier → Carrier → Bool

theorem rich_inherits (R : RichObserver) :
    (¬ Diagonal.PointSurjective R.read) ∧
    (¬ Interior.Articulates R.read (Diagonal.dodgeWith not R.read)) :=
  ⟨Diagonal.seal_bool R.read,
   Interior.self_opacity not TwoCycle.bool_fundamental.1 R.read⟩

def levelRichObserver (k : Nat)
    (store : Ladder.Level k → Ladder.Level k → Bool) : RichObserver :=
  ⟨levelObserver k, store⟩

theorem rich_inherits_at_level (k : Nat)
    (store : Ladder.Level k → Ladder.Level k → Bool) :
    (¬ Diagonal.PointSurjective (levelRichObserver k store).read) ∧
    (¬ Interior.Articulates (levelRichObserver k store).read
      (Diagonal.dodgeWith not (levelRichObserver k store).read)) ∧
    (∃ b, ∀ a, ∃ x,
      Ladder.rep (k + 1) (some a) (some x) ≠
        Ladder.rep (k + 1) b (some x)) :=
  ⟨(rich_inherits (levelRichObserver k store)).1,
   (rich_inherits (levelRichObserver k store)).2,
   observer_outrun k⟩

/-! ## Summary -/

/-- At each level: portrait law, seal, interior, outrun, and the restless
    signature over the level's Bool coordinates. -/
theorem observers_forced (k : Nat) :
    (∀ a : Ladder.Level k,
      Ladder.rep (k + 1) none (some a) = !(Ladder.rep k a a)) ∧
    (¬ Diagonal.PointSurjective (Ladder.rep k)) ∧
    (¬ Interior.Articulates (Ladder.rep k)
      (Diagonal.dodgeWith not (Ladder.rep k))) ∧
    (∃ b, ∀ a, ∃ x,
      Ladder.rep (k + 1) (some a) (some x) ≠
        Ladder.rep (k + 1) b (some x)) ∧
    (∀ S E : Bool → Bool, TwoCycle.TDiff S not → TwoCycle.Alive S not true →
      Interior.Tracks E S → ∀ c, E (not c) = !(E c)) :=
  ⟨namer_represents_the_past k, observer_sealed k,
   observer_interior k, observer_outrun k,
   fun S E hT hA htr => observer_signature S E not true hT hA htr⟩

#print axioms Observer.namer_represents_the_past
#print axioms Observer.observer_sealed
#print axioms Observer.observer_interior
#print axioms Observer.observer_outrun
#print axioms Observer.observer_signature
#print axioms Observer.rich_inherits
#print axioms Observer.rich_inherits_at_level
#print axioms Observer.observers_forced

end Observer
