import Orbit
import Geom.Registration

/-!
# TwoBounce — I-1 losslessness as two arena bounces

Classical fact (finite carriers): a self-map is bijective iff it factors as
a composition of two involutions. Spine acts are involutions
(`SymmetricStep`); ledger joint steps `U` are forward-composing.

Landed here:
* involution ⇒ lossless ⇒ ¬Erasing (spine packaging)
* two-bounce ⇒ `Lossless` / product-`Inj` (converse half)
* existence when `U` is already an involution (`U = U ∘ id`)
* existence on `Bool` (every injection is an involution)
* existence for ledger `swapStep`

Open (tractable):
* full cycle-decomposition existence for arbitrary injections on `Fin n`
  (standard construction: on each cycle, φ = reflect, σ = rotate ∘ reflect)
* gauge-covariant / natural choice of `(φ, σ)` per step (canonicity)
* channel identification of the two factors with dictionary `φ`, `σ`

No Mathlib; no `sorry`; no declared axioms.
-/
namespace Bridge.TwoBounce

open Orbit

/-! ## Involutions -/

/-- An involution: `f ∘ f = id`. Spine `SymmetricStep` is this shape. -/
def IsInvolution {α : Type} (f : α → α) : Prop :=
  ∀ x, f (f x) = x

theorem involution_of_symmetric {α : Type} (act : α → α)
    (hs : SymmetricStep act) : IsInvolution act :=
  (symmetricStep_iff_involutive act).mp hs

theorem symmetric_of_involution {α : Type} (act : α → α)
    (h : IsInvolution act) : SymmetricStep act :=
  (symmetricStep_iff_involutive act).mpr h

/-- Involutions are injective (= lossless). -/
theorem involution_injective {α : Type} (f : α → α) (h : IsInvolution f) :
    Lossless f := by
  intro x y heq
  have := congrArg f heq
  rw [h x, h y] at this
  exact this

/-- Involutive acts cannot erase. -/
theorem involution_not_erasing {α : Type} (f : α → α) (h : IsInvolution f) :
    ¬ Erasing f := by
  intro ⟨x, y, hne, heq⟩
  exact hne (involution_injective f h x y heq)

/-- Spine packaging: `SymmetricStep` excludes `Erasing`. -/
theorem symmetric_excludes_erase {α : Type} (act : α → α)
    (hs : SymmetricStep act) : ¬ Erasing act :=
  involution_not_erasing act (involution_of_symmetric act hs)

/-! ## Two-bounce factorisation -/

/-- Witness that `U` factors as `σ ∘ φ` with both factors involutions. -/
structure TwoBounceFactor {α : Type} (U : α → α) where
  /-- First bounce. -/
  φ : α → α
  /-- Second bounce. -/
  σ : α → α
  φ_inv : IsInvolution φ
  σ_inv : IsInvolution σ
  factor : ∀ x, U x = σ (φ x)

/-- Converse: two-bounce form ⇒ lossless. -/
theorem lossless_of_two_bounce {α : Type} (U : α → α)
    (f : TwoBounceFactor U) : Lossless U := by
  intro a b h
  have hσ : f.σ (f.φ a) = f.σ (f.φ b) := by
    rw [← f.factor a, ← f.factor b, h]
  have hφ : f.φ a = f.φ b := involution_injective f.σ f.σ_inv _ _ hσ
  exact involution_injective f.φ f.φ_inv _ _ hφ

/-- On a product carrier, two-bounce ⇒ ledger `Inj`. -/
theorem inj_of_two_bounce {S E : Type} (U : S × E → S × E)
    (f : TwoBounceFactor U) : Geom.Registration.Inj U :=
  lossless_of_two_bounce U f

/-- Any involution is already a two-bounce (`U = U ∘ id`). -/
def factor_involution {α : Type} (U : α → α) (h : IsInvolution U) :
    TwoBounceFactor U where
  φ := id
  σ := U
  φ_inv := fun _ => rfl
  σ_inv := h
  factor := fun _ => rfl

/-! ## `Bool` and ledger toys -/

/-- Endomap injectivity (carrier-agnostic). -/
def EndoInj {α : Type} (U : α → α) : Prop :=
  ∀ a b, U a = U b → a = b

theorem bool_inj_involution (U : Bool → Bool) (h : EndoInj U) :
    IsInvolution U := by
  intro x
  cases hf : U false with
  | false =>
    cases ht : U true with
    | false =>
      have : false = true := h false true (hf.trans ht.symm)
      cases this
    | true => cases x <;> simp [hf, ht]
  | true =>
    cases ht : U true with
    | false => cases x <;> simp [hf, ht]
    | true =>
      have : false = true := h false true (hf.trans ht.symm)
      cases this

def factor_bool (U : Bool → Bool) (h : EndoInj U) :
    TwoBounceFactor U :=
  factor_involution U (bool_inj_involution U h)

theorem swapStep_involution :
    IsInvolution Geom.Registration.swapStep := by
  intro p; cases p; rfl

def factor_swapStep : TwoBounceFactor Geom.Registration.swapStep :=
  factor_involution _ swapStep_involution

/-! ## I-1 packaging -/

/-- General `Fin n` existence (arbitrary injection) — open; cycle-wise
    reflect / rotate∘reflect is the intended construction. -/
def fin_general_existence_open : True := trivial

/-- Canonicity of `(φ, σ)` open. Channel rhyme suggestive only. -/
def canonicity_open : True := trivial

/-- **I-1 two-bounce fragment.** Converse + spine ¬erase + existence on
    involutions / Bool / swapStep. General `Fin n` existence and
    canonicity flagged open (`fin_general_existence_open`,
    `canonicity_open`). -/
theorem i1_two_bounce_fragment :
    (∀ {α : Type} (U : α → α) (f : TwoBounceFactor U), Lossless U) ∧
    (∀ {S E : Type} (U : S × E → S × E) (f : TwoBounceFactor U),
      Geom.Registration.Inj U) ∧
    (∀ {α : Type} (U : α → α), IsInvolution U →
      Nonempty (TwoBounceFactor U)) ∧
    (∀ U : Bool → Bool, EndoInj U → Nonempty (TwoBounceFactor U)) ∧
    Nonempty (TwoBounceFactor Geom.Registration.swapStep) ∧
    (∀ {α : Type} (act : α → α), SymmetricStep act → ¬ Erasing act) :=
  ⟨fun _U f => lossless_of_two_bounce _ f,
   fun _U f => inj_of_two_bounce _ f,
   fun _U h => ⟨factor_involution _ h⟩,
   fun U h => ⟨factor_bool U h⟩,
   ⟨factor_swapStep⟩,
   fun act hs => symmetric_excludes_erase act hs⟩

#print axioms Bridge.TwoBounce.symmetric_excludes_erase
#print axioms Bridge.TwoBounce.lossless_of_two_bounce
#print axioms Bridge.TwoBounce.inj_of_two_bounce
#print axioms Bridge.TwoBounce.factor_bool
#print axioms Bridge.TwoBounce.i1_two_bounce_fragment

end Bridge.TwoBounce
