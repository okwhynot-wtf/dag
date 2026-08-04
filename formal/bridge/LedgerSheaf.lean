import EinsteinSkeleton
import EffectiveMatter
import Alphabet

/-!
# O-3 fragment — stalk glue for local ledger patches

Jacobson needs independent local balance laws. T-16 supplies stalks
(`LocalLedgerPatch`). This module begins the sheaf programme:

- covers with pairwise `OverlapCompatible` patches
- glue: same locus ⇒ equal capacity length
- effective matter (fiber length) agrees whenever both patches are
  length-saturated against a shared capacity

Not a full sheaf (no restriction maps, no gluable sections of dynamics).
Continuum locality refused; this is combinatorial stalk agreement.
-/

namespace Bridge.LedgerSheaf

open Bridge.EinsteinSkeleton
open Bridge.EffectiveMatter

/-- A cover by local ledger patches. -/
structure LedgerCover (X E S E' : Type) where
  patches : List (LocalLedgerPatch X E S E')

/-- Every pair of patches is overlap-compatible. -/
def CoverCompatible {X E S E' : Type}
    (c : LedgerCover X E S E') : Prop :=
  ∀ p ∈ c.patches, ∀ q ∈ c.patches, OverlapCompatible p q

theorem cover_compatible_refl {X E S E' : Type}
    (p : LocalLedgerPatch X E S E') :
    CoverCompatible ⟨[p]⟩ := by
  intro q hq r hr
  have hq' : q = p := by
    cases hq with
    | head => rfl
    | tail _ h => cases h
  have hr' : r = p := by
    cases hr with
    | head => rfl
    | tail _ h => cases h
  rw [hq', hr']
  exact overlap_refl p

/-- **Glue on a locus.** Overlap compatibility + equal locus ⇒ equal
    capacity length (stalk agreement for the capacity schedule). -/
theorem glue_capacity_on_locus
    {X E S E' : Type}
    {p q : LocalLedgerPatch X E S E'}
    (h : OverlapCompatible p q)
    (hlocus : p.locus = q.locus) :
    p.alphabet.length = q.alphabet.length :=
  h hlocus

/-- Cover-level glue: any two patches at the same locus agree on capacity. -/
theorem cover_glue_capacity
    {X E S E' : Type}
    {c : LedgerCover X E S E'}
    (hcov : CoverCompatible c)
    {p q : LocalLedgerPatch X E S E'}
    (hp : p ∈ c.patches) (hq : q ∈ c.patches)
    (hlocus : p.locus = q.locus) :
    p.alphabet.length = q.alphabet.length :=
  glue_capacity_on_locus (hcov p hp q hq) hlocus

/-- If two patches share a locus and both realize fiber length = capacity
    length, their effective matter readings agree. -/
theorem glue_effectiveMatter_at_saturation_length
    {X E S E' : Type}
    {p q : LocalLedgerPatch X E S E'}
    (h : OverlapCompatible p q)
    (hlocus : p.locus = q.locus)
    (hp : p.fiber.length = p.alphabet.length)
    (hq : q.fiber.length = q.alphabet.length) :
    effectiveMatter p = effectiveMatter q := by
  have hcap := glue_capacity_on_locus h hlocus
  simp only [effectiveMatter, stressProxy]
  rw [hp, hq, hcap]

/-- Two-patch cover at one locus with matching alphabets is compatible. -/
theorem two_patch_cover_compatible
    {X E S E' : Type}
    (p q : LocalLedgerPatch X E S E')
    (_hlocus : p.locus = q.locus)
    (hcap : p.alphabet.length = q.alphabet.length) :
    CoverCompatible ⟨[p, q]⟩ := by
  intro a ha b hb hloc
  have mem_pq : ∀ x, x ∈ ([p, q] : List _) → x = p ∨ x = q := by
    intro x hx
    cases hx with
    | head => exact Or.inl rfl
    | tail _ hx' =>
      cases hx' with
      | head => exact Or.inr rfl
      | tail _ hx'' => cases hx''
  match mem_pq a ha, mem_pq b hb with
  | Or.inl hap, Or.inl hbq =>
    subst hap; subst hbq; rfl
  | Or.inl hap, Or.inr hbq =>
    subst hap; subst hbq; exact hcap
  | Or.inr hap, Or.inl hbq =>
    subst hap; subst hbq; exact hcap.symm
  | Or.inr hap, Or.inr hbq =>
    subst hap; subst hbq; rfl

/-! ## Restriction maps (sheaf programme, next rung) -/

/-- Restrict a patch to a new locus tag, keeping the ledger data.
    Combinatorial stand-in for restriction along a branch inclusion. -/
def restrictTo {X E S E' : Type}
    (p : LocalLedgerPatch X E S E') (locus' : Nat) :
    LocalLedgerPatch X E S E' where
  locus := locus'
  G := p.G
  e0 := p.e0
  s := p.s
  fiber := p.fiber
  alphabet := p.alphabet

theorem restrict_preserves_capacity {X E S E' : Type}
    (p : LocalLedgerPatch X E S E') (locus' : Nat) :
    (restrictTo p locus').alphabet.length = p.alphabet.length :=
  rfl

theorem restrict_preserves_fiber {X E S E' : Type}
    (p : LocalLedgerPatch X E S E') (locus' : Nat) :
    (restrictTo p locus').fiber.length = p.fiber.length :=
  rfl

theorem restrict_preserves_effectiveMatter {X E S E' : Type}
    (p : LocalLedgerPatch X E S E') (locus' : Nat) :
    effectiveMatter (restrictTo p locus') = effectiveMatter p :=
  rfl

/-- Restriction is idempotent on ledger data: re-tagging twice = once. -/
theorem restrict_idempotent_data {X E S E' : Type}
    (p : LocalLedgerPatch X E S E') (ℓ₁ ℓ₂ : Nat) :
    (restrictTo (restrictTo p ℓ₁) ℓ₂).alphabet = p.alphabet ∧
    (restrictTo (restrictTo p ℓ₁) ℓ₂).fiber = p.fiber :=
  ⟨rfl, rfl⟩

/-- Overlap after re-tag: if capacities already agree, matching locus tags glue. -/
theorem restrict_overlap_of_cap {X E S E' : Type}
    (p q : LocalLedgerPatch X E S E')
    (hcap : p.alphabet.length = q.alphabet.length) (ℓ : Nat) :
    OverlapCompatible (restrictTo p ℓ) (restrictTo q ℓ) := by
  intro _
  exact hcap

/-- Local balance (fiber length = alphabet length) is stable under restrict. -/
theorem restrict_preserves_balance {X E S E' : Type}
    (p : LocalLedgerPatch X E S E') (locus' : Nat)
    (hbal : p.fiber.length = p.alphabet.length) :
    (restrictTo p locus').fiber.length =
      (restrictTo p locus').alphabet.length := by
  simpa [restrict_preserves_fiber, restrict_preserves_capacity] using hbal

/-- **O-3 fragment package.** Stalk glue for capacity (and effective matter
    at equal saturated lengths); restriction preserves capacity / matter /
    balance. Full sheaf of dynamics remains open. -/
theorem o3_stalk_glue_fragment :
    (∀ {X E S E' : Type} {p q : LocalLedgerPatch X E S E'},
      OverlapCompatible p q → p.locus = q.locus →
        p.alphabet.length = q.alphabet.length) ∧
    (∀ {X E S E' : Type} {p q : LocalLedgerPatch X E S E'},
      OverlapCompatible p q → p.locus = q.locus →
      p.fiber.length = p.alphabet.length →
      q.fiber.length = q.alphabet.length →
        effectiveMatter p = effectiveMatter q) ∧
    Bridge.Alphabet.Kmin = 2 :=
  ⟨glue_capacity_on_locus,
   glue_effectiveMatter_at_saturation_length,
   Bridge.Alphabet.Kmin_eq⟩

/-- **O-3 restriction fragment.** Restriction maps preserve capacity,
    effective matter, and saturation balance; overlap after re-tag when
    capacities agree. -/
theorem o3_restriction_fragment :
    (∀ {X E S E' : Type} (p : LocalLedgerPatch X E S E') ℓ,
      (restrictTo p ℓ).alphabet.length = p.alphabet.length) ∧
    (∀ {X E S E' : Type} (p : LocalLedgerPatch X E S E') ℓ,
      effectiveMatter (restrictTo p ℓ) = effectiveMatter p) ∧
    (∀ {X E S E' : Type} (p q : LocalLedgerPatch X E S E')
      (hcap : p.alphabet.length = q.alphabet.length) ℓ,
      OverlapCompatible (restrictTo p ℓ) (restrictTo q ℓ)) ∧
    Bridge.Alphabet.Kmin = 2 :=
  ⟨fun p ℓ => restrict_preserves_capacity p ℓ,
   fun p ℓ => restrict_preserves_effectiveMatter p ℓ,
   fun p q hcap ℓ => restrict_overlap_of_cap p q hcap ℓ,
   Bridge.Alphabet.Kmin_eq⟩

#print axioms glue_capacity_on_locus
#print axioms cover_glue_capacity
#print axioms glue_effectiveMatter_at_saturation_length
#print axioms two_patch_cover_compatible
#print axioms o3_stalk_glue_fragment
#print axioms o3_restriction_fragment
#print axioms restrict_preserves_balance

end Bridge.LedgerSheaf
