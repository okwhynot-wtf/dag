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

/-- **O-3 fragment package.** Stalk glue for capacity (and effective matter
    at equal saturated lengths). Full sheaf of dynamics remains open. -/
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

#print axioms glue_capacity_on_locus
#print axioms cover_glue_capacity
#print axioms glue_effectiveMatter_at_saturation_length
#print axioms two_patch_cover_compatible
#print axioms o3_stalk_glue_fragment

end Bridge.LedgerSheaf
