import TwoBounce
import PeriodSpectrum

/-!
# Overtones (EXPERIMENTAL: quarantined; exports nothing to the paper)

The core of this probe has been promoted to `Bridge.PeriodSpectrum`:
the general dihedral factorisation (`rot_eq_two_flips`, the arithmetic
mirrors `reflZero` and `reflAt`, and the packaged computable
`rotFactor`) and the generation theorem `overtone_generation` (every
injective endomap on a finite carrier is a composite of two
involutions). This module re-exports those names under
`Experimental.Overtones` so downstream experiments keep compiling, and
it retains the quarantined remainder: the concrete `Fin 3` and `Fin 5`
exhibits with their original `decide` proofs, their re-derivations as
instances of the promoted general theorem, and the closed-form factors
for the concrete cycles.

The probe's question stands as before: the fundamental has period two,
and higher periods arise from it by composition of exactly two flips.
The musical names are decoration and carry no claim. Nothing here
asserts a continuum and nothing here is imported by any paper-cited
module.
-/
namespace Experimental.Overtones

open Bridge.TwoBounce

export Bridge.PeriodSpectrum (rot reflZero reflAt reflZero_involution
  reflAt_involution rot_eq_two_flips rotFactor overtone_generation)

/-! ## Period three, concretely -/

/-- Rotation by one on `Fin 3`: the period-three overtone. -/
def cyc3 : Fin 3 → Fin 3 := fun i => i + 1

/-- Mirror through 0. -/
def refl3 : Fin 3 → Fin 3 := fun i => 0 - i

/-- Mirror through one half. -/
def refl3' : Fin 3 → Fin 3 := fun i => 1 - i

theorem refl3_involution : IsInvolution refl3 := by
  unfold IsInvolution; decide

theorem refl3'_involution : IsInvolution refl3' := by
  unfold IsInvolution; decide

/-- The period-three overtone is exactly two flips. -/
theorem three_from_two_flips : ∀ i, cyc3 i = refl3' (refl3 i) := by
  decide

/-- `cyc3` genuinely has period three: the cube is the identity and no
    smaller positive power rests anywhere. -/
theorem cyc3_period_three :
    (∀ i, cyc3 (cyc3 (cyc3 i)) = i) ∧
    (∀ i, cyc3 i ≠ i) ∧
    (∀ i, cyc3 (cyc3 i) ≠ i) := by
  decide

/-! ## Period five, concretely -/

/-- Rotation by one on `Fin 5`: a prime overtone above the fundamental. -/
def cyc5 : Fin 5 → Fin 5 := fun i => i + 1

def refl5 : Fin 5 → Fin 5 := fun i => 0 - i

def refl5' : Fin 5 → Fin 5 := fun i => 1 - i

theorem refl5_involution : IsInvolution refl5 := by
  unfold IsInvolution; decide

theorem refl5'_involution : IsInvolution refl5' := by
  unfold IsInvolution; decide

theorem five_from_two_flips : ∀ i, cyc5 i = refl5' (refl5 i) := by
  decide

theorem cyc5_period_five :
    (∀ i, cyc5 (cyc5 (cyc5 (cyc5 (cyc5 i)))) = i) ∧
    (∀ i, cyc5 i ≠ i) ∧
    (∀ i, cyc5 (cyc5 i) ≠ i) ∧
    (∀ i, cyc5 (cyc5 (cyc5 i)) ≠ i) ∧
    (∀ i, cyc5 (cyc5 (cyc5 (cyc5 i))) ≠ i) := by
  decide

theorem cyc3_injective : EndoInj cyc3 := by
  unfold EndoInj; decide

theorem cyc5_injective : EndoInj cyc5 := by
  unfold EndoInj; decide

/-- Existence form of the closed-form factorisation: the shape of
    `overtone_generation`, but with the pair given in closed form
    instead of by the orbit-traversal construction of
    `factor_fin`. -/
theorem rot_from_two_flips {n : Nat} (k : Fin n) :
    ∃ φ σ : Fin n → Fin n,
      IsInvolution φ ∧ IsInvolution σ ∧ ∀ x, rot k x = σ (φ x) :=
  ⟨reflZero, reflAt k, reflZero_involution, reflAt_involution k,
   rot_eq_two_flips k⟩

/-! ## Subsumption of the concrete exhibits

The `Fin 3` / `Fin 5` shapes re-derived as instances of the promoted
general theorem. The original `decide` proofs above are kept intact;
only the bridge `0 - i = -i` (a `Nat.zero_mod` computation) separates
the concrete mirrors from the general ones. -/

/-- Value of negation on `Fin n`: `(-i).val = (n - i.val) % n`
    (local copy of the promoted private lemma). -/
private theorem neg_val {n : Nat} (i : Fin n) :
    (-i).val = (n - i.val) % n := by
  rw [Fin.neg_def]

/-- On a nonempty carrier the literal-`0` mirror `0 - i` agrees with
    the negation mirror `reflZero`. -/
private theorem zero_sub_eq_neg {m : Nat} (i : Fin (m + 1)) :
    (0 : Fin (m + 1)) - i = -i := by
  apply Fin.ext
  rw [Fin.val_sub, neg_val]
  show (m + 1 - i.val + 0) % (m + 1) = (m + 1 - i.val) % (m + 1)
  rw [Nat.add_zero]

/-- `three_from_two_flips`, re-derived from `rot_eq_two_flips` at
    `n = 3`, `k = 1` (subsumption of the concrete exhibit). -/
theorem three_from_two_flips_general :
    ∀ i, cyc3 i = refl3' (refl3 i) := by
  intro i
  have hz : refl3 i = reflZero i := zero_sub_eq_neg i
  rw [hz]
  exact rot_eq_two_flips (1 : Fin 3) i

/-- `five_from_two_flips`, re-derived from `rot_eq_two_flips` at
    `n = 5`, `k = 1` (subsumption of the concrete exhibit). -/
theorem five_from_two_flips_general :
    ∀ i, cyc5 i = refl5' (refl5 i) := by
  intro i
  have hz : refl5 i = reflZero i := zero_sub_eq_neg i
  rw [hz]
  exact rot_eq_two_flips (1 : Fin 5) i

/-- Closed-form factor for the period-three overtone: `rotFactor` at
    `k = 1` on `Fin 3` (`cyc3` is definitionally `rot 1`). -/
def cyc3Factor : TwoBounceFactor cyc3 := rotFactor (1 : Fin 3)

/-- Closed-form factor for the period-five overtone: `rotFactor` at
    `k = 1` on `Fin 5` (`cyc5` is definitionally `rot 1`). -/
def cyc5Factor : TwoBounceFactor cyc5 := rotFactor (1 : Fin 5)

#print axioms Experimental.Overtones.refl3_involution
#print axioms Experimental.Overtones.refl3'_involution
#print axioms Experimental.Overtones.three_from_two_flips
#print axioms Experimental.Overtones.cyc3_period_three
#print axioms Experimental.Overtones.refl5_involution
#print axioms Experimental.Overtones.refl5'_involution
#print axioms Experimental.Overtones.five_from_two_flips
#print axioms Experimental.Overtones.cyc5_period_five
#print axioms Experimental.Overtones.cyc3_injective
#print axioms Experimental.Overtones.cyc5_injective
#print axioms Experimental.Overtones.rot_from_two_flips
#print axioms Experimental.Overtones.neg_val
#print axioms Experimental.Overtones.zero_sub_eq_neg
#print axioms Experimental.Overtones.three_from_two_flips_general
#print axioms Experimental.Overtones.five_from_two_flips_general
#print axioms Experimental.Overtones.cyc3Factor
#print axioms Experimental.Overtones.cyc5Factor

end Experimental.Overtones
