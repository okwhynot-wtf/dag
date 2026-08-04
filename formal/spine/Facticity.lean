import Orbit
import TwoCycle

/-!
# Facticity — orbit liveness as non-degeneracy

Under the ambient equation `a ∘ a = id`, the orbit of a seed `z` is either
the singleton `{z}` or the pair `{z, a(z)}`. In the second case liveness
holds automatically at every point of the orbit. Consequently, for pointed
symmetric acts, liveness on the orbit is equivalent to non-degeneracy of
the orbit (`a(z) ≠ z`).

This converts quantified liveness into a theorem conditional on one bit of
facticity — the existence of a non-degenerate pointed act. That existential
is the audited residue; discharging it as a world-derivation from `Bool`
alone is refused (see paper Section 12 / status inventory).
-/
namespace Facticity

open Orbit

variable {α : Type}

/-- The seed's orbit is non-degenerate: the act moves the seed. -/
def NonDegenerate (act : α → α) (z : α) : Prop :=
  act z ≠ z

/-- Membership in the forward orbit of `z`. -/
def OnOrbit (act : α → α) (z x : α) : Prop :=
  ∃ n : Nat, iter act n z = x

/-- Liveness restricted to the orbit of the seed. -/
def LiveOnOrbit (act : α → α) (z : α) : Prop :=
  ∀ x, OnOrbit act z x → act x ≠ x

/-- Under a symmetric step, every orbit point is the seed or its image. -/
theorem orbit_of_symmetric (act : α → α) (hs : SymmetricStep act) (z : α) :
    ∀ x, OnOrbit act z x → x = z ∨ x = act z := by
  intro x ⟨n, hn⟩
  have hinv := (symmetricStep_iff_involutive act).mp hs
  have htwo := two_cycle_at act (hinv z) n
  cases htwo with
  | inl h => exact Or.inl (hn.symm.trans h)
  | inr h => exact Or.inr (hn.symm.trans h)

/-- Non-degeneracy forces a genuine two-point orbit under symmetry. -/
theorem nondegenerate_two_cycle (act : α → α) (hs : SymmetricStep act)
    (z : α) (hne : NonDegenerate act z) :
    act (act z) = z ∧ act z ≠ z ∧
      (∀ n, iter act n z = z ∨ iter act n z = act z) := by
  have hinv := (symmetricStep_iff_involutive act).mp hs
  exact ⟨hinv z, hne, two_cycle_at act (hinv z)⟩

/-- On a non-degenerate symmetric orbit, both points are live. -/
theorem nondegenerate_live_on_orbit (act : α → α) (hs : SymmetricStep act)
    (z : α) (hne : NonDegenerate act z) : LiveOnOrbit act z := by
  intro x hx
  have hinv := (symmetricStep_iff_involutive act).mp hs
  cases orbit_of_symmetric act hs z x hx with
  | inl hxz =>
    subst hxz
    exact hne
  | inr hxa =>
    subst hxa
    intro hfix
    exact hne (hfix.symm.trans (hinv z))

/-- Degeneracy refutes orbit liveness. -/
theorem degenerate_not_live_on_orbit (act : α → α) (z : α)
    (hdeg : ¬ NonDegenerate act z) : ¬ LiveOnOrbit act z := by
  intro hl
  have hz : OnOrbit act z z := ⟨0, rfl⟩
  have : act z ≠ z := hl z hz
  exact hdeg this

/-- **Orbit facticity.** For pointed symmetric acts, liveness on the orbit
    is equivalent to non-degeneracy of the seed. -/
theorem liveOnOrbit_iff_nondegenerate (act : α → α)
    (hs : SymmetricStep act) (z : α) :
    LiveOnOrbit act z ↔ NonDegenerate act z := by
  constructor
  · intro hl
    have hz : OnOrbit act z z := ⟨0, rfl⟩
    exact hl z hz
  · intro hne
    exact nondegenerate_live_on_orbit act hs z hne

/-- Global liveness implies orbit liveness at every seed. -/
theorem live_implies_liveOnOrbit (act : α → α) (hl : Live act) (z : α) :
    LiveOnOrbit act z :=
  fun _x _hx => hl _

/-- Under generation, orbit non-degeneracy upgrades to global liveness. -/
theorem nondegenerate_generated_live (act : α → α)
    (hs : SymmetricStep act) (hgen : TwoCycle.Generated act)
    (z : α) (hne : NonDegenerate act z) : Live act := by
  intro x hx
  have hinv := (symmetricStep_iff_involutive act).mp hs
  cases hgen z x with
  | inl heq =>
    subst heq
    exact hne hx
  | inr heq =>
    subst heq
    exact hne (hx.symm.trans (hinv z))

/-! ## Audited facticity interface

The irreducible residue is existence of one distinction. The Bool model
witnesses the mathematics; elevating that witness to a world-derivation
is refused. -/

/-- A pointed symmetric act with non-degenerate seed. -/
structure NondegeneratePointedAct where
  /-- Carrier. -/
  Carrier : Type
  /-- Act. -/
  act : Carrier → Carrier
  /-- Seed. -/
  seed : Carrier
  /-- Ambient equation. -/
  symmetric : SymmetricStep act
  /-- One bit of facticity. -/
  nondegenerate : NonDegenerate act seed

/-- Orbit liveness follows from the audited interface. -/
theorem NondegeneratePointedAct.liveOnOrbit (W : NondegeneratePointedAct) :
    LiveOnOrbit W.act W.seed :=
  (liveOnOrbit_iff_nondegenerate W.act W.symmetric W.seed).mpr W.nondegenerate

/-- Mathematical model: `(Bool, ¬, true)`. Not a world-derivation. -/
def boolModel : NondegeneratePointedAct where
  Carrier := Bool
  act := not
  seed := true
  symmetric := by
    intro x y h
    change y = !x at h
    subst h
    show x = !(!x)
    cases x <;> rfl
  nondegenerate := by intro h; cases h

/-- Constructive existence of a non-degenerate pointed act, as a model. -/
theorem exists_nondegenerate_pointed_act_model :
    Nonempty NondegeneratePointedAct :=
  ⟨boolModel⟩

/-- Refused: discharging facticity as derivation of the world from `Bool`
    alone. Marker only; the refusal is architectural (status inventory). -/
def world_from_Bool_discharge_refused : True := True.intro

/-- Package: orbit equivalence + model witness + discharge refusal. -/
theorem facticity_package (act : α → α) (hs : SymmetricStep act) (z : α) :
    (LiveOnOrbit act z ↔ NonDegenerate act z) ∧
    Nonempty NondegeneratePointedAct ∧
    world_from_Bool_discharge_refused = True.intro :=
  ⟨liveOnOrbit_iff_nondegenerate act hs z,
   exists_nondegenerate_pointed_act_model, rfl⟩

#print axioms Facticity.orbit_of_symmetric
#print axioms Facticity.nondegenerate_two_cycle
#print axioms Facticity.nondegenerate_live_on_orbit
#print axioms Facticity.degenerate_not_live_on_orbit
#print axioms Facticity.liveOnOrbit_iff_nondegenerate
#print axioms Facticity.live_implies_liveOnOrbit
#print axioms Facticity.nondegenerate_generated_live
#print axioms Facticity.NondegeneratePointedAct.liveOnOrbit
#print axioms Facticity.exists_nondegenerate_pointed_act_model
#print axioms Facticity.facticity_package

end Facticity
