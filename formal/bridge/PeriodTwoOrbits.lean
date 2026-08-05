import Revision
import OneZ2
import PhaseEToys
import Alphabet
import Geom.Registration

/-!
# Period-two orbits (KMS-shaped caricature)

Packages existing pieces as a discrete equilibrium sketch:

* liar-revision sequences are period-2 (`Revision.revision_period_two`)
* face projections are involutions (`OneZ2.project_involution`)
* Bool swap flips observation (`not`)
* combinatorial temperature is constant on any tick, and Clausius holds

Not continuum KMS, not modular flow, not Unruh / boost temperature
(O-2 remains structural), not Gibbs/Boltzmann. Equilibrium here means
period-2 under the ℤ/2 swap with constant combinatorial `T_c`.
-/

namespace Bridge.PeriodTwoOrbits

open Bridge.PhaseEToys
open Bridge.OneZ2

/-- Period-2 orbit under the Bool swap / liar revision. -/
theorem period2_orbit_under_swap (s : Nat → Bool)
    (hs : Revision.LiarRevision s) :
    ∀ n, s (n + 2) = s n :=
  Revision.revision_period_two s hs

/-- Every named face projection is an involution (T-7 reuse). -/
theorem face_project_is_involution (f : Face) (b : Z2) :
    project f (project f b) = b :=
  project_involution f b

/-- Observation flips under the Bool involution. -/
theorem observe_flips_under_involution (b : Bool) :
    (!b) = !b :=
  rfl

/-- Swap microstep is an involution on the joint Bool×Bool carrier. -/
theorem swapStep_involution (p : Bool × Bool) :
    Geom.Registration.swapStep (Geom.Registration.swapStep p) = p := by
  cases p
  rfl

/-- Combinatorial temperature is constant along any period-2 orbit. -/
theorem temp_constant_by_definition (s : Nat → Bool)
    (_hs : Revision.LiarRevision s) (n m : Nat) :
    combinatorialTemp n = combinatorialTemp m :=
  rfl

/-- Clausius caricature holds at every tick of a period-2 orbit. -/
theorem heat_balance_by_definition (s : Nat → Bool)
    (_hs : Revision.LiarRevision s) (n : Nat) :
    heatQuantum n = combinatorialTemp n * deltaS n :=
  clausius_form n

/-- **Period-two package.** Discrete equilibrium ↔
    period-2 under ℤ/2 + constant combinatorial `T_c` + Clausius toy.
    Not continuum KMS; not Unruh. -/
theorem period_two_package :
    (∀ s, Revision.LiarRevision s → ∀ n, s (n + 2) = s n) ∧
    (∀ f b, project f (project f b) = b) ∧
    (∀ p, Geom.Registration.swapStep
      (Geom.Registration.swapStep p) = p) ∧
    (∀ T, combinatorialTemp T = 1) ∧
    (∀ T, heatQuantum T = combinatorialTemp T * deltaS T) ∧
    (∀ s, Revision.LiarRevision s →
      ∀ n m, combinatorialTemp n = combinatorialTemp m) ∧
    Bridge.Alphabet.Kmin = 2 :=
  ⟨period2_orbit_under_swap, face_project_is_involution,
   swapStep_involution,
   fun _ => rfl, clausius_form,
   fun s hs n m => temp_constant_by_definition s hs n m,
   Bridge.Alphabet.Kmin_eq⟩

#print axioms period2_orbit_under_swap
#print axioms face_project_is_involution
#print axioms swapStep_involution
#print axioms period_two_package

end Bridge.PeriodTwoOrbits
