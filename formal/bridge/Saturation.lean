import Obs.Budget
import Obs.StochasticUnlock
import Obs.CausalOrder
import Obs.Dimension
import Geom.Profile
import Alphabet

/-!
# T-15 Saturation / equation-of-state form

Ledger balance as the equation-of-state shape of the Jacobson audit:
aliveness is the record-demand / capacity inequality; saturation is
equality; at saturation the realized record flux is fixed by the
capacity schedule (unique step-growth solution).

No curvature claimed; field equations refused. Packages existing
`Geom.Profile.Alive`, `Obs.Budget` B1/B2, and
`Obs.Dimension.capacity_unique_step_growth` — no new mathematics.
-/

namespace Bridge.Saturation

open Obs.StochasticUnlock
open Obs.Budget (Saturated)

/-- Alive ⇔ records demand ≤ capacity growth (definition unpacking). -/
theorem alive_iff_records_le_caps
    (K : Nat) (prof : Geom.Profile.DepthProfile) (T : Nat) :
    Geom.Profile.Alive K prof T ↔
      K ^ T ≤ Geom.Profile.capacityOf K prof T :=
  Iff.rfl

/-- Saturation := equality of per-tick record flux with consumed alphabet. -/
theorem saturation_iff_tick_equality
    {X E S E' : Type} [DecidableEq E']
    (G : X × E → S × E')
    (hinj : ∀ a b : X × E, G a = G b → a = b)
    (e0 : E) (s : S) (xs : List X) (hd : Distinct xs)
    (hsys : ∀ x, x ∈ xs → (G (x, e0)).1 = s)
    (Es : List E') (hEs : Distinct Es)
    (halph : ∀ x, x ∈ xs → (G (x, e0)).2 ∈ Es) :
    xs.length = Es.length ↔ Saturated G e0 xs Es :=
  Obs.Budget.budget_tick_eq_iff G hinj e0 s xs hd hsys Es hEs halph

/-- At saturation, record flux equals the declared capacity length. -/
theorem saturated_flux_fixed_by_capacity
    {X E S E' : Type} [DecidableEq E']
    (G : X × E → S × E')
    (hinj : ∀ a b : X × E, G a = G b → a = b)
    (e0 : E) (s : S) (xs : List X) (hd : Distinct xs)
    (hsys : ∀ x, x ∈ xs → (G (x, e0)).1 = s)
    (Es : List E') (hEs : Distinct Es)
    (halph : ∀ x, x ∈ xs → (G (x, e0)).2 ∈ Es)
    (c : Nat) (hcap : Es.length = c)
    (hsat : Saturated G e0 xs Es) :
    xs.length = c := by
  rw [← hcap]
  exact (saturation_iff_tick_equality
    G hinj e0 s xs hd hsys Es hEs halph).mpr hsat

/-- Capacity schedule is the unique step-growth solution. -/
theorem capacity_schedule_unique {K tTurn : Nat} :
    Obs.Dimension.StepGrowth K tTurn
      (fun t => Obs.CausalOrder.capacityAt K tTurn t) ∧
    ∀ c, Obs.Dimension.StepGrowth K tTurn c →
      ∀ t, t ≤ tTurn →
        c t = Obs.CausalOrder.capacityAt K tTurn t :=
  Obs.Dimension.capacity_unique_step_growth

/-- **T-15.** Alive ⇔ records ≤ caps; saturation := equality; at
    saturation, record flux is determined by the capacity schedule. -/
theorem T15_saturation_equation_of_state :
    (∀ (K : Nat) (prof : Geom.Profile.DepthProfile) (T : Nat),
      Geom.Profile.Alive K prof T ↔
        K ^ T ≤ Geom.Profile.capacityOf K prof T) ∧
    (∀ {X E S E' : Type} [DecidableEq E']
        (G : X × E → S × E')
        (_hinj : ∀ a b : X × E, G a = G b → a = b)
        (e0 : E) (s : S) (xs : List X) (_hd : Distinct xs)
        (_hsys : ∀ x, x ∈ xs → (G (x, e0)).1 = s)
        (Es : List E') (_hEs : Distinct Es)
        (_halph : ∀ x, x ∈ xs → (G (x, e0)).2 ∈ Es),
      xs.length = Es.length ↔ Saturated G e0 xs Es) ∧
    (∀ {K tTurn : Nat},
      Obs.Dimension.StepGrowth K tTurn
        (fun t => Obs.CausalOrder.capacityAt K tTurn t) ∧
      ∀ c, Obs.Dimension.StepGrowth K tTurn c →
        ∀ t, t ≤ tTurn →
          c t = Obs.CausalOrder.capacityAt K tTurn t) ∧
    Bridge.Alphabet.Kmin = 2 :=
  ⟨alive_iff_records_le_caps,
   saturation_iff_tick_equality,
   fun {_ _} => capacity_schedule_unique,
   Bridge.Alphabet.Kmin_eq⟩

#print axioms alive_iff_records_le_caps
#print axioms saturation_iff_tick_equality
#print axioms saturated_flux_fixed_by_capacity
#print axioms capacity_schedule_unique
#print axioms T15_saturation_equation_of_state

end Bridge.Saturation
