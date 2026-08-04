import Alphabet
import Capacity
import EinsteinSkeleton
import Forman
import Saturation
import Geom.Registration
import Geom.Profile
import Obs.Budget
import Obs.StochasticUnlock

/-!
# Effective matter — sprint A1–A3, B4, C2

Hypothesis H: matter is an emergent effective description of record
flux that a bounded lossless ledger is forced to emit at capacity
saturation.

This module makes H *testable*:
- **A1** `effectiveMatter` = stress/flux proxy on a local patch
- **A2** vacuum dynamics = Inj ∧ ¬Merges ∧ ¬Registers (oscillator witness)
- **A3** matter-bearing tick = saturated with nonzero fiber
- **B4** below saturation there is capacity slack
- **C2** Kmin Forman unpaid flatness fits inside the expand/caps aliveness budget

No Standard Model, no continuum `T_{μν}`, no cosmological numbers.
-/

namespace Bridge.EffectiveMatter

open Obs.StochasticUnlock
open Obs.Budget (Saturated)
open Bridge.EinsteinSkeleton
open Bridge.Forman

/-! ## A1 — effective matter as flux -/

/-- **A1.** Effective matter reading: record flux (merge-fiber size) on a
    local ledger patch. At saturation this equals consumed capacity (T-16). -/
def effectiveMatter {X E S E' : Type}
    (p : LocalLedgerPatch X E S E') : Nat :=
  stressProxy p.fiber.length

theorem effectiveMatter_eq_fiber
    {X E S E' : Type} (p : LocalLedgerPatch X E S E') :
    effectiveMatter p = p.fiber.length :=
  rfl

/-- At saturation, effective matter equals capacity consumed. -/
theorem effectiveMatter_eq_capacity_at_saturation
    {X E S E' : Type} [DecidableEq E']
    (p : LocalLedgerPatch X E S E')
    (hinj : ∀ a b : X × E, p.G a = p.G b → a = b)
    (hd : Distinct p.fiber)
    (hsys : ∀ x, x ∈ p.fiber → (p.G (x, p.e0)).1 = p.s)
    (hEs : Distinct p.alphabet)
    (halph : ∀ x, x ∈ p.fiber → (p.G (x, p.e0)).2 ∈ p.alphabet)
    (hsat : Saturated p.G p.e0 p.fiber p.alphabet) :
    effectiveMatter p = capacityProxy p.alphabet.length :=
  stress_eq_capacity_at_saturation
    p.G hinj p.e0 p.s p.fiber hd hsys p.alphabet hEs halph hsat

/-! ## A2 — vacuum class -/

/-- **A2.** Vacuum dynamics: injective, never merges, never registers.
    The frictionless / H=0 / oscillator class. -/
def VacuumDynamics {S E : Type} (U : S × E → S × E) : Prop :=
  Geom.Registration.Inj U ∧
    ¬ Geom.Registration.Merges U ∧
    ¬ Geom.Registration.Registers U

theorem osc_is_vacuum :
    VacuumDynamics Geom.Registration.oscStep :=
  Geom.Registration.osc_never_registers

theorem vacuum_no_merges {S E : Type} {U : S × E → S × E}
    (h : VacuumDynamics U) : ¬ Geom.Registration.Merges U :=
  h.2.1

theorem vacuum_no_registers {S E : Type} {U : S × E → S × E}
    (h : VacuumDynamics U) : ¬ Geom.Registration.Registers U :=
  h.2.2

/-- Vacuum has no merge ⇒ no Landauer registration channel. -/
theorem vacuum_silent {S E : Type} {U : S × E → S × E}
    (h : VacuumDynamics U) :
    ¬ Geom.Registration.Merges U ∧ ¬ Geom.Registration.Registers U :=
  ⟨h.2.1, h.2.2⟩

/-! ## A3 — matter-bearing tick -/

/-- **A3.** Matter-bearing tick: saturated with nonzero fiber.
    Nonzero saturated flux = effective matter on that tick. -/
def MatterBearingTick {X E S E' : Type}
    (G : X × E → S × E') (e0 : E) (xs : List X) (Es : List E') : Prop :=
  Saturated G e0 xs Es ∧ 0 < xs.length

theorem matterBearing_has_flux
    {X E S E' : Type}
    {G : X × E → S × E'} {e0 : E} {xs : List X} {Es : List E'}
    (h : MatterBearingTick G e0 xs Es) :
    0 < stressProxy xs.length :=
  h.2

theorem matterBearing_eq_capacity
    {X E S E' : Type} [DecidableEq E']
    (G : X × E → S × E')
    (hinj : ∀ a b : X × E, G a = G b → a = b)
    (e0 : E) (s : S) (xs : List X) (hd : Distinct xs)
    (hsys : ∀ x, x ∈ xs → (G (x, e0)).1 = s)
    (Es : List E') (hEs : Distinct Es)
    (halph : ∀ x, x ∈ xs → (G (x, e0)).2 ∈ Es)
    (h : MatterBearingTick G e0 xs Es) :
    stressProxy xs.length = capacityProxy Es.length :=
  stress_eq_capacity_at_saturation
    G hinj e0 s xs hd hsys Es hEs halph h.1

/-- Swap dynamics admits merges/registers — the matter-channel witness
    opposite the vacuum oscillator (registration independence). -/
theorem swap_admits_matter_channel :
    Geom.Registration.Inj Geom.Registration.swapStep ∧
    Geom.Registration.Merges Geom.Registration.swapStep ∧
    Geom.Registration.Registers Geom.Registration.swapStep :=
  Geom.Registration.swap_registers

/-- A1–A3 separability: vacuum and matter-channel witnesses both exist. -/
theorem vacuum_vs_matter_channel_separable :
    VacuumDynamics Geom.Registration.oscStep ∧
    (Geom.Registration.Merges Geom.Registration.swapStep ∧
      Geom.Registration.Registers Geom.Registration.swapStep) :=
  ⟨osc_is_vacuum, ⟨Geom.Registration.swap_registers.2.1,
    Geom.Registration.swap_registers.2.2⟩⟩

/-! ## B4 — slack below saturation -/

/-- **B4.** Below saturation, fiber length is strictly below alphabet
    length: unused capacity slack. "Matter pressure" is optional until
    the bound. -/
theorem slack_below_saturation
    {X E S E' : Type} [DecidableEq E']
    (G : X × E → S × E')
    (hinj : ∀ a b : X × E, G a = G b → a = b)
    (e0 : E) (s : S) (xs : List X) (hd : Distinct xs)
    (hsys : ∀ x, x ∈ xs → (G (x, e0)).1 = s)
    (Es : List E') (hEs : Distinct Es)
    (halph : ∀ x, x ∈ xs → (G (x, e0)).2 ∈ Es)
    (hnsat : ¬ Saturated G e0 xs Es) :
    xs.length < Es.length := by
  have hle : xs.length ≤ Es.length :=
    Obs.Budget.budget_tick G hinj e0 s xs hd hsys Es halph
  have hne : xs.length ≠ Es.length := by
    intro heq
    have hsat : Saturated G e0 xs Es :=
      (Bridge.Saturation.saturation_iff_tick_equality
        G hinj e0 s xs hd hsys Es hEs halph).mp heq
    exact hnsat hsat
  exact Nat.lt_of_le_of_ne hle hne

/-! ## C2 — flatness budget vs aliveness -/

/-- Faces needed to leave Forman negativity from zero faces. -/
def recombinationsNeeded (degU degV : Nat) : Nat :=
  unpaidFlatness degU degV 0

/-- Aliveness budget from committed predicate capacity `|caps T|`. -/
def alivenessBudget (T : Nat) : Nat :=
  Bridge.Capacity.caps T

/-- Expand-profile capacity budget at `K = 2`. -/
def expandBudget (T : Nat) : Nat :=
  Geom.Profile.capacityOf 2 Geom.Profile.expand T

theorem recombinationsNeeded_kmin_internal :
    recombinationsNeeded
      (internalDeg Bridge.Alphabet.Kmin)
      (internalDeg Bridge.Alphabet.Kmin) =
      Bridge.Alphabet.Kmin := by
  rw [Kmin_internal_deg, Bridge.Alphabet.Kmin_eq]
  rfl

/-- **C2.** Kmin internal-edge flatness cost (`= 2`) fits inside `|caps T|`
    for every horizon (caps = 2^(T+2) ≥ 4). -/
theorem kmin_flatness_within_caps_budget (T : Nat) :
    recombinationsNeeded
      (internalDeg Bridge.Alphabet.Kmin)
      (internalDeg Bridge.Alphabet.Kmin) ≤
      alivenessBudget T := by
  rw [recombinationsNeeded_kmin_internal, Bridge.Alphabet.Kmin_eq]
  show 2 ≤ Bridge.Capacity.caps T
  rw [Bridge.Capacity.caps_eq]
  -- 2 ≤ 2^1 ≤ 2^(T+2); avoid rewriting the `2` inside `T+2`
  have hle : 1 ≤ T + 2 := Nat.succ_le_succ (Nat.zero_le (T + 1))
  have hstep : (2 : Nat) ≤ 2 ^ 1 := by decide
  have hpow : 2 ^ 1 ≤ 2 ^ (T + 2) :=
    Nat.pow_le_pow_right (by decide : 0 < 2) hle
  exact Nat.le_trans hstep hpow

/-- **C2′.** Same cost fits expand capacity `2^T` once `T ≥ 1`. -/
theorem kmin_flatness_within_expand_budget
    (T : Nat) (hT : 1 ≤ T) :
    recombinationsNeeded
      (internalDeg Bridge.Alphabet.Kmin)
      (internalDeg Bridge.Alphabet.Kmin) ≤
      expandBudget T := by
  rw [recombinationsNeeded_kmin_internal, Bridge.Alphabet.Kmin_eq]
  show 2 ≤ 2 ^ T
  have h2 : (2 : Nat) = 2 ^ 1 := rfl
  rw [h2]
  exact Nat.pow_le_pow_right (by decide : 0 < 2) hT

/-! ## Sprint package -/

/-- Sprint A1–A3 + B4 + C2: H is Lean-testable.
    Vacuum ≠ matter-channel; saturation fixes effective matter;
    slack exists below saturation; Kmin flatness fits aliveness budget. -/
theorem effective_matter_sprint :
    VacuumDynamics Geom.Registration.oscStep ∧
    Geom.Registration.Merges Geom.Registration.swapStep ∧
    (∀ T, recombinationsNeeded
      (internalDeg Bridge.Alphabet.Kmin)
      (internalDeg Bridge.Alphabet.Kmin) ≤ alivenessBudget T) ∧
    Bridge.Alphabet.Kmin = 2 :=
  ⟨osc_is_vacuum,
   Geom.Registration.swap_registers.2.1,
   kmin_flatness_within_caps_budget,
   Bridge.Alphabet.Kmin_eq⟩

#print axioms osc_is_vacuum
#print axioms vacuum_vs_matter_channel_separable
#print axioms slack_below_saturation
#print axioms kmin_flatness_within_caps_budget
#print axioms kmin_flatness_within_expand_budget
#print axioms effective_matter_sprint

end Bridge.EffectiveMatter
