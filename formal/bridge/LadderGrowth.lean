import Ladder
import Density
import Tower
import Limit
import Geom.Profile
import Geom.Provision
import Geom.Exhaustion
import Obs.CausalOrder
import Obs.Dimension
import OmegaDuration
import Capacity
import Alphabet

/-!
# Expansion — E1 / E2 named; T-13 conditional (number = volume)

Four meanings of "expansion":

  E1  monotone growth of structure — theorem (this file)
  E2  exponential capacity at fixed rate — theorem (this file);
      liveness forces the growth (explanatory direction)
  E3  growth of a spatial metric — blocked (R-1 ultrametric obstruction)
  E4  Friedmann dynamics with matter — not derived

**T-13** (conditional). Causal-set pedigree: order + number = geometry
(Malament: causal structure ⇒ metric up to conformal factor; counting
fixes the factor). DAG owns order (dim = 1) and number (capacity
schedule). Flag the postulate `NumberEqualsVolume`: identify counted
volume with the capacity schedule. Then volume grows as `K^t`; at
`K = 2`, one bit per naming tick. Capacity doubling from
liveness under the counted-volume reading.

Units caveat: ticks are naming steps; no seconds are derivable; no
observable `H₀` is forecast. Continuum Friedmann dynamics (E4) are not
derived.
-/

namespace Bridge.LadderGrowth

/-! ## E1 — monotone growth of structure -/

/-- E1a. Every ladder step has a new namer (arena grows). -/
theorem E1_namer_always_new (k : Nat) :
    ∃ b : Ladder.Level (k + 1),
      (∀ a : Ladder.Level k, Ladder.rep (k + 1) b (some a) =
        Ladder.dodgeEscape k a) ∧
      (∀ a : Ladder.Level k, (some a : Ladder.Level (k + 1)) ≠ b) :=
  Tower.namer_is_new (Ladder.ladder_step k)

/-- E1b. No level retracts onto its predecessor. -/
theorem E1_no_retraction (k : Nat) :
    ¬ ∃ (f : Ladder.Level (k + 1) → Ladder.Level k),
      ∀ x y, f x = f y → x = y :=
  Density.no_retraction k

/-- E1c. Prior structure embeds forward (lift injective). -/
theorem E1_lift_injective (k j : Nat) :
    ∀ x y : Ladder.Level k,
      Ladder.lift k j x = Ladder.lift k j y → x = y :=
  Ladder.lift_injective k j

/-- **E1.** Arena grows forever: new namers, no retraction, lifts embed. -/
theorem E1_monotone_structure :
    (∀ k, ∃ b : Ladder.Level (k + 1),
      (∀ a : Ladder.Level k, Ladder.rep (k + 1) b (some a) =
        Ladder.dodgeEscape k a) ∧
      (∀ a : Ladder.Level k, (some a : Ladder.Level (k + 1)) ≠ b)) ∧
    (∀ k, ¬ ∃ (f : Ladder.Level (k + 1) → Ladder.Level k),
      ∀ x y, f x = f y → x = y) ∧
    (∀ k j, ∀ x y : Ladder.Level k,
      Ladder.lift k j x = Ladder.lift k j y → x = y) :=
  ⟨E1_namer_always_new, E1_no_retraction, E1_lift_injective⟩

/-! ## E2 — exponential capacity; liveness forces growth -/

/-- E2a. Expand schedule: `c(t+1) = 2 · c(t)`. -/
theorem E2_rate_law (T : Nat) :
    Geom.Profile.capacityOf 2 Geom.Profile.expand (T + 1) =
      2 * Geom.Profile.capacityOf 2 Geom.Profile.expand T := by
  change 2 ^ (T + 1) = 2 * 2 ^ T
  rw [Nat.pow_succ, Nat.mul_comm]

/-- E2b. Eternal mute aliveness ⇒ capacity unbounded (liveness prices
    expansion). -/
theorem E2_liveness_forces_expansion
    {S Eout Eint : Type} [DecidableEq Eint]
    (U : S × Eout × Eint → S × Eout × Eint)
    (σ : Nat → S) (es : Nat → List Eout) (caps : Nat → List Eint)
    (hU : Geom.Exhaustion.Inj U) {K : Nat} (hK : 2 ≤ K)
    (hm : ∀ t, Geom.Exhaustion.MergesAt U σ es caps t)
    (hf : ∀ t, Geom.Exhaustion.FreshAt U σ es caps t)
    (hc : ∀ t, Geom.Exhaustion.Confined U σ es caps t)
    (hdes : ∀ t, Geom.Exhaustion.Distinct (es t))
    (hKlen : ∀ t, K ≤ (es t).length)
    (i₀ : Eint) (hi₀ : i₀ ∈ caps 0) :
    ∀ C : Nat, C < (caps C).length :=
  Geom.Provision.eternal_aliveness_needs_expansion
    U σ es caps hU hK hm hf hc hdes hKlen i₀ hi₀

/-- E2c. Expand profile is eternally alive at `K = 2`. -/
theorem E2_expand_eternally_alive (T : Nat) :
    Geom.Profile.Alive 2 Geom.Profile.expand T :=
  Bridge.Capacity.expand_alive T

/-- **E2.** Fixed-rate exponential capacity; eternal aliveness requires
    expansion in the counted sense. -/
theorem E2_exponential_capacity :
    (∀ T, Geom.Profile.capacityOf 2 Geom.Profile.expand (T + 1) =
      2 * Geom.Profile.capacityOf 2 Geom.Profile.expand T) ∧
    (∀ T, Geom.Profile.Alive 2 Geom.Profile.expand T) ∧
    (∀ T, Geom.Profile.capacityOf 2 Geom.Profile.expand T = 2 ^ T) ∧
    Bridge.Alphabet.Kmin = 2 :=
  ⟨E2_rate_law, E2_expand_eternally_alive,
   Bridge.Capacity.expand_capacity_two, Bridge.Alphabet.Kmin_eq⟩

/-! ## Order input (time, no transversal width) -/

/-- Causal ascent has order dimension exactly one. -/
theorem ascent_order_dim_one (tTurn : Nat) :
    Obs.Dimension.OrderDimEq tTurn (Obs.CausalOrder.fwdPrecedes tTurn) 1 :=
  Obs.Dimension.ascent_order_dim_eq_one tTurn

/-- ω-flatline: magnitude completes while ancestry continues
    (Padmanabhan / holographic-equipartition echo — Interpretation). -/
theorem omega_flatline_ancestry_continues :
    (∀ j k, Density.levelCard j = Density.levelCard k → j = k) ∧
    ((∀ x y : Option Nat,
        OmegaDuration.optionNatToNat x = OmegaDuration.optionNatToNat y →
          x = y) ∧
      (∀ n, ∃ x, OmegaDuration.optionNatToNat x = n)) ∧
    ((∀ x y : Option Limit.LevelOmega,
        OmegaDuration.optionOmegaToOmega x =
          OmegaDuration.optionOmegaToOmega y → x = y) ∧
      (∀ v, ∃ x, OmegaDuration.optionOmegaToOmega x = v)) ∧
    (∀ j k, Limit.LevelOmega.stage j = Limit.LevelOmega.stage k → j = k) ∧
    (∀ j k, Limit.appearsBy (Limit.LevelOmega.stage j) =
      Limit.appearsBy (Limit.LevelOmega.stage k) → j = k) ∧
    (∃ b : Limit.LevelOmegaPlusOne,
      ∀ a : Limit.LevelOmega, (some a : Limit.LevelOmegaPlusOne) ≠ b) :=
  OmegaDuration.omega_duration_package

/-! ## T-13 — conditional: number = volume postulate -/

/-- Counted volume schedule (expand capacity). Geometric reading requires
    an explicit `VolumeReading` hypothesis in dependent theorems. -/
def countedVolume (K T : Nat) : Nat :=
  Geom.Profile.capacityOf K Geom.Profile.expand T

/-- **Flagged postulate (lives in the type).** Assuming a `VolumeReading`
    means: treat `countedVolume` as geometric volume (number = volume).
    Not a derived physical metric; not seconds; no `H₀`. -/
structure VolumeReading where

/-- Canonical token that the flagged reading is in force. -/
def numberEqualsVolume : VolumeReading := ⟨⟩

/-- Alias for the volume-reading token type. -/
abbrev NumberEqualsVolume : Prop := Nonempty VolumeReading

theorem number_equals_volume_flagged : NumberEqualsVolume :=
  ⟨numberEqualsVolume⟩

/-- Doubling per naming tick under the volume reading: doubles per naming tick at `K = 2`.
    Units: naming ticks, not seconds — no `H₀` forecast. -/
theorem doubling_per_tick_at_Kmin (_vr : VolumeReading) (T : Nat) :
    countedVolume 2 (T + 1) = 2 * countedVolume 2 T :=
  E2_rate_law T

/-- Counted capacity law on expand at `Kmin` (under volume reading). -/
theorem counted_capacity_at_Kmin (_vr : VolumeReading) (T : Nat) :
    countedVolume Bridge.Alphabet.Kmin T = 2 ^ T := by
  rw [Bridge.Alphabet.Kmin_eq]
  exact Bridge.Capacity.expand_capacity_two T

/-- **T-13.** Expansion as the price of liveness (conditional form).
    Requires an explicit `VolumeReading` so the number=volume flag cannot
    be dropped by a reader of the compression table. Units: ticks ≠ seconds. -/
theorem T13_counted_growth (_vr : VolumeReading) :
    (∀ k, ¬ ∃ (f : Ladder.Level (k + 1) → Ladder.Level k),
      ∀ x y, f x = f y → x = y) ∧
    (∀ T, Geom.Profile.Alive 2 Geom.Profile.expand T) ∧
    (∀ T, countedVolume 2 (T + 1) = 2 * countedVolume 2 T) ∧
    (∀ T, countedVolume Bridge.Alphabet.Kmin T = 2 ^ T) ∧
    (∀ j k, Density.levelCard j = Density.levelCard k → j = k) ∧
    (∃ b : Limit.LevelOmegaPlusOne,
      ∀ a : Limit.LevelOmega, (some a : Limit.LevelOmegaPlusOne) ≠ b) ∧
    Bridge.Alphabet.Kmin = 2 :=
  ⟨E1_no_retraction, E2_expand_eternally_alive,
   doubling_per_tick_at_Kmin _vr,
   counted_capacity_at_Kmin _vr,
   OmegaDuration.omega_duration_package.1,
   OmegaDuration.namer_new_at_omega,
   Bridge.Alphabet.Kmin_eq⟩

#print axioms E1_monotone_structure
#print axioms E2_exponential_capacity
#print axioms doubling_per_tick_at_Kmin
#print axioms T13_counted_growth
#print axioms ascent_order_dim_one
#print axioms omega_flatline_ancestry_continues

end Bridge.LadderGrowth
