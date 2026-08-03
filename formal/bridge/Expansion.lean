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

Four meanings of "expansion" (spec):

  E1  monotone growth of structure — *theorem* (this file)
  E2  exponential capacity at fixed rate — *theorem* (this file);
      liveness forces the growth (explanatory direction)
  E3  growth of a spatial metric — *blocked* (R-1 ultrametric obstruction)
  E4  Friedmann dynamics with matter — *refused*

**T-13** (conditional). Causal-set pedigree: order + number = geometry
(Malament: causal structure ⇒ metric up to conformal factor; counting
fixes the factor). DAG owns order (dim = 1) and number (capacity
schedule). Flag the postulate `NumberEqualsVolume`: identify counted
volume with the capacity schedule. Then volume grows as `K^t`; at
`K = 2`, one bit per naming tick. de Sitter's volume law from
liveness + one flagged postulate.

Units caveat: ticks are naming steps; no seconds are derivable; no
observable `H₀` is forecast. E4 refusal holds.
-/

namespace Bridge.Expansion

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
theorem ascent_is_time (tTurn : Nat) :
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

/-- Flagged reading (causal-set: number = volume). Counted volume *is*
    identified with the capacity schedule. Not a derived physical metric;
    the postulate is this identification. -/
def countedVolume (K T : Nat) : Nat :=
  Geom.Profile.capacityOf K Geom.Profile.expand T

/-- The postulate, as a named marker: volume readings use `countedVolume`. -/
def NumberEqualsVolume : Prop := True

/-- Postulate is flagged available (content = the identification above). -/
theorem number_equals_volume_flagged : NumberEqualsVolume := trivial

/-- Discrete Hubble: volume doubles per naming tick at `K = 2`.
    Units: naming ticks, not seconds — no `H₀` forecast. -/
theorem discrete_Hubble_one_bit_per_tick (T : Nat) :
    countedVolume 2 (T + 1) = 2 * countedVolume 2 T :=
  E2_rate_law T

/-- Counted de Sitter volume law on expand at `Kmin`. -/
theorem counted_deSitter_volume (T : Nat) :
    countedVolume Bridge.Alphabet.Kmin T = 2 ^ T := by
  rw [Bridge.Alphabet.Kmin_eq]
  exact Bridge.Capacity.expand_capacity_two T

/-- **T-13.** Expansion as the price of liveness (conditional form).
    E1 + E2 + order dim 1 + counted volume = `K^T` under the flagged
    number=volume reading + ω-flatline. Units caveat: ticks ≠ seconds. -/
theorem T13_expansion_conditional :
    (∀ k, ¬ ∃ (f : Ladder.Level (k + 1) → Ladder.Level k),
      ∀ x y, f x = f y → x = y) ∧
    (∀ T, Geom.Profile.Alive 2 Geom.Profile.expand T) ∧
    (∀ T, countedVolume 2 (T + 1) = 2 * countedVolume 2 T) ∧
    (∀ T, countedVolume Bridge.Alphabet.Kmin T = 2 ^ T) ∧
    NumberEqualsVolume ∧
    (∀ j k, Density.levelCard j = Density.levelCard k → j = k) ∧
    (∃ b : Limit.LevelOmegaPlusOne,
      ∀ a : Limit.LevelOmega, (some a : Limit.LevelOmegaPlusOne) ≠ b) ∧
    Bridge.Alphabet.Kmin = 2 :=
  ⟨E1_no_retraction, E2_expand_eternally_alive, discrete_Hubble_one_bit_per_tick,
   counted_deSitter_volume, number_equals_volume_flagged,
   OmegaDuration.omega_duration_package.1,
   OmegaDuration.namer_new_at_omega,
   Bridge.Alphabet.Kmin_eq⟩

#print axioms E1_monotone_structure
#print axioms E2_exponential_capacity
#print axioms discrete_Hubble_one_bit_per_tick
#print axioms T13_expansion_conditional
#print axioms ascent_is_time
#print axioms omega_flatline_ancestry_continues

end Bridge.Expansion
