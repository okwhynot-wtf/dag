import Alphabet
import Capacity
import ArchiveMustSpeak
import EffectiveMatter
import Expansion
import Forman
import Geom.Profile

/-!
# Phase E — optional continuum toys (not load-bearing for H)

Hypothesis H (matter = saturated record flux) already survives A–D.
Phase E only asks whether familiar *names* (temperature, radiation,
expansion) show up as discrete caricatures.

- **E1** Combinatorial `T_c` / Clausius: `S = log₂ |caps T| = T+2`, `ΔS = 1`
- **E2** Finite Page radiation = post-exhaustion archive speech (T-10)
- **E3** Discrete Friedmann-shaped capacity update at Kmin (no continuum, no H₀)

Failure of E does not kill H. See `docs/MATTER_FLUX_PLAN.md` Phase E.
-/

namespace Bridge.PhaseEToys

open Bridge.EffectiveMatter
open Bridge.Expansion
open Bridge.ArchiveMustSpeak

/-! ## E1 — Combinatorial temperature / Clausius -/

/-- Bit-count of the capacity ledger at depth `T`:
    `|caps T| = 2^(T+2)`, so `log₂ |caps T| = T + 2`. -/
def entropyBits (T : Nat) : Nat := T + 2

theorem entropyBits_eq_log_caps (T : Nat) :
    Bridge.Capacity.caps T = 2 ^ entropyBits T := by
  simp [entropyBits, Bridge.Capacity.caps_eq]

/-- Entropy jump when the ledger advances one tick. -/
def deltaS (T : Nat) : Nat := entropyBits (T + 1) - entropyBits T

/-- One-tick entropy jump is exactly one bit. -/
theorem deltaS_eq_one (T : Nat) : deltaS T = 1 := by
  unfold deltaS entropyBits
  -- (T+1)+2 = T+3 = (T+2)+1 definitionally
  change (T + 3) - (T + 2) = 1
  change ((T + 2) + 1) - (T + 2) = 1
  exact Nat.add_sub_self_left (T + 2) 1

/-- Combinatorial temperature: heat per unit entropy at saturation.
    With `Q_bit := 1` and `ΔS = 1`, one gets `T_c = 1`. -/
def combinatorialTemp (_T : Nat) : Nat := 1

/-- Clausius toy: δQ = T_c · ΔS with unit heat quantum. -/
def heatQuantum (_T : Nat) : Nat := 1

theorem clausius_caricature (T : Nat) :
    combinatorialTemp T * deltaS T = 1 := by
  simp [combinatorialTemp, deltaS_eq_one T]

theorem clausius_form (T : Nat) :
    heatQuantum T = combinatorialTemp T * deltaS T := by
  simp [heatQuantum, clausius_caricature T]

/-! ## E2 — Finite Page radiation = archive speech after exhaustion -/

/-- Radiation reading of a bounce Page horizon: thermal (alive+mute)
    window up to turnaround, then exhaustion forces archive speech. -/
structure PageRadiation where
  K : Nat
  hK : 2 ≤ K
  tTurn : Nat

/-- **E2a.** At Page time (= bounce exhaustion), the archive horizon is hit. -/
theorem page_radiation_horizon (r : PageRadiation) :
    Geom.Profile.IsExhaustionTick r.K (Geom.Profile.bounce r.tTurn) r.tTurn :=
  page_time_is_exhaustion r.hK r.tTurn

/-- **E2b.** Before exhaustion: alive on the bounce; at turnaround: speak. -/
theorem page_radiation_thermal_then_speech (r : PageRadiation) :
    (∀ T, T ≤ r.tTurn →
      Geom.Profile.Alive r.K (Geom.Profile.bounce r.tTurn) T) ∧
    Geom.Profile.IsExhaustionTick r.K (Geom.Profile.bounce r.tTurn) r.tTurn :=
  thermal_window_then_speech r.hK r.tTurn

/-- **E2c.** Post-exhaustion flux is the matter channel (Landauer), not vacuum. -/
theorem radiation_is_matter_channel :
    VacuumDynamics Geom.Registration.oscStep ∧
    Geom.Registration.Merges Geom.Registration.swapStep ∧
    Geom.Registration.Registers Geom.Registration.swapStep :=
  ⟨osc_is_vacuum,
   Geom.Registration.swap_registers.2.1,
   Geom.Registration.swap_registers.2.2⟩

/-- **E2.** Finite Page radiation package: T-10 horizon + matter channel. -/
theorem finite_page_radiation :
    (∀ {K : Nat}, 2 ≤ K → ∀ tTurn,
      Geom.Profile.IsExhaustionTick K (Geom.Profile.bounce tTurn) tTurn) ∧
    VacuumDynamics Geom.Registration.oscStep ∧
    Geom.Registration.Registers Geom.Registration.swapStep ∧
    Bridge.Alphabet.Kmin = 2 :=
  ⟨fun hK tTurn => page_time_is_exhaustion hK tTurn,
   osc_is_vacuum,
   Geom.Registration.swap_registers.2.2,
   Bridge.Alphabet.Kmin_eq⟩

/-! ## E3 — Discrete Friedmann-shaped capacity update -/

/-- Capacity "scale factor": bit-depth of the ledger (`log₂ |caps|`). -/
def scaleFactor (T : Nat) : Nat := entropyBits T

/-- One-tick growth of the scale factor (always +1 bit). -/
def deltaScale (T : Nat) : Nat := scaleFactor (T + 1) - scaleFactor T

theorem deltaScale_eq_one (T : Nat) : deltaScale T = 1 := by
  -- scaleFactor = entropyBits, so deltaScale = deltaS
  exact deltaS_eq_one T

/-- Discrete Hubble caricature: Δa / Δt with Δt := 1 naming tick. -/
def hubbleDisc (T : Nat) : Nat := deltaScale T

theorem hubble_disc_eq_one (T : Nat) : hubbleDisc T = 1 :=
  deltaScale_eq_one T

/-- Caps double each tick — Friedmann-shaped growth of the capacity arena. -/
theorem caps_double (T : Nat) :
    Bridge.Capacity.caps (T + 1) = 2 * Bridge.Capacity.caps T := by
  simp [Bridge.Capacity.caps_eq, Nat.pow_succ, Nat.mul_comm]

/-- Counted volume doubles (T-13 discrete Hubble), same shape. -/
theorem volume_double (T : Nat) :
    countedVolume 2 (T + 1) = 2 * countedVolume 2 T :=
  discrete_Hubble_one_bit_per_tick T

/-- At Kmin the Forman growth cost is bounded by capacity (C2),
    so the Friedmann-shaped update stays ledger-paid. -/
theorem friedmann_shaped_capacity_update (T : Nat) :
    recombinationsNeeded
      (Bridge.Forman.internalDeg Bridge.Alphabet.Kmin)
      (Bridge.Forman.internalDeg Bridge.Alphabet.Kmin) ≤
      alivenessBudget T ∧
    hubbleDisc T = 1 ∧
    Bridge.Capacity.caps (T + 1) = 2 * Bridge.Capacity.caps T ∧
    scaleFactor (T + 1) = scaleFactor T + 1 :=
  ⟨kmin_flatness_within_caps_budget T,
   hubble_disc_eq_one T,
   caps_double T,
   by simp [scaleFactor, entropyBits]⟩

/-! ## Phase E package -/

/-- **Phase E.** Optional toys: Clausius `T_c`, Page radiation, discrete
    Friedmann-shaped capacity. Failure would not kill H. -/
theorem phase_E_continuum_toys :
    (∀ T, deltaS T = 1) ∧
    (∀ T, heatQuantum T = combinatorialTemp T * deltaS T) ∧
    (∀ {K : Nat}, 2 ≤ K → ∀ tTurn,
      Geom.Profile.IsExhaustionTick K (Geom.Profile.bounce tTurn) tTurn) ∧
    Geom.Registration.Registers Geom.Registration.swapStep ∧
    (∀ T, Bridge.Capacity.caps (T + 1) = 2 * Bridge.Capacity.caps T) ∧
    (∀ T, hubbleDisc T = 1) ∧
    Bridge.Alphabet.Kmin = 2 :=
  ⟨deltaS_eq_one, clausius_form,
   fun hK tTurn => page_time_is_exhaustion hK tTurn,
   Geom.Registration.swap_registers.2.2,
   caps_double, hubble_disc_eq_one,
   Bridge.Alphabet.Kmin_eq⟩

#print axioms deltaS_eq_one
#print axioms clausius_form
#print axioms finite_page_radiation
#print axioms friedmann_shaped_capacity_update
#print axioms phase_E_continuum_toys

end Bridge.PhaseEToys
