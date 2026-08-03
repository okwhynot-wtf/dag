import Ladder
import Geom.Registration
import Geom.Profile
import Capacity

/-!
# T-2 Tick simulation (fragment)

Naming ticks (DM ladder steps) vs microticks (AG applications of U).
Proven fragment: the committed ladder yields an expanding mute schedule
matching AG provision at `K = 2`; full functorial round-trips remain
residue until completed (see `docs/RESIDUE.md`).
-/

namespace Bridge.TickSimulation

/-- A microtick is one joint step `U`. -/
abbrev Microstep (S E : Type) := S × E → S × E

/-- A naming tick is one ladder level increment. -/
def namingTick (k : Nat) : Type := Ladder.Level (k + 1)

/-- Committed ladder at horizon `T` supplies capacity `2^(T+2)`. -/
theorem naming_supplies_caps (T : Nat) :
    Bridge.Capacity.caps T = 2 ^ (T + 2) :=
  Bridge.Capacity.caps_eq T

/-- Expanding conveyor (AG) sustains stream muteness at alphabet size 2. -/
theorem expand_sustains_mute :
    ∀ T : Nat, Geom.Profile.Alive 2 Geom.Profile.expand T →
      Geom.Profile.capacityOf 2 Geom.Profile.expand T = 2 ^ T := by
  intro T _
  exact Bridge.Capacity.expand_capacity_two T

/-- Oscillator microstep never merges (AG pole) — silent archive. -/
theorem oscillator_silent :
    ¬ Geom.Registration.Merges Geom.Registration.oscStep ∧
    ¬ Geom.Registration.Registers Geom.Registration.oscStep :=
  ⟨Geom.Registration.osc_never_registers.2.1,
   Geom.Registration.osc_never_registers.2.2⟩

/-- Swap microstep merges and registers. -/
theorem swap_writes :
    Geom.Registration.Merges Geom.Registration.swapStep ∧
    Geom.Registration.Registers Geom.Registration.swapStep :=
  ⟨Geom.Registration.swap_registers.2.1,
   Geom.Registration.swap_registers.2.2⟩

/-- **T-2 fragment.** Round-trip identity on the committed path:
    naming capacity equals predicate count; expand profile matches
    demand `K^T` at `K = 2`; both AG poles are available as microsteps. -/
theorem tick_simulation_fragment :
    (∀ T, Bridge.Capacity.caps T = 2 ^ (T + 2)) ∧
    (∀ T, Geom.Profile.capacityOf 2 Geom.Profile.expand T = 2 ^ T) ∧
    (¬ Geom.Registration.Merges Geom.Registration.oscStep) ∧
    (Geom.Registration.Registers Geom.Registration.swapStep) :=
  ⟨naming_supplies_caps, Bridge.Capacity.expand_capacity_two,
   oscillator_silent.1, swap_writes.2⟩

/-- Full functorial factorisation (both directions, identity round-trips
    on all Registration sequences) is not claimed here. -/
def fullSimulationOpen : True := True.intro

#print axioms tick_simulation_fragment
#print axioms naming_supplies_caps

end Bridge.TickSimulation
