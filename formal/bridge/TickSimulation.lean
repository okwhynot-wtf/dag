import Ladder
import Tower
import Geom.Registration
import Geom.Profile
import Geom.Provision
import Geom.Freshness
import Capacity
import Environment

/-!
# T-2 Tick simulation

Committed-path equivalence between naming ticks (ladder) and microticks
(AG expand / Registration poles):

* **→** ladder supplies caps; expand at `K = 2` is eternally alive and
  stream-mute (provision);
* **←** expand capacity doubles each tick, matching predicate-count
  doubling; each naming tick adjoins a fresh namer (strict growth);
* identity round-trips on the committed path (expand profile ↔ caps arith).

Full factorisation of Registration sequences as *ladder carrier*
extensions is obstructed (`RegistrationFactor.registration_vs_naming_obstruction`):
swap registers forever on fixed `E = Bool` while naming grows `levelCard`.
Positive remnant: every injective 2-merge admits a namer-shaped label witness
(`registers_admits_namer`). Naming-tick/microtick identification stays on the
committed expand path plus that label fragment.
-/

namespace Bridge.TickSimulation

open Geom.Registration

/-- A microtick is one joint step `U`. -/
abbrev Microstep (S E : Type) := S × E → S × E

/-- A naming tick lands in `Level (k+1)`. -/
def namingCarrier (k : Nat) : Type := Ladder.Level (k + 1)

/-- Committed alphabet for K = 2. -/
def blank2 : List Bool := [false, true]

theorem blank2_length : blank2.length = 2 := rfl

/-! ## Forward: naming → microtick schedule -/

theorem naming_supplies_caps (T : Nat) :
    Bridge.Capacity.caps T = 2 ^ (T + 2) :=
  Bridge.Capacity.caps_eq T

/-- Expand profile is alive at every horizon for `K = 2`. -/
theorem expand_eternally_alive (T : Nat) :
    Geom.Profile.Alive 2 Geom.Profile.expand T :=
  Bridge.Capacity.expand_alive T

/-- Demand fits ladder caps. -/
theorem demand_le_naming_caps (T : Nat) :
    2 ^ T ≤ Bridge.Capacity.caps T :=
  Bridge.Capacity.alive_arith T

/-- **Committed ladder yields mute expanding U** (provision at `|A|=2`). -/
theorem committed_yields_mute
    (g : Bool → Bool) (hg : ∀ a b : Bool, g a = g b → a = b)
    (blank : Bool) (s0 : Bool) :
    Geom.Exhaustion.Inj (Geom.Provision.expandStep g blank)
    ∧ (∀ t, Geom.Exhaustion.FreshAt
        (Geom.Provision.expandStep g blank)
        (Geom.Provision.gIter g s0) (fun _ => blank2)
        (Geom.Provision.expandCaps blank2) t)
    ∧ (∀ T, (Geom.Provision.expandCaps (Eout := Bool) blank2 T).length =
        2 ^ T) := by
  have hprov := Geom.Provision.provision hg blank s0 blank2
  refine ⟨hprov.1, hprov.2.2.1, ?_⟩
  intro T
  have h := hprov.2.2.2.2 T
  rw [blank2_length] at h
  exact h

/-! ## Reverse: microtick rates → naming growth -/

/-- Expand capacity doubles each tick at `K = 2`. -/
theorem expand_doubles (T : Nat) :
    Geom.Profile.capacityOf 2 Geom.Profile.expand (T + 1) =
      2 * Geom.Profile.capacityOf 2 Geom.Profile.expand T := by
  -- capacityOf 2 expand n = 2^n
  change 2 ^ (T + 1) = 2 * (2 ^ T)
  rw [Nat.pow_succ, Nat.mul_comm]

/-- Predicate caps double each naming tick. -/
theorem caps_double (T : Nat) :
    Bridge.Capacity.caps (T + 1) = 2 * Bridge.Capacity.caps T := by
  rw [Bridge.Capacity.caps_eq, Bridge.Capacity.caps_eq]
  -- 2^(T+1+2) = 2^(T+3) = 2 * 2^(T+2)
  change 2 ^ (T + 3) = 2 * (2 ^ (T + 2))
  rw [show T + 3 = (T + 2) + 1 from rfl, Nat.pow_succ, Nat.mul_comm]

/-- Naming tick adjoins a fresh namer (strict growth). -/
theorem naming_tick_new_slot (k : Nat) :
    ∃ b : Ladder.Level (k + 1),
      ∀ a : Ladder.Level k, (some a : Ladder.Level (k + 1)) ≠ b :=
  Ladder.ladder_grows k

/-- Naming tick is a naming extension (Tower). -/
theorem naming_tick_extension (k : Nat) :
    Tower.NamingExtension
      (Ladder.rep k) (Ladder.rep (k + 1)) some (Ladder.dodgeEscape k) :=
  Ladder.ladder_step k

/-! ## Identity round-trips on the committed path -/

/-- Expand depth equals naming index on the committed profile. -/
theorem committed_roundtrip_depth (T : Nat) :
    Bridge.Capacity.committedProfile T = T ∧
    Geom.Profile.capacityOf 2 Geom.Profile.expand T = 2 ^ T ∧
    2 ^ T ≤ Bridge.Capacity.caps T :=
  ⟨Bridge.Capacity.committed_is_expand T,
   Bridge.Capacity.expand_capacity_two T,
   Bridge.Capacity.alive_arith T⟩

/-- Rate weld: expand doubling ≅ caps doubling. -/
theorem rate_weld (T : Nat) :
    Geom.Profile.capacityOf 2 Geom.Profile.expand (T + 1) =
      2 * Geom.Profile.capacityOf 2 Geom.Profile.expand T ∧
    Bridge.Capacity.caps (T + 1) = 2 * Bridge.Capacity.caps T :=
  ⟨expand_doubles T, caps_double T⟩

/-- AG poles as microsteps available on either reading. -/
theorem oscillator_silent :
    ¬ Merges oscStep ∧ ¬ Registers oscStep :=
  ⟨osc_never_registers.2.1, osc_never_registers.2.2⟩

theorem swap_writes :
    Merges swapStep ∧ Registers swapStep :=
  ⟨swap_registers.2.1, swap_registers.2.2⟩

/-- **T-2.** Tick simulation on the committed path. -/
theorem tick_simulation :
    (∀ T, Bridge.Capacity.caps T = 2 ^ (T + 2)) ∧
    (∀ T, Geom.Profile.Alive 2 Geom.Profile.expand T) ∧
    (∀ T, 2 ^ T ≤ Bridge.Capacity.caps T) ∧
    (∀ T, Geom.Profile.capacityOf 2 Geom.Profile.expand (T + 1) =
      2 * Geom.Profile.capacityOf 2 Geom.Profile.expand T) ∧
    (∀ T, Bridge.Capacity.caps (T + 1) = 2 * Bridge.Capacity.caps T) ∧
    (∀ k, Tower.NamingExtension
      (Ladder.rep k) (Ladder.rep (k + 1)) some (Ladder.dodgeEscape k)) ∧
    (∀ k, ∃ b : Ladder.Level (k + 1),
      ∀ a : Ladder.Level k, (some a : Ladder.Level (k + 1)) ≠ b) ∧
    (¬ Merges oscStep) ∧ (Registers swapStep) :=
  ⟨naming_supplies_caps, expand_eternally_alive, demand_le_naming_caps,
   expand_doubles, caps_double, naming_tick_extension, naming_tick_new_slot,
   oscillator_silent.1, swap_writes.2⟩

/-- Backward-compatible fragment name. -/
theorem tick_simulation_fragment :
    (∀ T, Bridge.Capacity.caps T = 2 ^ (T + 2)) ∧
    (∀ T, Geom.Profile.capacityOf 2 Geom.Profile.expand T = 2 ^ T) ∧
    (¬ Merges oscStep) ∧ (Registers swapStep) :=
  ⟨naming_supplies_caps, Bridge.Capacity.expand_capacity_two,
   oscillator_silent.1, swap_writes.2⟩

/-- Obstruction discharged in `RegistrationFactor.lean`. -/
def arbitraryRegistration_factor_open : False → True := fun h => h.elim

#print axioms tick_simulation
#print axioms committed_yields_mute
#print axioms rate_weld
#print axioms committed_roundtrip_depth
#print axioms tick_simulation_fragment

end Bridge.TickSimulation
