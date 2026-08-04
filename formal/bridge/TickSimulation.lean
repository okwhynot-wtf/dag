import Ladder
import Tower
import Geom.Registration
import Geom.Profile
import Geom.Provision
import Geom.Freshness
import Capacity
import Environment
import RegistrationFactor
import Dil
import EffectiveMatter

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
(`registers_admits_namer`). Straightening (`Dil.straighten_fragment`) supplies
append-only normal form mod base gauge for UF archives. Classified kernel:
`tick_identification` (Fund exempt; swap necessity; Dil append
step; namer + rate weld + ladder `NamingExtension`). Keep `_licensed` until
v0.2 rename to `tick_identification`. Not a total functor on carriers.
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

/-- **T-2 tick identification (licensed remnant).** Committed-path
    simulation + namer-shaped label factor are discharged; carrier-level
    Registration→naming factorisation is obstructed (swap vs `levelCard`).
    Naming-tick ↔ microtick identification is licensed exactly on that
    remnant — not as a total functor on carriers. -/
theorem tick_identification_licensed :
    (∀ T, Bridge.Capacity.caps T = 2 ^ (T + 2)) ∧
    (∀ T, Geom.Profile.Alive 2 Geom.Profile.expand T) ∧
    (∀ k, Tower.NamingExtension
      (Ladder.rep k) (Ladder.rep (k + 1)) some (Ladder.dodgeEscape k)) ∧
    (∀ {S E : Type} {U : S × E → S × E},
      Inj U →
        ∀ w : Bridge.Environment.TwoMerge S E U,
          Bridge.RegistrationFactor.outsideSingleton
            (Bridge.Environment.recordLabel w false)
            (Bridge.Environment.recordLabel w true)) ∧
    (Inj Geom.Registration.swapStep ∧
      Merges Geom.Registration.swapStep ∧
      Registers Geom.Registration.swapStep) ∧
    (∀ T, 1 ≤ T → Density.levelCard 0 < Density.levelCard T) ∧
    Bridge.Alphabet.Kmin = 2 :=
  ⟨tick_simulation.1,
   tick_simulation.2.1,
   tick_simulation.2.2.2.2.2.1,
   fun hU w => (Bridge.RegistrationFactor.registers_admits_namer hU w).1,
   ⟨Geom.Registration.swap_inj,
     Geom.Registration.swap_registers.2.1,
     Geom.Registration.swap_registers.2.2⟩,
   fun T hT =>
     (Bridge.RegistrationFactor.registration_vs_naming_obstruction).2.2.2 T hT,
   Bridge.Alphabet.Kmin_eq⟩

/-- **Proof-skeleton ingredients** toward a classified T-2 (not the theorem).
    Straightening (UF ≅ append-only on base) + rate weld + namer shape +
    obstruction (necessity: eternal hypothesis is tight) + Fund exempt.
    Induction glue across ticks remains open — keep `_licensed`. -/
theorem tick_identification_ingredients :
    (∀ {S : Type} {u : S → S} {A : Bridge.Dil.Archive S u}
      (_fa : Bridge.Dil.UniqueFactorization A),
      ∃ _i : Bridge.Dil.ArchiveIso A
        (Bridge.Dil.freeOnBase S u (A.E 0) A.z0), True) ∧
    (∀ T,
      Geom.Profile.capacityOf 2 Geom.Profile.expand (T + 1) =
        2 * Geom.Profile.capacityOf 2 Geom.Profile.expand T ∧
      Bridge.Capacity.caps (T + 1) = 2 * Bridge.Capacity.caps T) ∧
    (∀ {S E : Type} {U : S × E → S × E},
      Inj U →
        ∀ w : Bridge.Environment.TwoMerge S E U,
          Bridge.RegistrationFactor.outsideSingleton
            (Bridge.Environment.recordLabel w false)
            (Bridge.Environment.recordLabel w true)) ∧
    (Inj Geom.Registration.swapStep ∧
      Merges Geom.Registration.swapStep ∧
      Registers Geom.Registration.swapStep ∧
      ∀ T, 1 ≤ T → Density.levelCard 0 < Density.levelCard T) ∧
    (¬ Merges Geom.Registration.oscStep) ∧
    Bridge.Alphabet.Kmin = 2 :=
  ⟨fun fa => Bridge.Dil.uf_straightens_mod_base fa,
   rate_weld,
   fun hU w => (Bridge.RegistrationFactor.registers_admits_namer hU w).1,
   ⟨Geom.Registration.swap_inj,
     Geom.Registration.swap_registers.2.1,
     Geom.Registration.swap_registers.2.2,
     fun T hT =>
       (Bridge.RegistrationFactor.registration_vs_naming_obstruction).2.2.2 T hT⟩,
   oscillator_silent.1,
   Bridge.Alphabet.Kmin_eq⟩

/-! ## Classified T-2 design (target → `tick_identification`)

Target slogan (Claude): *eternal registering dynamics factor through
naming extensions up to record gauge; periodic dynamics exempt at Fund;
obstructed swap proves dichotomy exhaustive.*

### Predicates (corpus types, not abstract jargon)

* **Fund-exempt / periodic:** `¬ Merges oscStep` — oscillator on
  `Bool × Unit` never demands a namer (`oscillator_no_namer_demand`).
* **Bounded-reuse eternal registration:** `swapStep` registers every
  microtick on fixed `E = Bool` while `Density.levelCard` climbs —
  `registration_vs_naming_obstruction` (necessity: unbounded hyp tight).
* **UF-archive remnant (positive half):** Dil `UniqueFactorization`
  archives straighten (`isoToFreeOnBase`) to `freeOnBase`; each microtick
  is `Word.cons` on a frozen base (`freeOnBase_append_step`); gauge =
  base agreement (`record_gauge_is_base_bijection`). Ladder side supplies
  `Tower.NamingExtension` at each `k`; rate weld matches expand/caps.

### Induction glue (operational)

After `isoToFreeOnBase`, letter at tick `T` is `(e0, w : Word S T)`.
One microtick = `r T s (e0,w) = (e0, cons s w)` — append-only on
`freeOnBase`. Peeling recovers `(s,(e0,w))` (`freeOnBase_factor_cons` /
`factorHistory_step`). That is the per-tick glue on Dil carriers.
It does **not** mean arbitrary `S×E → S×E` Registration sequences become
`Ladder.Level` morphisms.

### Fence

Can prove Fin-combinatorially now: dichotomy package below (Fund exempt +
swap obstruction + UF straighten/append + namer labels + rate weld +
ladder `NamingExtension`).

Would overclaim: a total functor `Registers U ↦ NamingExtension` on
carriers; or that `swapStep` factors as carrier naming.

v0.2 freezes this as `tick_identification` (section 0 cites the theorem;
section V inherits proved status). The `_licensed` package remains as the
historical remnant conjunction. Fence: not a carrier functor.
-/

/-- Fund / period-2 pole: no merge ⇒ no namer demand. -/
def FundExempt : Prop := ¬ Merges Geom.Registration.oscStep

/-- Eternal registration on a reusable 2-letter env (swap clothes). -/
def BoundedReuseRegisters : Prop :=
  Inj Geom.Registration.swapStep ∧
  Merges Geom.Registration.swapStep ∧
  Registers Geom.Registration.swapStep

/-- Naming carriers strictly grow past the Fund card. -/
def NamingCarrierClimbs : Prop :=
  ∀ T, 1 ≤ T → Density.levelCard 0 < Density.levelCard T

/-- **Per-tick induction step on Dil.** UF ⇒ straighten; microtick on the
    normal form is append (`Word.cons`); factor peels the letter back. -/
theorem tick_identification_step {S : Type} {u : S → S}
    {A : Bridge.Dil.Archive S u} (fa : Bridge.Dil.UniqueFactorization A) :
    (∃ _i : Bridge.Dil.ArchiveIso A
      (Bridge.Dil.freeOnBase S u (A.E 0) A.z0), True) ∧
    (∀ (T : Nat) (s : S) (e0 : A.E 0) (w : Bridge.Dil.Word S T),
      (Bridge.Dil.freeOnBase S u (A.E 0) A.z0).r T s (e0, w) =
        (e0, Bridge.Dil.Word.cons s w)) ∧
    (∀ (T : Nat) (s : S) (e0 : A.E 0) (w : Bridge.Dil.Word S T),
      (Bridge.Dil.freeOnBaseUF S u (A.E 0) A.z0).factor T
        (e0, Bridge.Dil.Word.cons s w) = (s, (e0, w))) :=
  ⟨Bridge.Dil.uf_straightens_mod_base fa,
   fun T s e0 w => Bridge.Dil.freeOnBase_append_step S u (A.E 0) A.z0 T s e0 w,
   fun T s e0 w => Bridge.Dil.freeOnBase_factor_cons S u (A.E 0) A.z0 T s e0 w⟩

/-- **Dichotomy (necessity + exemption).** Periodic Fund never demands a
    namer; eternal swap registers on fixed `|E|=2` while naming climbs —
    so carrier-level Registration→naming cannot be total. -/
theorem tick_identification_dichotomy :
    FundExempt ∧
    BoundedReuseRegisters ∧
    NamingCarrierClimbs ∧
    (∀ T, Density.levelCard T = T + 2) ∧
    Density.levelCard 0 = 2 :=
  ⟨oscillator_silent.1,
   ⟨Geom.Registration.swap_inj,
     Geom.Registration.swap_registers.2.1,
     Geom.Registration.swap_registers.2.2⟩,
   fun T hT =>
     (Bridge.RegistrationFactor.registration_vs_naming_obstruction).2.2.2 T hT,
   Bridge.RegistrationFactor.naming_carrier_card,
   Density.levelCard_eq 0⟩

/-- **T-2 tick identification (classified).**

    Eternal UF-archive dynamics straighten to append-only on a frozen base
    (record gauge = base relabel); each microtick is `Word.cons`; labels
    admit namer shape; rates weld to caps; ladder steps are
    `NamingExtension`. Periodic Fund is exempt. Obstructed swap proves the
    dichotomy's necessity half (unbounded/UF hyp cannot be dropped).

    Fence: not `Registers U → NamingExtension` on arbitrary carriers.
    Cited by `docs/DAG_SYMBOLIC.txt` §0 / §V at v0.2. -/
theorem tick_identification :
    FundExempt ∧
    BoundedReuseRegisters ∧
    NamingCarrierClimbs ∧
    (∀ {S : Type} {u : S → S} {A : Bridge.Dil.Archive S u}
      (_fa : Bridge.Dil.UniqueFactorization A),
      (∃ _i : Bridge.Dil.ArchiveIso A
        (Bridge.Dil.freeOnBase S u (A.E 0) A.z0), True) ∧
      (∀ (T : Nat) (s : S) (e0 : A.E 0) (w : Bridge.Dil.Word S T),
        (Bridge.Dil.freeOnBase S u (A.E 0) A.z0).r T s (e0, w) =
          (e0, Bridge.Dil.Word.cons s w))) ∧
    (∀ {S E : Type} {U : S × E → S × E},
      Inj U →
        ∀ w : Bridge.Environment.TwoMerge S E U,
          Bridge.RegistrationFactor.outsideSingleton
            (Bridge.Environment.recordLabel w false)
            (Bridge.Environment.recordLabel w true)) ∧
    (∀ T,
      Geom.Profile.capacityOf 2 Geom.Profile.expand (T + 1) =
        2 * Geom.Profile.capacityOf 2 Geom.Profile.expand T ∧
      Bridge.Capacity.caps (T + 1) = 2 * Bridge.Capacity.caps T) ∧
    (∀ k, Tower.NamingExtension
      (Ladder.rep k) (Ladder.rep (k + 1)) some (Ladder.dodgeEscape k)) ∧
    (∀ T, Geom.Profile.Alive 2 Geom.Profile.expand T) ∧
    Bridge.Alphabet.Kmin = 2 :=
  ⟨tick_identification_dichotomy.1,
   tick_identification_dichotomy.2.1,
   tick_identification_dichotomy.2.2.1,
   fun fa => ⟨(tick_identification_step fa).1,
     (tick_identification_step fa).2.1⟩,
   fun hU w => (Bridge.RegistrationFactor.registers_admits_namer hU w).1,
   rate_weld,
   naming_tick_extension,
   expand_eternally_alive,
   Bridge.Alphabet.Kmin_eq⟩

/-- Backward-compatible alias (pre-v0.2 name). -/
def tick_identification_classified := tick_identification

/-- **Time–dissipation corollary.** Fund is exempt from tick identification
    (`FundExempt`), and Fund / oscillator is vacuum dynamics
    (`¬Merges ∧ ¬Registers`). Registration (= merge) is exactly where the
    naming demand appears (`merge ⇒ record`). So undamped dynamics have no
    naming ticks, and the arrow appears exactly when registration does.

    Formal columns (spine/ledger): theorem-grade. Dictionary H=0 / damping
    rhyme remains K-certificate (T-5/T-6) by I-4 discipline. -/
theorem time_dissipation_one_property :
    FundExempt ∧
    Bridge.EffectiveMatter.VacuumDynamics Geom.Registration.oscStep ∧
    (Merges Geom.Registration.swapStep ∧
      Registers Geom.Registration.swapStep) ∧
    (∀ {S E : Type} {U : S × E → S × E},
      Inj U → Merges U → Registers U) ∧
    Bridge.Alphabet.Kmin = 2 :=
  ⟨tick_identification.1,
   Bridge.EffectiveMatter.osc_is_vacuum,
   ⟨Geom.Registration.swap_registers.2.1,
     Geom.Registration.swap_registers.2.2⟩,
   fun hU hm => Geom.Registration.merge_registers hU hm,
   Bridge.Alphabet.Kmin_eq⟩

#print axioms tick_simulation
#print axioms committed_yields_mute
#print axioms rate_weld
#print axioms committed_roundtrip_depth
#print axioms tick_simulation_fragment
#print axioms tick_identification_licensed
#print axioms tick_identification_ingredients
#print axioms tick_identification_step
#print axioms tick_identification_dichotomy
#print axioms tick_identification
#print axioms tick_identification_classified
#print axioms time_dissipation_one_property

end Bridge.TickSimulation
