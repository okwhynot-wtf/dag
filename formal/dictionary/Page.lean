import LCertificate
import Geom.Registration
import Geom.Profile
import ArchiveMustSpeak
import Alphabet

/-!
# Page toy — ledger dictionary entry (black hole information paradox)

A finite Page-style model of evaporation bookkeeping: system factor with
coarse-graining merge, radiation register `E`, injective joint step,
capacity schedule, and exhaustion tick. Continuum gravitational / QFT
black-hole physics lies outside this module.

Dictionary map:
  Unitarity of evaporation     ↔ Inj(U)
  No-hair (microstates → M…)   ↔ K-fold merge in U_S
  Exactly thermal Hawking      ↔ StreamMute sustained forever
  Bekenstein–Hawking entropy   ↔ |caps T|
  Entropy bound                ↔ aliveness
  Page time                    ↔ t_exh
  Hayden–Preskill decoding     ↔ archive recoverable on ascent

Hawking 1976 corresponds to eternal mute merging; Registration together
with T-10 is the ledger-level analogue of the unitarist reply. Admission is by
L-certificate (not the I-4 K-certificate schema). A kernel-side reading
of Hawking pairs as an involution with horizon zero-mode locus is not
claimed in this module.
-/

namespace Dictionary.Page

open Dictionary.LCertificate
open Geom.Registration

/-! ## Finite toy: system ↔ radiation swap (Registration witness)

`S = Bool` is the coarse-grained system factor (no-hair caricature after
merge); `E = Bool` is a one-qubit radiation register. `swapStep` is
injective, merges on the system slot, and writes the compensating
record into radiation — the Registration triangle in one step.
-/

/-- (a)(b)(c) witness: joint swap. -/
def U : Bool × Bool → Bool × Bool := swapStep

theorem page_inj : Inj U := swap_inj

theorem page_merges : Merges U := swap_registers.2.1

theorem page_registers : Registers U := swap_registers.2.2

/-- Counting form: |E| ≥ K with K = Kmin = 2 on this toy. -/
theorem radiation_holds_distinctions :
    Bridge.Alphabet.Kmin = 2 ∧ Registers U :=
  ⟨Bridge.Alphabet.Kmin_eq, page_registers⟩

/-! ## Capacity schedule + Page time (bounce) -/

/-- Finite BH caricature: bounce turnaround = Page / exhaustion tick. -/
def pageTime (tTurn : Nat) : Nat := tTurn

theorem page_alive (tTurn : Nat) :
    ∀ T, T ≤ tTurn → Geom.Profile.Alive 2 (Geom.Profile.bounce tTurn) T :=
  fun T hT => (Geom.Profile.bounce_alive_iff (by decide : 2 ≤ 2) tTurn T).mpr hT

theorem page_exhaustion (tTurn : Nat) :
    Geom.Profile.IsExhaustionTick 2 (Geom.Profile.bounce tTurn) tTurn :=
  Bridge.ArchiveMustSpeak.page_time_is_exhaustion (by decide : 2 ≤ 2) tTurn

/-- Page-shaped schedule: thermal window, then speech. -/
theorem page_curve (tTurn : Nat) :
    (∀ T, T ≤ tTurn → Geom.Profile.Alive 2 (Geom.Profile.bounce tTurn) T) ∧
    Geom.Profile.IsExhaustionTick 2 (Geom.Profile.bounce tTurn) tTurn :=
  Bridge.ArchiveMustSpeak.thermal_window_then_speech (by decide : 2 ≤ 2) tTurn

/-! ## L-certificate filing -/

/-- Filled L-certificate at an arbitrary finite Page time. -/
def pageCert (tTurn : Nat) : LedgerCert Bool Bool where
  U := U
  inj := page_inj
  merges := page_merges
  registers := page_registers
  K := 2
  hK := by decide
  prof := Geom.Profile.bounce tTurn
  tExh := tTurn
  alive_before := page_alive tTurn
  is_exhaustion := page_exhaustion tTurn

/-- **Admission.** Page toy files all five L-certificate clauses. -/
theorem page_admitted (tTurn : Nat) :
    let c := pageCert tTurn
    Inj c.U ∧ Merges c.U ∧ Registers c.U ∧
    c.K = 2 ∧
    (∀ T, T ≤ c.tExh → Geom.Profile.Alive c.K c.prof T) ∧
    Geom.Profile.IsExhaustionTick c.K c.prof c.tExh :=
  ⟨page_inj, page_merges, page_registers, rfl,
   page_alive tTurn, page_exhaustion tTurn⟩

/-- Mute-failure corollary is T-10 (owned by the bridge; cited here). -/
theorem archive_must_speak_cited :
    (∀ {K : Nat}, 2 ≤ K → ∀ tTurn,
      Geom.Profile.IsExhaustionTick K (Geom.Profile.bounce tTurn) tTurn) ∧
    Bridge.Alphabet.Kmin = 2 :=
  ⟨fun hK tTurn => Bridge.ArchiveMustSpeak.page_time_is_exhaustion hK tTurn,
   Bridge.Alphabet.Kmin_eq⟩

/-- Dictionary covers both lower layers: Kramers (kernel/spine fixed-
    point-freeness) pairs with Page (ledger Registration + exhaustion). -/
theorem ledger_entry_filed (tTurn : Nat) :
    Inj (pageCert tTurn).U ∧
    Registers (pageCert tTurn).U ∧
    Geom.Profile.IsExhaustionTick 2 (Geom.Profile.bounce tTurn) tTurn :=
  ⟨page_inj, page_registers, page_exhaustion tTurn⟩

#print axioms page_admitted
#print axioms page_curve
#print axioms archive_must_speak_cited
#print axioms ledger_entry_filed

end Dictionary.Page
