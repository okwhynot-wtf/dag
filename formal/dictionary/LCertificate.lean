import Geom.Registration
import Geom.Profile
import Geom.Bounce
import ArchiveMustSpeak
import Alphabet

/-!
# L-certificate — ledger admission route

I-4 / KernelCert admits kernel instantiations (involution, negation
observable, fixed locus, forced +1). Ledger-layer physical instantiations
use a separate admission schema.

An L-certificate admits a model that exhibits, on a finite toy:
  (a) a bijective / injective joint step `U`;
  (b) an identified system-side merge;
  (c) the compensating environment record;
  (d) a capacity schedule with its aliveness bound;
  (e) an exhaustion tick with the mute-failure corollary (T-10).

The Page toy files all five. Continuum gravitational / QFT black-hole
physics lies outside this module; the toy is finite-dimensional and
constructive.
-/

namespace Dictionary.LCertificate

/-- Ledger-side certificate: Registration + capacity/exhaustion package. -/
structure LedgerCert (S E : Type) where
  /-- (a) joint microstep -/
  U : S × E → S × E
  inj : Geom.Registration.Inj U
  /-- (b) system-side merge -/
  merges : Geom.Registration.Merges U
  /-- (c) compensating record (Registration forces this from (a)+(b)) -/
  registers : Geom.Registration.Registers U
  /-- (d) merge rate and capacity profile -/
  K : Nat
  hK : 2 ≤ K
  prof : Geom.Profile.DepthProfile
  /-- (e) exhaustion / Page tick -/
  tExh : Nat
  alive_before : ∀ T, T ≤ tExh → Geom.Profile.Alive K prof T
  is_exhaustion : Geom.Profile.IsExhaustionTick K prof tExh

/-- Registration clause: (a)+(b) ⇒ (c) is free from T-4 / AG. -/
theorem registers_of_merge {S E : Type} (U : S × E → S × E)
    (hU : Geom.Registration.Inj U) (hm : Geom.Registration.Merges U) :
    Geom.Registration.Registers U :=
  Geom.Registration.merge_registers hU hm

/-- Bounce schedule realises (d)+(e) at any turnaround (Page time). -/
def bounceSchedule {K : Nat} (hK : 2 ≤ K) (tTurn : Nat) :
    (∀ T, T ≤ tTurn → Geom.Profile.Alive K (Geom.Profile.bounce tTurn) T) ∧
    Geom.Profile.IsExhaustionTick K (Geom.Profile.bounce tTurn) tTurn :=
  Bridge.ArchiveMustSpeak.thermal_window_then_speech hK tTurn

/-- Minimal alphabet is available to every L-certificate. -/
theorem K_at_least_Kmin {K : Nat} (hK : 2 ≤ K) :
    Bridge.Alphabet.Kmin ≤ K := by
  rw [Bridge.Alphabet.Kmin_eq]; exact hK

#print axioms registers_of_merge
#print axioms bounceSchedule

end Dictionary.LCertificate
