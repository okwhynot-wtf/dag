import Obs.Unlock
import Obs.EffectiveDynamics

/-!
# Obs.ContinuumUnlock

Unlock packages for continuum carriers; DPI ledger along induced readout maps.
-/

namespace Obs.ContinuumUnlock

open Obs.Unlock
open Obs.EffectiveDynamics

/-! ## Continuum-capable packages

  Obs.Unlock.CutRefinement / DisplacedRecovery / NotReadClosed are already
  parametric in the carrier type. Continuum unlock reuses them and records
  that the correct monotone on a continuum ambient space is mutual
  information under an induced readout channel.
-/

/-- Continuum cut refinement: same as `Obs.Unlock.CutRefinement` (any carrier). -/
abbrev ContinuumCutRefinement (X : Type) (Content : Type)
    (ReadLocked : Type) (ReadUnlocked : Type)
    (bk : Obs.AbstractMemory.Booking X Content) :=
  CutRefinement X Content ReadLocked ReadUnlocked bk

/-- Continuum displaced recovery: same as `Obs.Unlock.DisplacedRecovery`. -/
abbrev ContinuumDisplacedRecovery (X : Type) (Content : Type)
    (ReadLocked : Type) (ReadUnlocked : Type) :=
  DisplacedRecovery X Content ReadLocked ReadUnlocked

theorem continuum_refinement_unlocks
    {X Content ReadLocked ReadUnlocked : Type}
    (bk : Obs.AbstractMemory.Booking X Content)
    (U : ContinuumCutRefinement X Content ReadLocked ReadUnlocked bk) :
    (∃ c₁ c₂ : Content,
      c₁ ≠ c₂ ∧
        U.readLocked (bk.book c₁) = U.readLocked (bk.book c₂)) ∧
    (∀ c₁ c₂ : Content,
      U.readUnlocked (bk.book c₁) = U.readUnlocked (bk.book c₂) → c₁ = c₂) :=
  unlocks_at_imprint_of_refinement bk U

theorem continuum_not_write_unread_unlocked
    {X Content ReadLocked ReadUnlocked : Type}
    (bk : Obs.AbstractMemory.Booking X Content)
    (U : ContinuumCutRefinement X Content ReadLocked ReadUnlocked bk) :
    ¬ ∃ c₁ c₂ : Content,
        c₁ ≠ c₂ ∧
          U.readUnlocked (bk.book c₁) = U.readUnlocked (bk.book c₂) :=
  not_write_unread_unlocked bk U

theorem continuum_displaced_locked_merged
    {X Content ReadLocked ReadUnlocked : Type}
    (D : ContinuumDisplacedRecovery X Content ReadLocked ReadUnlocked) :
    ∃ c₁ c₂ : Content,
      c₁ ≠ c₂ ∧
        D.readLocked (D.step (D.book c₁)) =
          D.readLocked (D.step (D.book c₂)) :=
  locked_still_merged_of_displaced D

/-! ## Continuum ledger: DPI under induced readout maps

  On a continuum ambient carrier, image-counting `|Im|` is not the historical
  monotone. When an induced readout map `g` exists
  (`read ∘ step = g ∘ read`), Shannon mutual information satisfies
  `I(C₀; R_{t+1}) ≤ I(C₀; R_t)` by data processing. `ContinuumDPILedger`
  records that monotonicity abstractly.
-/

/-- Abstract DPI ledger along iterates of an induced readout map. -/
structure ContinuumDPILedger (Readout : Type) where
  /-- Mutual information I(C₀; R_t) in exact bits (finite C₀). -/
  I : Nat → Nat
  g : Readout → Readout
  /-- Data-processing monotonicity along g. -/
  dpi_monotone : ∀ t : Nat, I (t + 1) ≤ I t

/-- From an induced readout map, a DPI ledger records the continuum
    historical monotonicity law for a supplied `I`. -/
def ledger_of_induced_dpi
    {Readout : Type}
    (g : Readout → Readout)
    (I : Nat → Nat)
    (h : ∀ t : Nat, I (t + 1) ≤ I t) :
    ContinuumDPILedger Readout where
  I := I
  g := g
  dpi_monotone := h

/-- Read-closure stability still governs fixed-cut historical equality —
    continuum does not weaken Obs.Unlock.U2. -/
theorem continuum_historical_stability_requires_closure
    {X Content Readout : Type}
    (step : X → X) (read : X → Readout) (book : Content → X)
    (hc : ReadClosed step read)
    {c₁ c₂ : Content} (t : Nat)
    (h : read (iterate step t (book c₁)) =
      read (iterate step t (book c₂))) :
    read (iterate step (t + 1) (book c₁)) =
      read (iterate step (t + 1) (book c₂)) :=
  historical_stability_requires_closure step read book hc t h

/-- Broken read-closure remains incompatible with ReadClosed. -/
theorem continuum_not_both_closed
    {X Readout : Type}
    {step : X → X} {read : X → Readout}
    (hc : ReadClosed step read)
    (hn : NotReadClosed step read) : False :=
  not_both_closed hc hn

/-!
# Obs.ContinuumUnlock

Unlock packages for continuum carriers; DPI ledger along induced readout maps.
-/

/-- Continuum unlock programme: refinement + displaced duals + DPI ledger law. -/
structure ContinuumUnlockProgramme (X : Type) (Content : Type)
    (ReadLocked : Type) (ReadUnlocked : Type)
    (bk : Obs.AbstractMemory.Booking X Content) where
  refinement : ContinuumCutRefinement X Content ReadLocked ReadUnlocked bk
  displaced : ContinuumDisplacedRecovery X Content ReadLocked ReadUnlocked
  /-- Optional DPI ledger on the locked readout when an induced map exists. -/
  lockedDPI : Option (ContinuumDPILedger ReadLocked)

end Obs.ContinuumUnlock

/- audit -/
#print axioms Obs.ContinuumUnlock.continuum_refinement_unlocks
#print axioms Obs.ContinuumUnlock.continuum_not_write_unread_unlocked
#print axioms Obs.ContinuumUnlock.continuum_displaced_locked_merged
#print axioms Obs.ContinuumUnlock.continuum_historical_stability_requires_closure
#print axioms Obs.ContinuumUnlock.continuum_not_both_closed
