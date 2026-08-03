import Obs.AbstractMemory
import Obs.EffectiveDynamics
import Obs.Unlock
import Obs.UnlockCompleteness

/-!
# Obs.UnlockPricing

Access and autonomy prices for locked observation.
-/

namespace Obs.Unlock

open Obs.AbstractMemory
open Obs.EffectiveDynamics
open Obs.Unlock

/-! ## Post-processing -/

/-- The probe agrees with `h ∘ readL` on the two `t`-states of the pair:
    at horizon `t`, `readU` is (locally) post-processing of the locked
    readout. -/
def PostProcessedOnPairAt {X Content ReadLocked ReadUnlocked : Type}
    (step : X → X) (book : Content → X)
    (readL : X → ReadLocked) (readU : X → ReadUnlocked)
    (c₁ c₂ : Content) (t : Nat) (h : ReadLocked → ReadUnlocked) : Prop :=
  h (readL (iterate step t (book c₁))) = readU (iterate step t (book c₁)) ∧
  h (readL (iterate step t (book c₂))) = readU (iterate step t (book c₂))

/-! ## Access price -/

/-- **Access price.** If the locked cut merges the pair at horizon `t`
    while the probe separates it there, the probe is not post-processing
    of the locked readout at `t` — for any `h` whatsoever. Distinguishing
    power cannot be manufactured downstream of the locked cut. -/
theorem no_postprocessing_of_separating
    {X Content ReadLocked ReadUnlocked : Type}
    {step : X → X} {book : Content → X}
    {readL : X → ReadLocked} {readU : X → ReadUnlocked}
    {c₁ c₂ : Content} {t : Nat}
    (hm : MergedAt step readL book c₁ c₂ t)
    (hsep : ¬ MergedAt step readU book c₁ c₂ t) :
    ∀ h : ReadLocked → ReadUnlocked,
      ¬ PostProcessedOnPairAt step book readL readU c₁ c₂ t h :=
  fun h hpp =>
    hsep ((hpp.1.symm.trans (congrArg h hm)).trans hpp.2)

/-- A separating probe lies strictly outside the locked algebra in the
    refinement order: `readU ⋠ readL`. No global post-processing of the
    locked readout reproduces the probe, since restricting one to the
    pair's `t`-states would contradict the access price. This is the
    formal content of "genuinely new observational access". -/
theorem separating_probe_not_coarsening
    {X Content ReadLocked ReadUnlocked : Type}
    {step : X → X} {book : Content → X}
    {readL : X → ReadLocked} {readU : X → ReadUnlocked}
    {c₁ c₂ : Content} {t : Nat}
    (hm : MergedAt step readL book c₁ c₂ t)
    (hsep : ¬ MergedAt step readU book c₁ c₂ t) :
    ¬ Coarsens readU readL :=
  fun ⟨h, hh⟩ =>
    no_postprocessing_of_separating hm hsep h
      ⟨(hh (iterate step t (book c₁))).symm,
       (hh (iterate step t (book c₂))).symm⟩

/-- U1 pays access: a cut separating at imprint reads outside the locked
    algebra already at booking time. -/
theorem refinement_pays_access
    {X Content ReadLocked ReadUnlocked : Type}
    {step : X → X} {book : Content → X}
    {readL : X → ReadLocked} {readU : X → ReadUnlocked}
    {c₁ c₂ : Content}
    (hpair : PairCutReplacement step book readL readU c₁ c₂) :
    ∀ h : ReadLocked → ReadUnlocked,
      ¬ PostProcessedOnPairAt step book readL readU c₁ c₂ 0 h :=
  no_postprocessing_of_separating hpair.1 hpair.2

/-- U3 pays access: displaced recovery reads a sector outside the locked
    algebra at the recovery horizon. -/
theorem displacement_pays_access
    {X Content ReadLocked ReadUnlocked : Type}
    {step : X → X} {book : Content → X}
    {readL : X → ReadLocked} {readU : X → ReadUnlocked}
    {c₁ c₂ : Content} {t : Nat}
    (hd : PairDisplacedRecovery step book readL readU c₁ c₂ t) :
    ∀ h : ReadLocked → ReadUnlocked,
      ¬ PostProcessedOnPairAt step book readL readU c₁ c₂ t h :=
  no_postprocessing_of_separating hd.1 hd.2

/-! ## Autonomy price -/

/-- **Autonomy price.** Broken read-closure means no induced readout map
    exists: there is no `g : R → R` with `read ∘ step = g ∘ read`, so the
    readout process is not a self-contained dynamical system and the
    historical monotonicity guarantee is forfeit. -/
theorem broken_closure_pays_autonomy
    {X Readout : Type} {step : X → X} {read : X → Readout}
    (hn : NotReadClosed step read) :
    ¬ Nonempty (InducedReadoutMap X Readout step read) :=
  fun ⟨ind⟩ => not_both_closed (readClosed_of_induced ind) hn

/-!
# Obs.UnlockPricing

Access and autonomy prices for locked observation.
-/

/-- **No free unlock (access or autonomy).** Every unlock witness pays:
    either the probe cut is not post-processing of the locked readout at
    the witness horizon (new access — the U1/U3 doors), or read-closure
    broke and no induced readout dynamics exists for the locked cut
    (lost autonomy — the U2 door). -/
theorem access_or_autonomy
    {X Content ReadLocked ReadUnlocked : Type} [DecidableEq ReadLocked]
    (step : X → X) (book : Content → X)
    (readL : X → ReadLocked) (readU : X → ReadUnlocked)
    {c₁ c₂ : Content}
    (hlock : MergedAt step readL book c₁ c₂ 0)
    (t : Nat) (hsep : ¬ MergedAt step readU book c₁ c₂ t) :
    (∀ h : ReadLocked → ReadUnlocked,
        ¬ PostProcessedOnPairAt step book readL readU c₁ c₂ t h)
    ∨ ¬ Nonempty (InducedReadoutMap X ReadLocked step readL) :=
  if hm : MergedAt step readL book c₁ c₂ t then
    Or.inl (no_postprocessing_of_separating hm hsep)
  else
    match crossing_of_merge_break step readL book t hlock hm with
    | ⟨s, _, hms, hns⟩ =>
      Or.inr (broken_closure_pays_autonomy
        ⟨iterate step s (book c₁), iterate step s (book c₂), hms, hns⟩)

end Obs.Unlock

/- axiom footprint -/
#print axioms Obs.Unlock.no_postprocessing_of_separating
#print axioms Obs.Unlock.separating_probe_not_coarsening
#print axioms Obs.Unlock.refinement_pays_access
#print axioms Obs.Unlock.displacement_pays_access
#print axioms Obs.Unlock.broken_closure_pays_autonomy
#print axioms Obs.Unlock.access_or_autonomy
