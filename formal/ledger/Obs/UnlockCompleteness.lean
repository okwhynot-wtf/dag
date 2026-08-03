import Obs.AbstractMemory
import Obs.EffectiveDynamics
import Obs.Unlock

/-!
# Obs.UnlockCompleteness

Completeness packaging for the unlock trichotomy.
-/

namespace Obs.Unlock

open Obs.AbstractMemory
open Obs.EffectiveDynamics

/-! ## Historical merge at a horizon -/

/-- Historical merge at time `t`: the two booked contents read equal under
    `read` after `t` steps. `MergedAt … 0` is pairwise write-unread. -/
abbrev MergedAt {X Content Readout : Type}
    (step : X → X) (read : X → Readout) (book : Content → X)
    (c₁ c₂ : Content) (t : Nat) : Prop :=
  read (iterate step t (book c₁)) = read (iterate step t (book c₂))

/-! ## Pairwise unlock structures

  Pair forms of the bundled `CutRefinement` / `DisplacedRecovery`
  (those are the ∀-content, one-step specializations). -/

/-- U1 (pair form): locked cut merges the pair at imprint; the replacement
    cut separates it there. -/
def PairCutReplacement {X Content ReadLocked ReadUnlocked : Type}
    (step : X → X) (book : Content → X)
    (readL : X → ReadLocked) (readU : X → ReadUnlocked)
    (c₁ c₂ : Content) : Prop :=
  MergedAt step readL book c₁ c₂ 0 ∧ ¬ MergedAt step readU book c₁ c₂ 0

/-- U3 (pair form, horizon `t`): locked cut merged at `t` while the
    extended cut separates at `t`. -/
def PairDisplacedRecovery {X Content ReadLocked ReadUnlocked : Type}
    (step : X → X) (book : Content → X)
    (readL : X → ReadLocked) (readU : X → ReadUnlocked)
    (c₁ c₂ : Content) (t : Nat) : Prop :=
  MergedAt step readL book c₁ c₂ t ∧ ¬ MergedAt step readU book c₁ c₂ t

/-- U1 is U3 at horizon zero: cut replacement at imprint is displaced
    recovery with no elapsed dynamics. The distinction is temporal, not
    structural. -/
theorem cut_replacement_is_displaced_at_zero
    {X Content ReadLocked ReadUnlocked : Type}
    (step : X → X) (book : Content → X)
    (readL : X → ReadLocked) (readU : X → ReadUnlocked)
    (c₁ c₂ : Content) :
    PairCutReplacement step book readL readU c₁ c₂ =
      PairDisplacedRecovery step book readL readU c₁ c₂ 0 :=
  rfl

/-! ## Soundness dual: a closed cut stays merged forever

  The iterated form of `historical_reads_stable` — the "locked forever"
  statement. The trichotomy below is its completeness dual: these are
  the only doors out. -/

/-- Under read-closure, a pair merged at imprint stays merged at every
    horizon. Same-cut unlock at any time therefore requires ¬ReadClosed. -/
theorem merged_forever_of_readClosed
    {X Content Readout : Type}
    (step : X → X) (read : X → Readout) (book : Content → X)
    (hc : ReadClosed step read)
    {c₁ c₂ : Content}
    (h0 : MergedAt step read book c₁ c₂ 0) :
    ∀ t : Nat, MergedAt step read book c₁ c₂ t
  | 0 => h0
  | t + 1 => hc _ _ (merged_forever_of_readClosed step read book hc h0 t)

/-! ## First crossing

  Merged at imprint, separated at `t`: the merge breaks at an extractable
  step. Discrete intermediate value along the orbit; decidable readout
  equality keeps it choice-free. -/

/-- If a pair is merged at 0 and separated at `t`, there is a step `s < t`
    at which the merge breaks: merged at `s`, separated at `s + 1`. -/
theorem crossing_of_merge_break
    {X Content Readout : Type} [DecidableEq Readout]
    (step : X → X) (read : X → Readout) (book : Content → X)
    {c₁ c₂ : Content} :
    ∀ t : Nat,
      MergedAt step read book c₁ c₂ 0 →
      ¬ MergedAt step read book c₁ c₂ t →
      ∃ s : Nat, s < t ∧ MergedAt step read book c₁ c₂ s ∧
        ¬ MergedAt step read book c₁ c₂ (s + 1)
  | 0, h0, hnot => absurd h0 hnot
  | t + 1, h0, hnot =>
    if hm : MergedAt step read book c₁ c₂ t then
      ⟨t, Nat.lt_succ_self t, hm, hnot⟩
    else
      match crossing_of_merge_break step read book t h0 hm with
      | ⟨s, hs, hms, hns⟩ =>
        ⟨s, Nat.lt_trans hs (Nat.lt_succ_self t), hms, hns⟩

/-! ## The trichotomy -/

/-- **Unlock completeness (trichotomy).** Let `(c₁, c₂)` be locked at
    imprint under `readL`, and let `(readU, t)` be any unlock witness —
    any probe cut separating the pair at any time. Then exactly one of:

    * **U1** — `t = 0`: pairwise cut replacement at imprint;
    * **U2** — `t > 0` and the locked cut also separates at `t`:
      read-closure broke (`NotReadClosed`, witness extracted at the
      first crossing);
    * **U3** — `t > 0` and the locked cut is still merged at `t`:
      pairwise displaced recovery at horizon `t`.

    The labels partition witnesses: U1 vs U2/U3 by the time, U2 vs U3 by
    the locked cut's status at `t`. There is no fourth witness form
    within this interface (readout-side operations, `(X, step, book)`
    fixed). (Exactness is per witness: a configuration may admit
    witnesses of several types.) -/
theorem unlock_trichotomy
    {X Content ReadLocked ReadUnlocked : Type} [DecidableEq ReadLocked]
    (step : X → X) (book : Content → X)
    (readL : X → ReadLocked) (readU : X → ReadUnlocked)
    {c₁ c₂ : Content}
    (hlock : MergedAt step readL book c₁ c₂ 0) :
    ∀ t : Nat, ¬ MergedAt step readU book c₁ c₂ t →
      (t = 0 ∧ PairCutReplacement step book readL readU c₁ c₂)
      ∨ (0 < t ∧ ¬ MergedAt step readL book c₁ c₂ t ∧
          NotReadClosed step readL)
      ∨ (0 < t ∧ PairDisplacedRecovery step book readL readU c₁ c₂ t)
  | 0, hsep => Or.inl ⟨rfl, hlock, hsep⟩
  | t + 1, hsep =>
    if hm : MergedAt step readL book c₁ c₂ (t + 1) then
      Or.inr (Or.inr ⟨Nat.succ_pos t, hm, hsep⟩)
    else
      match crossing_of_merge_break step readL book (t + 1) hlock hm with
      | ⟨s, _, hms, hns⟩ =>
        Or.inr (Or.inl ⟨Nat.succ_pos t, hm,
          ⟨iterate step s (book c₁), iterate step s (book c₂), hms, hns⟩⟩)

/-! ## Exclusivity of the labels -/

/-- U1 excludes U2/U3: a witness cannot be at imprint and later. -/
theorem labels_exclusive_time {t : Nat} (h0 : t = 0) (ht : 0 < t) : False :=
  Nat.lt_irrefl 0 (h0 ▸ ht)

/-- U2 excludes U3: the locked cut cannot be both separated and merged
    at the witness time. -/
theorem labels_exclusive_broken_displaced
    {X Content Readout : Type}
    {step : X → X} {read : X → Readout} {book : Content → X}
    {c₁ c₂ : Content} {t : Nat}
    (hnot : ¬ MergedAt step read book c₁ c₂ t)
    (hm : MergedAt step read book c₁ c₂ t) : False :=
  hnot hm

/-! ## Normal form: the joint cut

  Every witness is carried by a refinement of the locked cut — pair the
  locked readout with the probe. Unlock never needs an alien cut: keep
  everything you could read and add probes. -/

/-- Joint cut: locked readout paired with the probe. -/
def jointCut {X ReadLocked ReadUnlocked : Type}
    (readL : X → ReadLocked) (readU : X → ReadUnlocked) :
    X → ReadLocked × ReadUnlocked :=
  fun x => (readL x, readU x)

/-- The joint cut refines the locked cut: it factors through the first
    projection, so nothing readable is lost. -/
theorem jointCut_refines_locked
    {X ReadLocked ReadUnlocked : Type}
    (readL : X → ReadLocked) (readU : X → ReadUnlocked) :
    ∀ x y : X, jointCut readL readU x = jointCut readL readU y →
      readL x = readL y :=
  fun _ _ h => congrArg Prod.fst h

/-- The joint cut carries every witness: wherever the probe separates the
    pair, so does the joint cut. -/
theorem jointCut_separates
    {X Content ReadLocked ReadUnlocked : Type}
    (step : X → X) (book : Content → X)
    (readL : X → ReadLocked) (readU : X → ReadUnlocked)
    {c₁ c₂ : Content} {t : Nat}
    (hsep : ¬ MergedAt step readU book c₁ c₂ t) :
    ¬ MergedAt step (jointCut readL readU) book c₁ c₂ t :=
  fun h => hsep (congrArg Prod.snd h)

/-!
# Obs.UnlockCompleteness

Completeness packaging for the unlock trichotomy.
-/

/-- `r₁` is a coarsening of `r₂`: `r₁ = h ∘ r₂` for some `h`. -/
def Coarsens {X R₁ R₂ : Type} (r₁ : X → R₁) (r₂ : X → R₂) : Prop :=
  ∃ h : R₂ → R₁, ∀ x : X, r₁ x = h (r₂ x)

theorem coarsens_refl {X R : Type} (r : X → R) : Coarsens r r :=
  ⟨id, fun _ => rfl⟩

theorem coarsens_trans {X R₁ R₂ R₃ : Type}
    {r₁ : X → R₁} {r₂ : X → R₂} {r₃ : X → R₃}
    (h₁₂ : Coarsens r₁ r₂) (h₂₃ : Coarsens r₂ r₃) : Coarsens r₁ r₃ :=
  match h₁₂, h₂₃ with
  | ⟨h, hh⟩, ⟨k, hk⟩ =>
    ⟨fun r => h (k r), fun x => (hh x).trans (congrArg h (hk x))⟩

/-- The locked cut is a coarsening of the joint cut: refining by a probe
    loses nothing readable. -/
theorem locked_coarsens_jointCut {X ReadLocked ReadUnlocked : Type}
    (readL : X → ReadLocked) (readU : X → ReadUnlocked) :
    Coarsens readL (jointCut readL readU) :=
  ⟨Prod.fst, fun _ => rfl⟩

/-- The probe is a coarsening of the joint cut. -/
theorem probe_coarsens_jointCut {X ReadLocked ReadUnlocked : Type}
    (readL : X → ReadLocked) (readU : X → ReadUnlocked) :
    Coarsens readU (jointCut readL readU) :=
  ⟨Prod.snd, fun _ => rfl⟩

/-- **Refinement normal form.** Every unlock witness is carried by a
    refinement of the locked cut: the joint cut lies above `readL` in
    the refinement order and separates the pair wherever the probe does.
    An unlock never requires abandoning the locked cut for an alien
    one. -/
theorem unlock_refinement_normal_form
    {X Content ReadLocked ReadUnlocked : Type}
    (step : X → X) (book : Content → X)
    (readL : X → ReadLocked) (readU : X → ReadUnlocked)
    {c₁ c₂ : Content} {t : Nat}
    (hsep : ¬ MergedAt step readU book c₁ c₂ t) :
    Coarsens readL (jointCut readL readU) ∧
      ¬ MergedAt step (jointCut readL readU) book c₁ c₂ t :=
  ⟨locked_coarsens_jointCut readL readU,
   jointCut_separates step book readL readU hsep⟩

end Obs.Unlock

/- axiom footprint -/
#print axioms Obs.Unlock.cut_replacement_is_displaced_at_zero
#print axioms Obs.Unlock.merged_forever_of_readClosed
#print axioms Obs.Unlock.crossing_of_merge_break
#print axioms Obs.Unlock.unlock_trichotomy
#print axioms Obs.Unlock.labels_exclusive_time
#print axioms Obs.Unlock.labels_exclusive_broken_displaced
#print axioms Obs.Unlock.jointCut_refines_locked
#print axioms Obs.Unlock.jointCut_separates
#print axioms Obs.Unlock.coarsens_refl
#print axioms Obs.Unlock.coarsens_trans
#print axioms Obs.Unlock.locked_coarsens_jointCut
#print axioms Obs.Unlock.probe_coarsens_jointCut
#print axioms Obs.Unlock.unlock_refinement_normal_form
