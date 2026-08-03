import Obs.AbstractMemory

/-!
# Obs.AbstractThermo

Booking + SelfBlindness implies a non-injective step.
-/

namespace Obs.AbstractThermo

open Obs.AbstractMemory

/-- Step is not injective: distinct states share a successor. -/
def NonInjective {X : Type} (step : X → X) : Prop :=
  ∃ x y : X, x ≠ y ∧ step x = step y

/-- Booking + SelfBlindness ⇒ NonInjective step. -/
theorem noninjective_of_booking_selfblind
    {X Content Readout : Type}
    (M : System X)
    (bk : Booking X Content)
    (sb : SelfBlindness X Content Readout M bk) :
    NonInjective M.step := by
  rcases sb.write_unread with ⟨c₁, c₂, hne, hread⟩
  refine ⟨bk.book c₁, bk.book c₂, book_ne_of_ne bk hne, ?_⟩
  exact sb.step_factors_read (bk.book c₁) (bk.book c₂) hread

/-- Causal-record package implies non-injectivity. -/
theorem noninjective_of_causal_record
    {X Content Readout : Type}
    (C : CausalRecordSystem X Content Readout) :
    NonInjective C.system.step :=
  noninjective_of_booking_selfblind C.system C.booking C.selfBlind

/-- Read-closure: equal reads stay equal after a step. -/
theorem read_step_congruence
    {X Content Readout : Type}
    (C : CausalRecordSystem X Content Readout)
    {x y : X}
    (h : C.selfBlind.read x = C.selfBlind.read y) :
    C.selfBlind.read (C.system.step x) =
      C.selfBlind.read (C.system.step y) :=
  C.readClosure.closed x y h

/-- Reference support is nonempty (ledger domain exists). -/
theorem reference_support_nonempty
    {X Content Readout : Type}
    (C : CausalRecordSystem X Content Readout) :
    C.referenceSupport.support ≠ [] :=
  C.referenceSupport.nonempty

/-- No-demon through read: booked contents are not separated by readout.
    (`SelfBlindness.write_unread`.) -/
def NoDemonThroughRead
    {X Content Readout : Type}
    (M : System X)
    (bk : Booking X Content)
    (sb : SelfBlindness X Content Readout M bk) : Prop :=
  ∃ c₁ c₂ : Content,
    c₁ ≠ c₂ ∧ sb.read (bk.book c₁) = sb.read (bk.book c₂)

theorem no_demon_of_selfblind
    {X Content Readout : Type}
    (M : System X)
    (bk : Booking X Content)
    (sb : SelfBlindness X Content Readout M bk) :
    NoDemonThroughRead M bk sb :=
  sb.write_unread

theorem no_demon_of_causal_record
    {X Content Readout : Type}
    (C : CausalRecordSystem X Content Readout) :
    NoDemonThroughRead C.system C.booking C.selfBlind :=
  no_demon_of_selfblind C.system C.booking C.selfBlind

/-!
# Obs.AbstractThermo

Booking + SelfBlindness implies a non-injective step.
-/

/-- Deduplicated one-step image of a finite enumerated domain. -/
def listImage {X : Type} [BEq X] (step : X → X) (S : List X) : List X :=
  (S.map step).eraseDups

theorem length_eraseDups_le {X : Type} [BEq X] :
    ∀ S : List X, S.eraseDups.length ≤ S.length
  | [] => by simp [List.eraseDups]
  | a :: as => by
    simp only [List.eraseDups_cons, List.length_cons]
    have h1 := length_eraseDups_le (as.filter fun b => !b == a)
    have h2 := List.length_filter_le (fun b => !b == a) as
    exact Nat.succ_le_succ (Nat.le_trans h1 h2)
termination_by S => S.length
decreasing_by
  simp only [List.length_cons]
  exact Nat.lt_succ_of_le (List.length_filter_le _ _)

/-- One-step image never enlarges a finite support. -/
theorem listImage_length_le {X : Type} [BEq X]
    (step : X → X) (S : List X) :
    (listImage step S).length ≤ S.length := by
  simpa [listImage, List.length_map] using length_eraseDups_le (S.map step)

/-- Iterated image sizes are monotone: `|Im F^{t+1}| ≤ |Im F^t|`
    on a finite BEq-enumerated support. -/
def imageSizes {X : Type} [BEq X]
    (step : X → X) (S : List X) : Nat → List X
  | 0 => S.eraseDups
  | t + 1 => listImage step (imageSizes step S t)

theorem image_size_monotone_step {X : Type} [BEq X]
    (step : X → X) (S : List X) (t : Nat) :
    (imageSizes step S (t + 1)).length ≤ (imageSizes step S t).length := by
  simpa [imageSizes] using listImage_length_le step (imageSizes step S t)

/-- On any causal-record reference support (with BEq), image sizes are monotone. -/
theorem causal_record_image_monotone {X Content Readout : Type} [BEq X]
    (C : CausalRecordSystem X Content Readout) (t : Nat) :
    (imageSizes C.system.step C.referenceSupport.support (t + 1)).length ≤
      (imageSizes C.system.step C.referenceSupport.support t).length :=
  image_size_monotone_step C.system.step C.referenceSupport.support t

/- Logical merge cost is counted in ring/abstract_thermo.py; physical
   Landauer cost requires an erasure implementation (ring/blotter_bath.py). -/

end Obs.AbstractThermo

/- axiom footprint -/
#print axioms Obs.AbstractThermo.noninjective_of_booking_selfblind
#print axioms Obs.AbstractThermo.noninjective_of_causal_record
#print axioms Obs.AbstractThermo.no_demon_of_causal_record
#print axioms Obs.AbstractThermo.causal_record_image_monotone
#print axioms Obs.AbstractThermo.image_size_monotone_step
