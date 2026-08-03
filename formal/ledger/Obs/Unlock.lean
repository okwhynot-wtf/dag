import Obs.AbstractMemory
import Obs.EffectiveDynamics

/-!
# Obs.Unlock

Unlock trichotomy: cut refinement, displaced recovery, read-closure failure.
-/

namespace Obs.Unlock

open Obs.AbstractMemory
open Obs.EffectiveDynamics

/-! ## Cut refinement

  A finer readout that separates booked contents unlocked at imprint.
-/

/-- Finer cut: locked write-unread, unlocked write-unread fails. -/
structure CutRefinement (X : Type) (Content : Type)
    (ReadLocked : Type) (ReadUnlocked : Type)
    (bk : Booking X Content) where
  readLocked : X → ReadLocked
  readUnlocked : X → ReadUnlocked
  locked_write_unread :
    ∃ c₁ c₂ : Content,
      c₁ ≠ c₂ ∧
        readLocked (bk.book c₁) = readLocked (bk.book c₂)
  unlocked_separates :
    ∀ c₁ c₂ : Content,
      readUnlocked (bk.book c₁) = readUnlocked (bk.book c₂) → c₁ = c₂

/-- Refinement unlocks at imprint: locked unread, unlocked injective on books. -/
theorem unlocks_at_imprint_of_refinement
    {X Content ReadLocked ReadUnlocked : Type}
    (bk : Booking X Content)
    (U : CutRefinement X Content ReadLocked ReadUnlocked bk) :
    (∃ c₁ c₂ : Content,
      c₁ ≠ c₂ ∧
        U.readLocked (bk.book c₁) = U.readLocked (bk.book c₂)) ∧
    (∀ c₁ c₂ : Content,
      U.readUnlocked (bk.book c₁) = U.readUnlocked (bk.book c₂) → c₁ = c₂) :=
  ⟨U.locked_write_unread, U.unlocked_separates⟩

/-- Unlocked cut is not write-unread on the booking. -/
theorem not_write_unread_unlocked
    {X Content ReadLocked ReadUnlocked : Type}
    (bk : Booking X Content)
    (U : CutRefinement X Content ReadLocked ReadUnlocked bk) :
    ¬ ∃ c₁ c₂ : Content,
        c₁ ≠ c₂ ∧
          U.readUnlocked (bk.book c₁) = U.readUnlocked (bk.book c₂) := by
  intro h
  rcases h with ⟨c₁, c₂, hne, heq⟩
  exact hne (U.unlocked_separates c₁ c₂ heq)

/-! ## Broken read-closure

  Without ReadClosed, equal historical reads need not stay equal —
  the stability lemma of EffectiveDynamics fails in the converse direction.
-/

/-- Witness that read-closure fails for some pair. -/
def NotReadClosed {X Readout : Type}
    (step : X → X) (read : X → Readout) : Prop :=
  ∃ x y : X, read x = read y ∧ read (step x) ≠ read (step y)

/-- ReadClosed and NotReadClosed are incompatible. -/
theorem not_both_closed
    {X Readout : Type}
    {step : X → X} {read : X → Readout}
    (hc : ReadClosed step read)
    (hn : NotReadClosed step read) : False := by
  rcases hn with ⟨x, y, hread, hne⟩
  exact hne (hc x y hread)

/-- If historical reads coincide at 	 and closure holds, they coincide at 	+1.
    Contrapositively: growth of historical separation requires ¬ReadClosed
    (or a change of cut — handled by CutRefinement). -/
theorem historical_stability_requires_closure
    {X Content Readout : Type}
    (step : X → X) (read : X → Readout) (book : Content → X)
    (hc : ReadClosed step read)
    {c₁ c₂ : Content} (t : Nat)
    (h : read (iterate step t (book c₁)) =
      read (iterate step t (book c₂))) :
    read (iterate step (t + 1) (book c₁)) =
      read (iterate step (t + 1) (book c₂)) :=
  historical_reads_stable step read book hc t h

/-!
# Obs.Unlock

Unlock trichotomy: cut refinement, displaced recovery, read-closure failure.
-/

/-- After one step, locked reads of bookings merge; unlocked reads separate. -/
structure DisplacedRecovery (X : Type) (Content : Type)
    (ReadLocked : Type) (ReadUnlocked : Type) where
  book : Content → X
  step : X → X
  readLocked : X → ReadLocked
  readUnlocked : X → ReadUnlocked
  book_injective : ∀ c₁ c₂ : Content, book c₁ = book c₂ → c₁ = c₂
  nontrivial : ∃ c₁ c₂ : Content, c₁ ≠ c₂
  post_locked_merged :
    ∃ c₁ c₂ : Content,
      c₁ ≠ c₂ ∧
        readLocked (step (book c₁)) = readLocked (step (book c₂))
  post_unlocked_separates :
    ∀ c₁ c₂ : Content,
      readUnlocked (step (book c₁)) = readUnlocked (step (book c₂)) →
        c₁ = c₂

/-- Displaced recovery does not restore separation on the locked cut. -/
theorem locked_still_merged_of_displaced
    {X Content ReadLocked ReadUnlocked : Type}
    (D : DisplacedRecovery X Content ReadLocked ReadUnlocked) :
    ∃ c₁ c₂ : Content,
      c₁ ≠ c₂ ∧
        D.readLocked (D.step (D.book c₁)) =
          D.readLocked (D.step (D.book c₂)) :=
  D.post_locked_merged

/-- Unlocked extended readout separates post-step bookings. -/
theorem unlocked_separates_post_of_displaced
    {X Content ReadLocked ReadUnlocked : Type}
    (D : DisplacedRecovery X Content ReadLocked ReadUnlocked) :
    ∀ c₁ c₂ : Content,
      D.readUnlocked (D.step (D.book c₁)) =
          D.readUnlocked (D.step (D.book c₂)) →
        c₁ = c₂ :=
  D.post_unlocked_separates

end Obs.Unlock

/- axiom footprint -/
#print axioms Obs.Unlock.unlocks_at_imprint_of_refinement
#print axioms Obs.Unlock.not_write_unread_unlocked
#print axioms Obs.Unlock.not_both_closed
#print axioms Obs.Unlock.historical_stability_requires_closure
#print axioms Obs.Unlock.locked_still_merged_of_displaced
#print axioms Obs.Unlock.unlocked_separates_post_of_displaced
