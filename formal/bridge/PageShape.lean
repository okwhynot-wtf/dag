import Alphabet
import Capacity
import ArchiveMustSpeak
import Geom.Profile

/-!
# T-10 Page flux shape

Promotes archive-must-speak from existence to a combinatorial flux curve
on a bounded archive of capacity `C`:

  occupancy(t) = min(t, C)
  stream(t)    = max(0, t − C)
  t_exh        = C + 1   (first tick with positive stream)

The classical Page tent `min(t, n − t)` is a companion shape on a finite
window. Continuum QFT / Bogoliubov are not derived.
-/

namespace Bridge.PageShape

/-- Archive occupancy under unit ingest and hard capacity `C`. -/
def occupancy (C t : Nat) : Nat := min t C

/-- Stream info after the archive is full (post-exhaustion speech). -/
def streamInfo (C t : Nat) : Nat := t - min t C

/-- Classical Page tent on a window of length `n`. -/
def pageTent (n t : Nat) : Nat := min t (n - t)

/-- Exhaustion tick: first ingest forced into the stream after a full archive. -/
def exhaustionTick (C : Nat) : Nat := C + 1

/-- Before capacity is reached, the stream stays mute. -/
theorem stream_mute_before {C t : Nat} (ht : t ≤ C) :
    streamInfo C t = 0 := by
  unfold streamInfo
  have hmin : min t C = t := Nat.min_eq_left ht
  rw [hmin, Nat.sub_self]

/-- At and after capacity, stream tracks `t - C`. -/
theorem stream_tracks_after {C t : Nat} (ht : C ≤ t) :
    streamInfo C t = t - C := by
  unfold streamInfo
  have hmin : min t C = C := Nat.min_eq_right ht
  rw [hmin]

theorem occupancy_fill {C t : Nat} (ht : t ≤ C) :
    occupancy C t = t :=
  Nat.min_eq_left ht

theorem occupancy_plateau {C t : Nat} (ht : C ≤ t) :
    occupancy C t = C :=
  Nat.min_eq_right ht

theorem succ_sub_self (C : Nat) : C + 1 - C = 1 := by
  induction C with
  | zero => rfl
  | succ C ih =>
    -- (C+1)+1 - (C+1) = C+1 - C
    simpa [Nat.succ_sub_succ] using ih

theorem exhaustion_predicted (C : Nat) :
    streamInfo C C = 0 ∧ streamInfo C (C + 1) = 1 :=
  ⟨stream_mute_before (Nat.le_refl C),
   (stream_tracks_after (Nat.le_succ C)).trans (succ_sub_self C)⟩

/-- Positive stream forces `t_exh ≤ t`. -/
theorem first_speech_bound {C t : Nat} (hspeech : 0 < streamInfo C t) :
    exhaustionTick C ≤ t := by
  unfold exhaustionTick
  by_cases ht : t ≤ C
  · have hm := stream_mute_before ht
    rw [hm] at hspeech
    exact absurd hspeech (Nat.lt_irrefl 0)
  · exact Nat.succ_le_of_lt (Nat.lt_of_not_ge ht)

/-- Page tent peaks at the midpoint of an even window `n = 2m`. -/
theorem pageTent_peak (m : Nat) :
    pageTent (2 * m) m = m := by
  unfold pageTent
  have h : 2 * m - m = m := by
    have h2 : 2 * m = m + m := Nat.two_mul m
    rw [h2, Nat.add_sub_cancel]
  rw [h]
  exact Nat.min_self m

/-- On committed K=2 expand, demand stays under caps — no Page close without a bound. -/
theorem expand_never_exhausts (T : Nat) :
    2 ^ T ≤ Bridge.Capacity.caps T :=
  Bridge.Capacity.alive_arith T

/-- Bounce Page time coincides with T-10 exhaustion (existence weld). -/
theorem bounce_page_time {K : Nat} (hK : 2 ≤ K) (tTurn : Nat) :
    Geom.Profile.IsExhaustionTick K (Geom.Profile.bounce tTurn) tTurn :=
  Bridge.ArchiveMustSpeak.page_time_is_exhaustion hK tTurn

/-- **T-10 shape package.** Mute before `C`, stream `t−C` after;
    `t_exh = C+1` predicted; Page tent peak; expand never exhausts. -/
theorem T10_page_flux_shape :
    (∀ C t, t ≤ C → streamInfo C t = 0) ∧
    (∀ C t, C ≤ t → streamInfo C t = t - C) ∧
    (∀ C, streamInfo C C = 0 ∧ streamInfo C (C + 1) = 1) ∧
    (∀ m, pageTent (2 * m) m = m) ∧
    (∀ T, 2 ^ T ≤ Bridge.Capacity.caps T) ∧
    Bridge.Alphabet.Kmin = 2 :=
  ⟨fun _ _ ht => stream_mute_before ht,
   fun _ _ ht => stream_tracks_after ht,
   exhaustion_predicted,
   pageTent_peak,
   expand_never_exhausts,
   Bridge.Alphabet.Kmin_eq⟩

#print axioms stream_mute_before
#print axioms stream_tracks_after
#print axioms exhaustion_predicted
#print axioms pageTent_peak
#print axioms T10_page_flux_shape

end Bridge.PageShape
