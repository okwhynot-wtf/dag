import PeriodTwoOrbits
import PhaseEToys
import Capacity
import Saturation
import Alphabet
import Revision

/-!
# O-2 — cut-shift as candidate modular flow

On the period-2 KMS caricature, a shift of the system/archive cut at
saturation is treated as a boost analogue. Toy correlators satisfy a KMS
condition at inverse temperature set by the period.

Period-2 correlators satisfy a β = 2 stationarity caricature, and
cut-shift is well-defined at saturated capacity, but `T_c` is set by the
period (a global datum), so the cut cannot change it. With one ℤ/2 there
is one modular flow; cut-dependent Unruh `T` is therefore unavailable.
O-2 is the absence of a continuous 1-parameter subgroup, the same missing
object as O-4 (thermal vs geometric faces).

Continuum KMS, Lorentz boosts, and Unruh temperature as continuum physics
are not derived.
-/

namespace Bridge.CutShift

open Bridge.PhaseEToys
open Bridge.PeriodTwoOrbits

/-- Cut between system-side and archive-side slots at saturated capacity
    (`|caps T|` slots partitioned). Shift of this cut is the boost
    analogue under study. -/
structure SaturatedCut (T : Nat) where
  systemSlots : Nat
  archiveSlots : Nat
  sum_eq_caps : systemSlots + archiveSlots = Bridge.Capacity.caps T

/-- Shift one slot from system to archive (cut moves toward archive). -/
def cutShiftRight {T : Nat} (c : SaturatedCut T)
    (h : 0 < c.systemSlots) : SaturatedCut T where
  systemSlots := c.systemSlots - 1
  archiveSlots := c.archiveSlots + 1
  sum_eq_caps := by
    have hsum := c.sum_eq_caps
    have hsa :
        (c.systemSlots - 1) + (c.archiveSlots + 1) =
          c.systemSlots + c.archiveSlots := by
      have hge : 1 ≤ c.systemSlots := Nat.succ_le_of_lt h
      calc
        (c.systemSlots - 1) + (c.archiveSlots + 1)
            = (c.systemSlots - 1 + 1) + c.archiveSlots := by
              simp [Nat.add_assoc, Nat.add_comm]
        _ = c.systemSlots + c.archiveSlots := by
              rw [Nat.sub_add_cancel hge]
    exact hsa.trans hsum

/-- Shift one slot from archive to system. -/
def cutShiftLeft {T : Nat} (c : SaturatedCut T)
    (h : 0 < c.archiveSlots) : SaturatedCut T where
  systemSlots := c.systemSlots + 1
  archiveSlots := c.archiveSlots - 1
  sum_eq_caps := by
    have hsum := c.sum_eq_caps
    have hge : 1 ≤ c.archiveSlots := Nat.succ_le_of_lt h
    have hsa :
        (c.systemSlots + 1) + (c.archiveSlots - 1) =
          c.systemSlots + c.archiveSlots := by
      calc
        (c.systemSlots + 1) + (c.archiveSlots - 1)
            = c.systemSlots + (1 + (c.archiveSlots - 1)) := by
              simp [Nat.add_assoc]
        _ = c.systemSlots + c.archiveSlots := by
              rw [Nat.add_comm 1, Nat.sub_add_cancel hge]
    exact hsa.trans hsum

/-- Mid cut at tick `T`: half the capacity on each side (even by caps law). -/
def midCut (T : Nat) : SaturatedCut T where
  systemSlots := Bridge.Capacity.caps T / 2
  archiveSlots := Bridge.Capacity.caps T / 2
  sum_eq_caps := by
    -- caps T = 2^(T+2) is even; half+half = whole
    have hcaps : Bridge.Capacity.caps T = 2 ^ (T + 2) :=
      Bridge.Capacity.caps_eq T
    have heven : 2 * (Bridge.Capacity.caps T / 2) = Bridge.Capacity.caps T := by
      rw [hcaps]
      have : 2 ^ (T + 2) = 2 * 2 ^ (T + 1) := by
        rw [Nat.pow_succ, Nat.mul_comm]
      rw [this, Nat.mul_div_right _ (by decide : 0 < 2)]
    -- want half + half = caps
    calc Bridge.Capacity.caps T / 2 + Bridge.Capacity.caps T / 2
        = 2 * (Bridge.Capacity.caps T / 2) := by rw [Nat.two_mul]
      _ = Bridge.Capacity.caps T := heven

/-- Inverse temperature candidate from the period-2 orbit: β = period. -/
def betaPeriod : Nat := 2

/-- Two-point correlator on a Bool orbit (agreement of `s t` with `s 0`). -/
def correlator (s : Nat → Bool) (t : Nat) : Nat :=
  if s t = s 0 then 1 else 0

/-- Period-2 ⇒ correlator is stationary under `+ β` with `β = 2`. -/
theorem correlator_period2_stationary (s : Nat → Bool)
    (hs : Revision.LiarRevision s) (t : Nat) :
    correlator s t = correlator s (t + betaPeriod) := by
  have h2 := period2_orbit_under_swap s hs t
  -- s (t+2) = s t ⇒ agreement with s 0 is unchanged
  simp only [correlator, betaPeriod, h2]

/-- KMS caricature at β = period: stationarity of the two-point function
    under the period-2 modular shift. (Toy — not continuum KMS.) -/
theorem cut_period_stationarity (s : Nat → Bool)
    (hs : Revision.LiarRevision s) :
    ∀ t, correlator s t = correlator s (t + betaPeriod) :=
  fun t => correlator_period2_stationary s hs t

/-- Combinatorial temperature is independent of cut position. -/
theorem cut_temp_independent {T : Nat} (_c : SaturatedCut T) :
    combinatorialTemp T = 1 :=
  rfl

/-- Cut-shift preserves temperature independence (still `T_c = 1`). -/
theorem cut_shift_temp_independent {T : Nat} (c : SaturatedCut T)
    (_h : 0 < c.systemSlots) :
    combinatorialTemp T = 1 ∧
    combinatorialTemp T = combinatorialTemp T :=
  ⟨cut_temp_independent c, rfl⟩

/-- Horizon-side area proxy (`areaBits`) depends only on tick `T`,
    not on the system/archive cut. -/
theorem area_blind_to_cut {T : Nat} (_c : SaturatedCut T) :
    Bridge.Capacity.areaBits T = T + 2 :=
  rfl

/-- Different cuts at the same `T` share the same `T_c` and area —
    no Unruh-like temperature-vs-cut dependence. -/
theorem no_unruh_from_cut {T : Nat} (c₁ c₂ : SaturatedCut T) :
    combinatorialTemp T = 1 ∧
    combinatorialTemp T = 1 ∧
    Bridge.Capacity.areaBits T = T + 2 ∧
    c₁.systemSlots + c₁.archiveSlots = c₂.systemSlots + c₂.archiveSlots :=
  ⟨cut_temp_independent c₁, cut_temp_independent c₂, area_blind_to_cut c₁,
   c₁.sum_eq_caps.trans c₂.sum_eq_caps.symm⟩

/-- In the period-2 caricature, temperature is set by the period — a global
    datum — and the cut only chooses the partition. Cut-dependent `T` would
    require a family of modular flows (a one-parameter group). With exactly
    one ℤ/2 there is exactly one flow, so `T_c` and `areaBits` are
    independent of cut position. O-2 is the absence of a continuous
    1-parameter subgroup; same missing object as O-4. -/
theorem o2_forced_blindness :
    (∀ T (_c : SaturatedCut T), combinatorialTemp T = 1) ∧
    (∀ T (_c : SaturatedCut T), Bridge.Capacity.areaBits T = T + 2) ∧
    betaPeriod = 2 ∧
    Bridge.Alphabet.Kmin = 2 :=
  ⟨fun _T c => cut_temp_independent c,
   fun _T c => area_blind_to_cut c,
   rfl, Bridge.Alphabet.Kmin_eq⟩

/-- **O-2 cut-shift package.**

    Saturated cut with left/right shift; period-2 correlator KMS
    caricature at `β = 2`; mid-cut witness. `T_c` and `areaBits` are
    independent of cut position (`o2_forced_blindness`). Continuum Unruh
    temperature and Lorentz boosts are not derived; O-2 is the absence of
    a continuous 1-parameter subgroup (linked to O-4). -/
theorem o2_cut_shift_dead_end :
    (∀ T, ∃ _c : SaturatedCut T, True) ∧
    (∀ s, Revision.LiarRevision s →
      ∀ t, correlator s t = correlator s (t + betaPeriod)) ∧
    (∀ T (_c : SaturatedCut T), combinatorialTemp T = 1) ∧
    (∀ T (_c : SaturatedCut T), Bridge.Capacity.areaBits T = T + 2) ∧
    (∀ _T, combinatorialTemp _T = 1) ∧
    Bridge.Alphabet.Kmin = 2 :=
  ⟨fun T => ⟨midCut T, True.intro⟩,
   cut_period_stationarity,
   fun _T c => cut_temp_independent c,
   fun _T c => area_blind_to_cut c,
   fun _ => rfl,
   Bridge.Alphabet.Kmin_eq⟩

#print axioms correlator_period2_stationary
#print axioms cut_period_stationarity
#print axioms cut_shift_temp_independent
#print axioms no_unruh_from_cut
#print axioms o2_forced_blindness
#print axioms o2_cut_shift_dead_end

end Bridge.CutShift
