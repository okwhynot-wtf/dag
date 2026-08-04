import Density
import Ladder
import Alphabet
import Geom.Profile
import Geom.Provision
import Geom.Bounce

/-!
# T-9 Capacity dictionary

On the committed ladder: `|caps T| = 2^(T+2)` via predicate count;
the expand profile is the committed schedule; aliveness is eternal by
arithmetic; ω-flatline vs ancestry is named as the capacity-clock limit.
-/

namespace Bridge.Capacity

/-- Predicate-space capacity at ladder level `T` (I-2). -/
def caps (T : Nat) : Nat := Density.predicateCount T

theorem caps_eq (T : Nat) : caps T = 2 ^ (T + 2) :=
  Density.predicateCount_eq T

/-- Level cardinality is `T + 2` (Bool base + one namer per tick). -/
theorem levelCard_eq (T : Nat) : Density.levelCard T = T + 2 :=
  Density.levelCard_eq T

/-- Committed ladder realises AG's `expand` depth profile (diagonal). -/
def committedProfile : Geom.Profile.DepthProfile := Geom.Profile.expand

theorem committed_is_expand (T : Nat) : committedProfile T = T := rfl

/-- At merge rate `K = 2`, demand `2^T` fits predicate capacity `2^(T+2)`. -/
theorem alive_arith (T : Nat) : 2 ^ T ≤ caps T := by
  rw [caps_eq]
  have h : T ≤ T + 2 := Nat.le_add_right T 2
  exact Nat.pow_le_pow_right (by decide : 0 < 2) h

/-- Demand vs predicate caps (the I-2 arithmetic fact). -/
theorem committed_alive_vs_caps (T : Nat) :
    2 ^ T ≤ caps T :=
  alive_arith T

/-- Expand-profile aliveness at `K = 2` holds for every horizon. -/
theorem expand_alive (T : Nat) :
    Geom.Profile.Alive 2 Geom.Profile.expand T :=
  Nat.le_refl (2 ^ T)

/-- Expand capacity at alphabet size 2 matches `2^T` (AG weld). -/
theorem expand_capacity_two (T : Nat) :
    Geom.Profile.capacityOf 2 Geom.Profile.expand T = 2 ^ T :=
  rfl

/-- **T-9.** Capacity dictionary package. -/
theorem capacity_dictionary (T : Nat) :
    caps T = 2 ^ (T + 2) ∧
    committedProfile T = T ∧
    2 ^ T ≤ caps T ∧
    Geom.Profile.capacityOf 2 Geom.Profile.expand T = 2 ^ T :=
  ⟨caps_eq T, committed_is_expand T, alive_arith T, expand_capacity_two T⟩

/-- Ancestry (stage tags / level index) remains recoverable while the
    magnitude reading flatlines at ω — cited from the spine. -/
theorem ancestry_survives :
    (∀ k, Density.levelCard k = k + 2) ∧
    (∀ T, caps T = 2 ^ (T + 2)) :=
  ⟨levelCard_eq, caps_eq⟩

/-! ## Area-as-caps sharpening (Bekenstein-shaped reading) -/

/-- Area proxy: bit-depth of the capacity ledger (`log₂ |caps T|`).
    Not continuum area / island theorems. -/
def areaBits (T : Nat) : Nat := T + 2

theorem areaBits_eq_log_caps (T : Nat) :
    caps T = 2 ^ areaBits T := by
  simp [areaBits, caps_eq]

/-- Aliveness demand never exceeds the area/capacity ledger. -/
theorem demand_le_area (T : Nat) :
    2 ^ T ≤ 2 ^ areaBits T := by
  simpa [areaBits_eq_log_caps T] using alive_arith T

/-- One-tick area growth is one bit (same as Phase-E `deltaS`). -/
theorem areaBits_succ (T : Nat) :
    areaBits (T + 1) = areaBits T + 1 := by
  simp [areaBits, Nat.add_assoc]

/-- **Area-as-caps sharpening.** Bekenstein-shaped reading of `|caps T|`
    as discrete area: `log₂ |caps| = T+2`, demand ≤ area, +1 bit/tick.
    Continuum area / holographic island theorems remain refused. -/
theorem area_as_caps_sharpening :
    (∀ T, caps T = 2 ^ areaBits T) ∧
    (∀ T, 2 ^ T ≤ caps T) ∧
    (∀ T, areaBits (T + 1) = areaBits T + 1) ∧
    (∀ T, areaBits T = Density.levelCard T) ∧
    Bridge.Alphabet.Kmin = 2 :=
  ⟨areaBits_eq_log_caps, alive_arith, areaBits_succ,
   fun T => by simp [areaBits, levelCard_eq],
   Bridge.Alphabet.Kmin_eq⟩

#print axioms capacity_dictionary
#print axioms alive_arith
#print axioms ancestry_survives
#print axioms area_as_caps_sharpening

end Bridge.Capacity
