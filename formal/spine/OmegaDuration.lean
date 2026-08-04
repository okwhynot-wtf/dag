import Density
import Limit
import NonCommencement

/-!
# OmegaDuration — magnitude flatlines, ancestry continues

Below omega, level cardinality recovers the ladder index
(NonCommencement.ladder_index_recoverable): magnitude tracks history.
At omega the Option-extension of a countable carrier is equinumerous with
the carrier (Hilbert hotel). Magnitude flatlines. Ancestry continues
through Limit.appearsBy / stage tags. The namer at omega+1 remains outside
the image of the prior stage (Limit.omega_plus_one_grows).

Quantitative duration (size-as-clock) ends. Ancestral duration
(tagged history) continues. The arrow does not stop.
-/
namespace OmegaDuration

open Limit
open NonCommencement

/-! ## Hilbert hotel on Nat -/

/-- Shift map witnessing Option Nat bijective with Nat. -/
def optionNatToNat : Option Nat → Nat
  | none => 0
  | some n => n + 1

def natToOptionNat : Nat → Option Nat
  | 0 => none
  | n + 1 => some n

theorem optionNat_left_inv (x : Option Nat) :
    natToOptionNat (optionNatToNat x) = x := by
  cases x with
  | none => rfl
  | some n => rfl

theorem optionNat_right_inv (n : Nat) :
    optionNatToNat (natToOptionNat n) = n := by
  cases n with
  | zero => rfl
  | succ n => rfl

/-- Option Nat is equinumerous with Nat. -/
theorem optionNat_bijective :
    (∀ x y, optionNatToNat x = optionNatToNat y → x = y) ∧
    (∀ n, ∃ x, optionNatToNat x = n) :=
  ⟨fun x y h => by
      have := congrArg natToOptionNat h
      simp [optionNat_left_inv] at this
      exact this,
    fun n => ⟨natToOptionNat n, optionNat_right_inv n⟩⟩

/-! ## Hilbert hotel on LevelOmega -/

/-- Shift map witnessing Option LevelOmega bijective with LevelOmega.
    LevelOmegaPlusOne is definitionally Option LevelOmega, so this is the
    cardinality statement that the omega+1 carrier is equinumerous with
    the colimit carrier. -/
def optionOmegaToOmega : Option LevelOmega → LevelOmega
  | none => LevelOmega.base false
  | some (LevelOmega.base false) => LevelOmega.base true
  | some (LevelOmega.base true) => LevelOmega.stage 0
  | some (LevelOmega.stage k) => LevelOmega.stage (k + 1)

def omegaToOptionOmega : LevelOmega → Option LevelOmega
  | LevelOmega.base false => none
  | LevelOmega.base true => some (LevelOmega.base false)
  | LevelOmega.stage 0 => some (LevelOmega.base true)
  | LevelOmega.stage (k + 1) => some (LevelOmega.stage k)

theorem optionOmega_left_inv (x : Option LevelOmega) :
    omegaToOptionOmega (optionOmegaToOmega x) = x := by
  cases x with
  | none => rfl
  | some v =>
    cases v with
    | base b =>
      cases b with
      | false => rfl
      | true => rfl
    | stage k => rfl

theorem optionOmega_right_inv (v : LevelOmega) :
    optionOmegaToOmega (omegaToOptionOmega v) = v := by
  cases v with
  | base b =>
    cases b with
    | false => rfl
    | true => rfl
  | stage k =>
    cases k with
    | zero => rfl
    | succ k => rfl

/-- Option LevelOmega is equinumerous with LevelOmega. -/
theorem optionLevelOmega_bijective :
    (∀ x y, optionOmegaToOmega x = optionOmegaToOmega y → x = y) ∧
    (∀ v, ∃ x, optionOmegaToOmega x = v) :=
  ⟨fun x y h => by
      have := congrArg omegaToOptionOmega h
      simp [optionOmega_left_inv] at this
      exact this,
    fun v => ⟨omegaToOptionOmega v, optionOmega_right_inv v⟩⟩

/-! ## Ancestry that survives the flatline -/

/-- Stage tags remain injective: ancestry is recoverable at omega. -/
theorem stage_tag_injective (j k : Nat) :
    LevelOmega.stage j = LevelOmega.stage k → j = k :=
  Limit.stage_inj

/-- First-appearance stage of a stage-tag is one past the tag index. -/
theorem appearsBy_stage (k : Nat) :
    Limit.appearsBy (LevelOmega.stage k) = k + 1 :=
  rfl

/-- Equal first-appearance stages on stage tags recover the tag index. -/
theorem appearsBy_recovers_stage (j k : Nat) :
    Limit.appearsBy (LevelOmega.stage j) =
      Limit.appearsBy (LevelOmega.stage k) → j = k := by
  intro h
  have hj : Limit.appearsBy (LevelOmega.stage j) = j + 1 := rfl
  have hk : Limit.appearsBy (LevelOmega.stage k) = k + 1 := rfl
  have hsum : j + 1 = k + 1 := by
    rw [← hj, h, hk]
  exact Nat.succ.inj hsum

/-- The namer at omega+1 is new: outside the image of some. -/
theorem namer_new_at_omega :
    ∃ b : Limit.LevelOmegaPlusOne,
      ∀ a : LevelOmega, (some a : Limit.LevelOmegaPlusOne) ≠ b :=
  Limit.omega_plus_one_grows

/-! ## Colimit is duration, not a rung -/

/-- The ω-colimit carrier admits no injection into any finite ladder level.
    Completeness-as-colimit is therefore not a representation at a rung:
    `LevelOmega` is a duration (ancestral clock), not a level. -/
theorem omega_not_a_rung (k : Nat) :
    ¬ ∃ (f : LevelOmega → Ladder.Level k),
      ∀ x y, f x = f y → x = y := by
  intro ⟨f, hinj⟩
  let g (i : Nat) : Nat :=
    if h : i < k + 3 then Density.levelToNat k (f (LevelOmega.stage i)) else 0
  have hg : ∀ i (hi : i < k + 3),
      g i = Density.levelToNat k (f (LevelOmega.stage i)) := by
    intro i hi; exact dif_pos hi
  have hb : ∀ i, i < (k + 2) + 1 → g i < k + 2 := by
    intro i hi; rw [hg i hi]; exact Density.levelToNat_lt k _
  have hginj : ∀ i j, i < (k + 2) + 1 → j < (k + 2) + 1 → g i = g j → i = j := by
    intro i j hi hj heq
    have heq' : Density.levelToNat k (f (LevelOmega.stage i)) =
                Density.levelToNat k (f (LevelOmega.stage j)) := by
      rw [← hg i hi, ← hg j hj, heq]
    have hlev := Density.levelToNat_inj k _ _ heq'
    have hdom := hinj _ _ hlev
    exact Limit.stage_inj hdom
  exact Density.no_distinct_large (k + 2) g hb hginj

/-! ## Package -/

/--
  Package: below omega, magnitude recovers history
  (ladder_index_recoverable). At omega, Option-extension of the countable
  carriers Nat and LevelOmega is equinumerous with the carrier, so
  magnitude no longer tracks history. Stage tags / appearsBy keep
  ancestry recoverable. The namer at omega+1 remains outside the prior image.
-/
theorem omega_duration_package :
    (∀ j k, Density.levelCard j = Density.levelCard k → j = k) ∧
    ((∀ x y : Option Nat, optionNatToNat x = optionNatToNat y → x = y) ∧
      (∀ n, ∃ x, optionNatToNat x = n)) ∧
    ((∀ x y : Option LevelOmega,
        optionOmegaToOmega x = optionOmegaToOmega y → x = y) ∧
      (∀ v, ∃ x, optionOmegaToOmega x = v)) ∧
    (∀ j k, LevelOmega.stage j = LevelOmega.stage k → j = k) ∧
    (∀ j k, Limit.appearsBy (LevelOmega.stage j) =
      Limit.appearsBy (LevelOmega.stage k) → j = k) ∧
    (∃ b : Limit.LevelOmegaPlusOne,
      ∀ a : LevelOmega, (some a : Limit.LevelOmegaPlusOne) ≠ b) :=
  ⟨ladder_index_recoverable,
   optionNat_bijective,
   optionLevelOmega_bijective,
   stage_tag_injective,
   appearsBy_recovers_stage,
   namer_new_at_omega⟩

/-- Package plus the rung refusal: completeness-as-colimit is not a level. -/
theorem omega_duration_not_a_rung_package :
    (∀ j k, Density.levelCard j = Density.levelCard k → j = k) ∧
    (∃ b : Limit.LevelOmegaPlusOne,
      ∀ a : LevelOmega, (some a : Limit.LevelOmegaPlusOne) ≠ b) ∧
    (∀ k, ¬ ∃ (f : LevelOmega → Ladder.Level k),
      ∀ x y, f x = f y → x = y) :=
  ⟨ladder_index_recoverable, namer_new_at_omega, omega_not_a_rung⟩

#print axioms OmegaDuration.omega_not_a_rung
#print axioms OmegaDuration.omega_duration_package
#print axioms OmegaDuration.omega_duration_not_a_rung_package

end OmegaDuration
