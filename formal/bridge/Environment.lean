import Density
import Ladder
import Tower
import Alphabet
import Capacity
import Geom.Registration
import Geom.Ledger

/-!
# T-1 Environment universality

Define record-labels as the universal completion of a merge fiber:
`Bool` (≃ `Fin 2`) injects into the outgoing environment of any injective
2-merge. Existence via AG swap; ladder implements `E(T)` with
`|caps T| = 2^(T+2)`. Alphabet bound `|E| ≥ K` is the first corollary
(at `Kmin = 2`).

Keystone progress: `Bridge.Dil` lands free-archive initiality, the
capacity step law, registration-from-joint-inj, and the minimal K=2
schedule realised by `|caps T|`. Uniform-fiber rigidity and graded
terminality (full I-2 discharge) remain open — see `docs/RESIDUE.md`.
-/

namespace Bridge.Environment

open Geom.Registration

/-- Environment at horizon `T`: the DM ladder carrier (I-2). -/
def E (T : Nat) : Type := Ladder.Level T

/-- Cap slots at `T` are counted by the predicate space. -/
def capCount (T : Nat) : Nat := Bridge.Capacity.caps T

theorem capCount_eq (T : Nat) : capCount T = 2 ^ (T + 2) :=
  Bridge.Capacity.caps_eq T

theorem env_card (T : Nat) : Density.levelCard T = T + 2 :=
  Density.levelCard_eq T

theorem env_ge_Kmin :
    Bridge.Alphabet.Kmin = 2 ∧
    (∀ T, Bridge.Alphabet.Kmin ≤ capCount T) := by
  refine ⟨rfl, ?_⟩
  intro T
  rw [capCount_eq]
  have hpos : 0 < 2 := by decide
  have hle : 1 ≤ T + 2 := Nat.succ_le_succ (Nat.zero_le (T + 1))
  exact Nat.pow_le_pow_right hpos hle

theorem env_exists (T : Nat) : Nonempty (E T) := by
  match T with
  | 0 => exact ⟨true⟩
  | _n + 1 => exact ⟨none⟩

/-! ## Universal property of 2-merge record labels -/

/-- A witnessed 2-fold system merge under joint step `U`. -/
structure TwoMerge (S E : Type) (U : S × E → S × E) where
  a : S × E
  b : S × E
  ne : a ≠ b
  sysEq : (U a).1 = (U b).1

/-- Record-label map: the two outgoing environment letters. -/
def recordLabel {S E : Type} {U : S × E → S × E}
    (w : TwoMerge S E U) : Bool → E
  | true => (U w.a).2
  | false => (U w.b).2

/-- **UP (injectivity).** Under `Inj U`, record labels are distinct —
    `Bool` injects into `E` along the merge fiber. -/
theorem recordLabel_injective {S E : Type} {U : S × E → S × E}
    (hU : Inj U) (w : TwoMerge S E U) :
    ∀ i j : Bool, recordLabel w i = recordLabel w j → i = j := by
  intro i j h
  have hrec : (U w.a).2 ≠ (U w.b).2 :=
    Geom.Ledger.merge_registers_is_ledger_pair hU w.ne w.sysEq
  cases i <;> cases j
  · rfl
  · exact absurd h.symm hrec
  · exact absurd h hrec
  · rfl

/-- Two-element carriers are unique up to unique Bool-coordinates
    (arena-style uniqueness for the minimal alphabet). -/
def boolCoord {α : Type} (x y : α) : Bool → α
  | true => x
  | false => y

theorem boolCoord_inj {α : Type} (x y : α) (hxy : x ≠ y) :
    ∀ b b' : Bool, boolCoord x y b = boolCoord x y b' → b = b' := by
  intro b b' h
  cases b with
  | true =>
    cases b' with
    | true => rfl
    | false => exact (hxy h).elim
  | false =>
    cases b' with
    | true => exact (hxy h.symm).elim
    | false => rfl

theorem boolCoord_surj {α : Type} (x y : α)
    (hall : ∀ z : α, z = x ∨ z = y) :
    ∀ z : α, ∃ b : Bool, boolCoord x y b = z := by
  intro z
  match hall z with
  | Or.inl hx => exact ⟨true, hx.symm⟩
  | Or.inr hy => exact ⟨false, hy.symm⟩

theorem two_carrier_reads_as_bool {α : Type}
    (x y : α) (hxy : x ≠ y) (hall : ∀ z : α, z = x ∨ z = y) :
    ∃ f : Bool → α,
      (∀ b b', f b = f b' → b = b') ∧
      (∀ z, ∃ b, f b = z) ∧
      f true = x ∧ f false = y :=
  ⟨boolCoord x y, boolCoord_inj x y hxy, boolCoord_surj x y hall, rfl, rfl⟩
/-- Any injective 2-merge yields a `TwoMerge` witness. -/
theorem merges_yields_twoMerge {S E : Type} {U : S × E → S × E}
    (hm : Merges U) : ∃ _w : TwoMerge S E U, True := by
  obtain ⟨a, b, hab, hsys⟩ := hm
  exact ⟨⟨a, b, hab, hsys⟩, True.intro⟩

/-- **Existence.** Swap is a 2-completion: injective, merges, registers. -/
def swapWitness : TwoMerge Bool Bool swapStep where
  a := (false, true)
  b := (true, true)
  ne := by decide
  sysEq := rfl

theorem swap_is_completion :
    Inj swapStep ∧ Merges swapStep ∧ Registers swapStep ∧
    (∀ i j : Bool, recordLabel swapWitness i = recordLabel swapWitness j →
      i = j) :=
  ⟨swap_inj, swap_registers.2.1, swap_registers.2.2,
   recordLabel_injective swap_inj swapWitness⟩

/-- Minimal alphabet size is exactly `Kmin` on the Fundamental. -/
theorem minimal_alphabet_is_Kmin :
    Bridge.Alphabet.Kmin = 2 ∧
    (∀ n : Nat, ∀ act : Fin n → Fin n,
      Canon.IsFundamental act → n = Bridge.Alphabet.Kmin) :=
  ⟨rfl, Bridge.Alphabet.fundamentals_only_at_two⟩

/-- **Corollary.** Ledger counting: record pair distinct under Inj. -/
theorem alphabet_ge_two {S E : Type} {U : S × E → S × E}
    (hU : Inj U) (w : TwoMerge S E U) :
    (U w.a).2 ≠ (U w.b).2 :=
  Geom.Ledger.merge_registers_is_ledger_pair hU w.ne w.sysEq

/-- Ladder environment grows a fresh namer each tick (forced +1). -/
theorem ladder_strict_growth (k : Nat) :
    ∃ b : E (k + 1), ∀ a : E k, (some a : E (k + 1)) ≠ b :=
  Ladder.ladder_grows k

/-- **T-1.** Environment universality package (fiber-tagging UP):
    (i) record labels inject `Bool` into `E`;
    (ii) swap exists as completion;
    (iii) two-carriers read as Bool;
    (iv) ladder implements `E(T)` with `|caps T| = 2^(T+2)`;
    (v) `|record pair| = 2` lower-bounds the alphabet. -/
theorem environment_universality :
    (∀ {S E : Type} {U : S × E → S × E},
      Inj U → ∀ w : TwoMerge S E U,
        ∀ i j, recordLabel w i = recordLabel w j → i = j) ∧
    (Inj swapStep ∧ Merges swapStep ∧ Registers swapStep) ∧
    (∀ T, capCount T = 2 ^ (T + 2)) ∧
    (∀ T, Nonempty (E T)) ∧
    (∀ k, ∃ b : E (k + 1), ∀ a : E k, (some a : E (k + 1)) ≠ b) ∧
    Bridge.Alphabet.Kmin = 2 :=
  ⟨fun hU w => recordLabel_injective hU w,
   ⟨swap_inj, swap_registers.2.1, swap_registers.2.2⟩,
   capCount_eq, env_exists, ladder_strict_growth,
   Bridge.Alphabet.Kmin_eq⟩

/-- Backward-compatible name for the earlier fragment. -/
theorem environment_universality_fragment :
    (∀ T, capCount T = 2 ^ (T + 2)) ∧
    (∀ T, Nonempty (E T)) ∧
    Bridge.Alphabet.Kmin = 2 ∧
    (∀ T, Bridge.Alphabet.Kmin ≤ capCount T) :=
  ⟨capCount_eq, env_exists, env_ge_Kmin.1, env_ge_Kmin.2⟩

/-- Obstruction marker: UP for arbitrary `U_S` shapes beyond fiber tagging.
    Partial discharge: see `Bridge.Dil.keystone_dil_sprint`. -/
def arbitraryUS_UP_open : True := True.intro

#print axioms environment_universality
#print axioms recordLabel_injective
#print axioms swap_is_completion
#print axioms two_carrier_reads_as_bool
#print axioms environment_universality_fragment

end Bridge.Environment
