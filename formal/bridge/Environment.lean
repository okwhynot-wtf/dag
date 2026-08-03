import Density
import Ladder
import Alphabet
import Capacity

/-!
# T-1 Environment universality (keystone — constructive fragment)

Define `E` as the ladder carrier supplying cap slots; recover `|E| ≥ K`
as corollary of alphabet grounding at `K = 2`. Full universal-property
uniqueness up to iso is residue if the arrow-theoretic statement fails
(see `docs/RESIDUE.md`).
-/

namespace Bridge.Environment

/-- Environment at horizon `T`: the DM ladder carrier (I-2). -/
def E (T : Nat) : Type := Ladder.Level T

/-- Cap slots at `T` are counted by the predicate space. -/
def capCount (T : Nat) : Nat := Bridge.Capacity.caps T

theorem capCount_eq (T : Nat) : capCount T = 2 ^ (T + 2) :=
  Bridge.Capacity.caps_eq T

/-- Carrier size of `E T` is `T + 2`. -/
theorem env_card (T : Nat) : Density.levelCard T = T + 2 :=
  Density.levelCard_eq T

/-- At the Fundamental, the environment alphabet is at least 2. -/
theorem env_ge_Kmin :
    Bridge.Alphabet.Kmin = 2 ∧
    (∀ T, Bridge.Alphabet.Kmin ≤ capCount T) := by
  refine ⟨rfl, ?_⟩
  intro T
  rw [capCount_eq]
  -- 2 = 2^1 ≤ 2^(T+2)
  have hpos : 0 < 2 := by decide
  have hle : 1 ≤ T + 2 := Nat.succ_le_succ (Nat.zero_le (T + 1))
  exact Nat.pow_le_pow_right hpos hle

/-- Existence: the ladder supplies an environment for every horizon. -/
theorem env_exists (T : Nat) : Nonempty (E T) := by
  match T with
  | 0 => exact ⟨true⟩
  | n + 1 => exact ⟨none⟩

/-- **T-1 fragment.** Environment implemented by the ladder; capacity
    count `2^(T+2)`; `|E|`-side lower bound at `Kmin = 2`. Full UP
    uniqueness deferred. -/
theorem environment_universality_fragment :
    (∀ T, capCount T = 2 ^ (T + 2)) ∧
    (∀ T, Nonempty (E T)) ∧
    Bridge.Alphabet.Kmin = 2 ∧
    (∀ T, Bridge.Alphabet.Kmin ≤ capCount T) :=
  ⟨capCount_eq, env_exists, env_ge_Kmin.1, env_ge_Kmin.2⟩

def universalityUPOpen : True := True.intro

#print axioms environment_universality_fragment
#print axioms env_exists
#print axioms capCount_eq

end Bridge.Environment
