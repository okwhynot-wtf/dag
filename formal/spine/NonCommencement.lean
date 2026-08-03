import Canon
import Density
import Ladder
import Tower

/-!
# NonCommencement — the fundamental is below every before

The ladder has a least rung, and the fundamental carries no iteration count.
Together these facts block the reading of Level 0 as a first event that
began after something earlier.

* **Parity forgetting** (`iterate_parity`, `fundamental_forgets_count`): on an
  involutive act, iterates depend only on the parity of the index, so the
  fundamental state records no count of applications.
* **No rung below** (`no_fundamental_below_two`, `no_live_act_on_inhabited_subsingleton`,
  `fundamental_is_least`): no fundamental on `Fin 1`; no live act on an inhabited
  subsingleton; no inhabited live source injects into Level 0 as the
  source of a naming extension.
* **Ladder contrast** (`ladder_index_recoverable`): level cardinality
  recovers the index, so ladder states wear their history.

No declared axioms.
-/
namespace NonCommencement

open Orbit

variable {α : Type}

/-! ## Parity forgetting on involutions

Library lemmas for `Nat.mod` depend on `propext` in this toolchain, so the
parity character is carried by the recursive remainder `mod2` (equal in
informal content to `n % 2`). -/

/-- Recursive remainder modulo 2: `0` on evens, `1` on odds. -/
def mod2 : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n + 2 => mod2 n

theorem mod2_even (k : Nat) : mod2 (k + k) = 0 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hshape : (k + 1) + (k + 1) = (k + k) + 2 := by
      calc
        (k + 1) + (k + 1) = k + (1 + (k + 1)) := by rw [Nat.add_assoc]
        _ = k + ((1 + k) + 1) := by rw [← Nat.add_assoc 1 k 1]
        _ = k + ((k + 1) + 1) := by rw [Nat.add_comm 1 k]
        _ = k + (k + (1 + 1)) := by rw [Nat.add_assoc k 1 1]
        _ = k + (k + 2) := rfl
        _ = (k + k) + 2 := by rw [← Nat.add_assoc]
    show mod2 ((k + 1) + (k + 1)) = 0
    rw [hshape]
    exact ih

theorem mod2_odd (k : Nat) : mod2 (k + k + 1) = 1 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hshape : (k + 1) + (k + 1) + 1 = (k + k + 1) + 2 := by
      have heven : (k + 1) + (k + 1) = (k + k) + 2 := by
        calc
          (k + 1) + (k + 1) = k + (1 + (k + 1)) := by rw [Nat.add_assoc]
          _ = k + ((1 + k) + 1) := by rw [← Nat.add_assoc 1 k 1]
          _ = k + ((k + 1) + 1) := by rw [Nat.add_comm 1 k]
          _ = k + (k + (1 + 1)) := by rw [Nat.add_assoc k 1 1]
          _ = k + (k + 2) := rfl
          _ = (k + k) + 2 := by rw [← Nat.add_assoc]
      calc
        (k + 1) + (k + 1) + 1 = (k + k) + 2 + 1 := by rw [heven]
        _ = (k + k) + (2 + 1) := by rw [Nat.add_assoc]
        _ = (k + k) + (1 + 2) := by rw [Nat.add_comm 2 1]
        _ = (k + k + 1) + 2 := by rw [← Nat.add_assoc]
    show mod2 ((k + 1) + (k + 1) + 1) = 1
    rw [hshape]
    exact ih

/-- Even iterates of an involution recover the seed. -/
theorem iter_even (act : α → α) (h : ∀ x, act (act x) = x)
    (z : α) (k : Nat) : iter act (k + k) z = z := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hshape : (k + 1) + (k + 1) = (k + k) + 2 := by
      calc
        (k + 1) + (k + 1) = k + (1 + (k + 1)) := by rw [Nat.add_assoc]
        _ = k + ((1 + k) + 1) := by rw [← Nat.add_assoc 1 k 1]
        _ = k + ((k + 1) + 1) := by rw [Nat.add_comm 1 k]
        _ = k + (k + (1 + 1)) := by rw [Nat.add_assoc k 1 1]
        _ = k + (k + 2) := rfl
        _ = (k + k) + 2 := by rw [← Nat.add_assoc]
    show iter act ((k + 1) + (k + 1)) z = z
    rw [hshape]
    show act (act (iter act (k + k) z)) = z
    rw [ih, h]

/-- Odd iterates of an involution recover one application. -/
theorem iter_odd (act : α → α) (h : ∀ x, act (act x) = x)
    (z : α) (k : Nat) : iter act (k + k + 1) z = act z := by
  show act (iter act (k + k) z) = act z
  rw [iter_even act h z k]

/-- On an involutive act, the `n`-th iterate equals the iterate at `mod2 n`
    (remainder modulo 2). Even indices recover the seed; odd indices recover
    one application. -/
theorem iterate_parity (act : α → α) (h : ∀ x, act (act x) = x)
    (z : α) (n : Nat) :
    iter act n z = iter act (mod2 n) z := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    match n with
    | 0 => rfl
    | 1 => rfl
    | n + 2 =>
      have hn : n < n + 2 := Nat.lt_add_of_pos_right (Nat.zero_lt_succ 1)
      have ihn : iter act n z = iter act (mod2 n) z := ih n hn
      show act (act (iter act n z)) = iter act (mod2 n) z
      rw [h (iter act n z), ihn]

/-- Equal parity of indices yields equal iterates under an involution.
    The fundamental state carries no recoverable count of applications beyond
    parity. -/
theorem fundamental_forgets_count (act : α → α) (h : ∀ x, act (act x) = x)
    (z : α) (m n : Nat) (hpar : mod2 m = mod2 n) :
    iter act m z = iter act n z := by
  rw [iterate_parity act h z m, iterate_parity act h z n, hpar]

/-! ## No live act beneath two elements -/

/-- An inhabited subsingleton admits no live act: the unique point is a
    fixed point. The empty type is excluded by `Inhabited`; vacuous
    liveness on `Empty` is not a predecessor rung. -/
theorem no_live_act_on_inhabited_subsingleton
    [Subsingleton α] [Inhabited α] (act : α → α) :
    ¬ Live act := by
  intro hl
  exact hl default (Subsingleton.elim (act default) default)

/-- No fundamental exists on a one-point carrier. Rest is forced, and rest
    contradicts the liveness that fundamentality implies. -/
theorem no_fundamental_below_two (act : Fin 1 → Fin 1) :
    ¬ Canon.IsFundamental act := by
  intro h
  have := Density.fundamentals_only_at_two 1 act h
  exact (by decide : ¬ (1 = 2)) this

/-! ## Least rung -/

/-- No inhabited live source injects into Level 0 as the source of a naming
    extension. The namer lies outside the image, so the image is a singleton
    in `Bool`; injectivity then forces a subsingleton source, which admits
    no live act. -/
theorem fundamental_is_least {A : Type} [Inhabited A] (act : A → A)
    (hl : Live act) (f : A → A → Bool) (ι : A → Ladder.Level 0)
    (e : A → Bool) (ne : Tower.NamingExtension f (Ladder.rep 0) ι e)
    (hinj : ∀ a₁ a₂, ι a₁ = ι a₂ → a₁ = a₂) :
    False := by
  obtain ⟨b, _, hnew⟩ := Tower.namer_is_new ne
  let a0 : A := default
  have him : ∀ a, ι a = ι a0 := by
    intro a
    have ha : ι a ≠ b := hnew a
    have h0 : ι a0 ≠ b := hnew a0
    cases b with
    | false =>
      have ha' : ι a = true := by
        cases hι : ι a with
        | false => exact absurd hι ha
        | true => rfl
      have h0' : ι a0 = true := by
        cases hι : ι a0 with
        | false => exact absurd hι h0
        | true => rfl
      exact ha'.trans h0'.symm
    | true =>
      have ha' : ι a = false := by
        cases hι : ι a with
        | true => exact absurd hι ha
        | false => rfl
      have h0' : ι a0 = false := by
        cases hι : ι a0 with
        | true => exact absurd hι h0
        | false => rfl
      exact ha'.trans h0'.symm
  have hsub : ∀ a, a = a0 := fun a => hinj a a0 (him a)
  haveI : Subsingleton A := ⟨fun x y => (hsub x).trans (hsub y).symm⟩
  exact no_live_act_on_inhabited_subsingleton act hl

/-! ## Ladder contrast: index from cardinality -/

/-- Equal level cardinalities yield equal indices. Ladder states wear their
    history; paired with `fundamental_forgets_count`, this is the formal
    signature of duration above and eternity below. -/
theorem ladder_index_recoverable (j k : Nat) :
    Density.levelCard j = Density.levelCard k → j = k := by
  intro h
  have hj : Density.levelCard j = j + 2 := Density.levelCard_eq j
  have hk : Density.levelCard k = k + 2 := Density.levelCard_eq k
  have hsum : j + 2 = k + 2 := by
    rw [← hj, h, hk]
  exact Nat.succ.inj (Nat.succ.inj hsum)

/-! ## Package -/

/-- Non-commencement package: parity forgetting, no fundamental below two, and
    recoverable ladder index. -/
theorem non_commencement_package :
    (∀ (act : α → α), (∀ x, act (act x) = x) →
      ∀ z n, iter act n z = iter act (mod2 n) z) ∧
    (∀ (act : Fin 1 → Fin 1), ¬ Canon.IsFundamental act) ∧
    (∀ j k, Density.levelCard j = Density.levelCard k → j = k) :=
  ⟨fun act h z n => iterate_parity act h z n,
   no_fundamental_below_two,
   ladder_index_recoverable⟩

end NonCommencement
