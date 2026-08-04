import Obs.Recovery
import Geom.Bounce

/-!
# Obs.CausalOrder

Finite causal order reconstructed from a bounce ascent and swap-archive
write order.

* Events: ascent ticks `0, …, tTurn`.
* Forward order: write order along the forward address (`i < j`).
* Reverse order: the opposite relation (address reversal).
* Interval cardinality matches capacity depth gap on ascent.
* Merge-rate capacity at tick `t` is `K ^ t` on ascent.

Orders and capacity volumes are unique up to address reversal.
-/

namespace Obs.CausalOrder

open Obs.Recovery
open Geom.Bounce

set_option linter.unusedVariables false

/-! ## Events and orders -/

/-- Forward causal order: earlier write before later write on the ascent. -/
def fwdPrecedes (tTurn i j : Nat) : Prop :=
  i < j ∧ j ≤ tTurn

/-- Reverse causal order: opposite of forward (address reversal). -/
def revPrecedes (tTurn i j : Nat) : Prop :=
  j < i ∧ i ≤ tTurn

/-- Order from an observer address. -/
def precedes (tTurn : Nat) : Address → Nat → Nat → Prop
  | Address.forward, i, j => fwdPrecedes tTurn i j
  | Address.reverse, i, j => revPrecedes tTurn i j

/-- Opposite relation. -/
def opposite (r : Nat → Nat → Prop) (i j : Nat) : Prop := r j i

theorem rev_is_opposite_fwd (tTurn i j : Nat) :
    revPrecedes tTurn i j ↔ opposite (fwdPrecedes tTurn) i j :=
  Iff.rfl

/-- Address reversal swaps the order (definitional on this encoding). -/
theorem address_reversal_opposes (tTurn i j : Nat) :
    precedes tTurn Address.forward i j ↔
      precedes tTurn Address.reverse j i :=
  Iff.rfl

theorem fwd_irrefl (tTurn i : Nat) : ¬ fwdPrecedes tTurn i i := by
  intro h
  exact Nat.lt_irrefl i h.1

theorem rev_irrefl (tTurn i : Nat) : ¬ revPrecedes tTurn i i := by
  intro h
  exact Nat.lt_irrefl i h.1

theorem fwd_trans {tTurn i j k : Nat}
    (hij : fwdPrecedes tTurn i j) (hjk : fwdPrecedes tTurn j k) :
    fwdPrecedes tTurn i k :=
  ⟨Nat.lt_trans hij.1 hjk.1, hjk.2⟩

theorem rev_trans {tTurn i j k : Nat}
    (hij : revPrecedes tTurn i j) (hjk : revPrecedes tTurn j k) :
    revPrecedes tTurn i k :=
  ⟨Nat.lt_trans hjk.1 hij.1, hij.2⟩

/-- Forward and reverse disagree on ordered pairs. -/
theorem fwd_rev_exclusive {tTurn i j : Nat}
    (hf : fwdPrecedes tTurn i j) : ¬ revPrecedes tTurn i j := by
  intro hr
  exact Nat.lt_asymm hf.1 hr.1

/-! ## Interval sizes match capacity depth -/

/-- Inclusive forward interval cardinality between `i` and `j` (`i ≤ j`). -/
def intervalCard (i j : Nat) : Nat := j - i + 1

/-- On ascent, bounce depth equals the tick. -/
theorem ascent_depth (tTurn t : Nat) (h : t ≤ tTurn) :
    bounceDepth tTurn t = t :=
  bounceDepth_asc h

/-- Interval card = depth gap + 1 on the forward ascent. -/
theorem interval_matches_depth {tTurn i j : Nat}
    (hij : i ≤ j) (hj : j ≤ tTurn) :
    intervalCard i j = (bounceDepth tTurn j - bounceDepth tTurn i) + 1 := by
  have hi : i ≤ tTurn := Nat.le_trans hij hj
  rw [ascent_depth tTurn j hj, ascent_depth tTurn i hi]
  rfl

/-- Capacity label at an ascent event for merge rate `K`. -/
def capacityAt (K tTurn t : Nat) : Nat := K ^ bounceDepth tTurn t

/-- On ascent, capacity is `K ^ t`. -/
theorem capacity_on_ascent {K tTurn t : Nat} (h : t ≤ tTurn) :
    capacityAt K tTurn t = K ^ t := by
  rw [capacityAt, ascent_depth tTurn t h]

/-- Capacity multiplies along a forward interval by `K ^ (j - i)`. -/
theorem pow_mul_gap (K i j : Nat) (hij : i ≤ j) :
    K ^ j = K ^ i * K ^ (j - i) := by
  induction hij with
  | refl =>
    have hz : i - i = 0 := Nat.sub_self i
    rw [hz, Nat.pow_zero, Nat.mul_one]
  | step h ih =>
    rename_i n
    -- `h : i ≤ n`, goal at `n+1`.
    rw [Nat.pow_succ, ih, Nat.mul_assoc, Nat.succ_sub h, Nat.pow_succ]

theorem capacity_along_interval {K tTurn i j : Nat}
    (_hK : 2 ≤ K) (hij : i ≤ j) (hj : j ≤ tTurn) :
    capacityAt K tTurn j = capacityAt K tTurn i * K ^ (j - i) := by
  have hi : i ≤ tTurn := Nat.le_trans hij hj
  simp only [capacityAt]
  rw [ascent_depth tTurn j hj, ascent_depth tTurn i hi]
  exact pow_mul_gap K i j hij

/-! ## Swap archive induces forward write order -/

/-- Write-index order on an archive of length `T`: slot `i` before `j`. -/
def archivePrecedes (T i j : Nat) : Prop :=
  i < j ∧ j < T

/-- Swap archive equals the prior path — write order is path index order. -/
theorem swap_archive_is_path (s : Bool) (es : List Bool) :
    (swapRun s es).2 = swapPriors s es :=
  swap_archive_path_recovers s es

/-- `j < T` iff `j ≤ T - 1` when `0 < T`. -/
theorem lt_iff_le_pred {T j : Nat} (hT : 0 < T) : j < T ↔ j ≤ T - 1 := by
  cases T with
  | zero => exact absurd hT (Nat.lt_irrefl 0)
  | succ n =>
    show j < n + 1 ↔ j ≤ n
    constructor
    · exact Nat.le_of_lt_succ
    · exact Nat.lt_succ_of_le

/-- Archive write order coincides with `fwdPrecedes` on write slots
`0 .. T-1` when the ascent turnaround is `T - 1`. -/
theorem archive_preceeds_iff_fwd {T i j : Nat} (hT : 0 < T) :
    archivePrecedes T i j ↔ fwdPrecedes (T - 1) i j := by
  constructor
  · intro h
    exact ⟨h.1, (lt_iff_le_pred hT).mp h.2⟩
  · intro h
    exact ⟨h.1, (lt_iff_le_pred hT).mpr h.2⟩

/-! ## Uniqueness up to address reversal

`unique_up_to_reversal_fwd` / `_rev` characterise Nat-monotone (resp.
Nat-antitone) orders on the window. `direction_dichotomy` recovers the
global direction from adjacency on consecutive ticks, propagated by
transitivity: every adjacency-uniform transitive order is forward or
reverse. -/

/-- The forward order is adjacency-uniform, so it instantiates the hypothesis
of `direction_dichotomy`. -/
theorem fwd_adjacent (tTurn : Nat) :
    ∀ i, i + 1 ≤ tTurn → fwdPrecedes tTurn i (i + 1) :=
  fun i h => ⟨Nat.lt_succ_self i, h⟩

/-- The reverse order is adjacency-uniform in the opposite sense. -/
theorem rev_adjacent (tTurn : Nat) :
    ∀ i, i + 1 ≤ tTurn → revPrecedes tTurn (i + 1) i :=
  fun i h => ⟨Nat.lt_succ_self i, h⟩

/-- Transitive + forward on consecutive pairs ⇒ Nat-monotone on the window. -/
theorem monotone_of_adjacent {tTurn : Nat} (prec : Nat → Nat → Prop)
    (htrans : ∀ a b c, prec a b → prec b c → prec a c)
    (hadj : ∀ i, i + 1 ≤ tTurn → prec i (i + 1)) :
    ∀ i j, j ≤ tTurn → i < j → prec i j := by
  intro i j
  induction j generalizing i with
  | zero => intro _ hi; exact absurd hi (Nat.not_lt_zero i)
  | succ n ih =>
    intro hn1 hi
    have hadjn : prec n (n + 1) := hadj n hn1
    cases Nat.lt_or_ge i n with
    | inl hlt =>
      exact htrans i n (n + 1) (ih i (Nat.le_of_succ_le hn1) hlt) hadjn
    | inr hge =>
      have heq : i = n := Nat.le_antisymm (Nat.le_of_lt_succ hi) hge
      rw [heq]
      exact hadjn

/-- Transitive + reverse on consecutive pairs ⇒ Nat-antitone on the window. -/
theorem antitone_of_adjacent {tTurn : Nat} (prec : Nat → Nat → Prop)
    (htrans : ∀ a b c, prec a b → prec b c → prec a c)
    (hadj : ∀ i, i + 1 ≤ tTurn → prec (i + 1) i) :
    ∀ i j, j ≤ tTurn → i < j → prec j i := by
  intro i j
  induction j generalizing i with
  | zero => intro _ hi; exact absurd hi (Nat.not_lt_zero i)
  | succ n ih =>
    intro hn1 hi
    have hadjn : prec (n + 1) n := hadj n hn1
    cases Nat.lt_or_ge i n with
    | inl hlt =>
      exact htrans (n + 1) n i hadjn (ih i (Nat.le_of_succ_le hn1) hlt)
    | inr hge =>
      have heq : i = n := Nat.le_antisymm (Nat.le_of_lt_succ hi) hge
      rw [heq]
      exact hadjn

/-- **Consecutive ticks fix the global direction.** A transitive order on the
window that agrees with the write order on every consecutive pair is
Nat-monotone; one that opposes it on every consecutive pair is Nat-antitone.
Local adjacency data forces one of exactly two global readings. -/
theorem direction_dichotomy {tTurn : Nat} (prec : Nat → Nat → Prop)
    (htrans : ∀ a b c, prec a b → prec b c → prec a c)
    (huniform : (∀ i, i + 1 ≤ tTurn → prec i (i + 1))
                ∨ (∀ i, i + 1 ≤ tTurn → prec (i + 1) i)) :
    (∀ i j, j ≤ tTurn → i < j → prec i j)
    ∨ (∀ i j, j ≤ tTurn → i < j → prec j i) := by
  cases huniform with
  | inl h => exact Or.inl (monotone_of_adjacent prec htrans h)
  | inr h => exact Or.inr (antitone_of_adjacent prec htrans h)

/-- **Unique up to address reversal.** An irreflexive, transitive,
adjacency-uniform order on the ascent window *is* the forward order or *is*
the reverse order. Note that totality is not needed: irreflexivity plus
transitivity already give asymmetry, and adjacency-uniformity supplies the
direction. -/
theorem unique_up_to_reversal {tTurn : Nat} (prec : Nat → Nat → Prop)
    (hirrefl : ∀ i, ¬ prec i i)
    (htrans : ∀ a b c, prec a b → prec b c → prec a c)
    (huniform : (∀ i, i + 1 ≤ tTurn → prec i (i + 1))
                ∨ (∀ i, i + 1 ≤ tTurn → prec (i + 1) i)) :
    (∀ i j, i ≤ tTurn → j ≤ tTurn → (prec i j ↔ fwdPrecedes tTurn i j))
    ∨ (∀ i j, i ≤ tTurn → j ≤ tTurn → (prec i j ↔ revPrecedes tTurn i j)) := by
  cases direction_dichotomy prec htrans huniform with
  | inl hmono =>
    refine Or.inl ?_
    intro i j hi hj
    constructor
    · intro hp
      refine ⟨?_, hj⟩
      cases Nat.lt_or_ge i j with
      | inl h => exact h
      | inr hge =>
        cases Nat.eq_or_lt_of_le hge with
        | inl heq =>
          rw [heq] at hp
          exact absurd hp (hirrefl i)
        | inr hlt =>
          exact absurd (htrans i j i hp (hmono j i hi hlt)) (hirrefl i)
    · intro hf
      exact hmono i j hj hf.1
  | inr hanti =>
    refine Or.inr ?_
    intro i j hi hj
    constructor
    · intro hp
      refine ⟨?_, hi⟩
      cases Nat.lt_or_ge j i with
      | inl h => exact h
      | inr hge =>
        cases Nat.eq_or_lt_of_le hge with
        | inl heq =>
          rw [heq] at hp
          exact absurd hp (hirrefl j)
        | inr hlt =>
          exact absurd (htrans i j i hp (hanti i j hj hlt)) (hirrefl i)
    · intro hr
      exact hanti j i hi hr.1

/-- If `prec` is total on `{0,…,tTurn}` and implies `i < j`, it is forward. -/
theorem unique_up_to_reversal_fwd {tTurn : Nat}
    (prec : Nat → Nat → Prop)
    (htotal : ∀ i j, i ≤ tTurn → j ≤ tTurn → i ≠ j → prec i j ∨ prec j i)
    (hmonotone : ∀ i j, prec i j → i < j) :
    ∀ i j, i ≤ tTurn → j ≤ tTurn → (prec i j ↔ fwdPrecedes tTurn i j) := by
  intro i j hi hj
  constructor
  · intro hp
    exact ⟨hmonotone i j hp, hj⟩
  · intro hf
    have hne : i ≠ j := Nat.ne_of_lt hf.1
    cases htotal i j hi hj hne with
    | inl hp => exact hp
    | inr hp =>
      exact absurd (hmonotone j i hp) (Nat.lt_asymm hf.1)

/-- If `prec` is total on `{0,…,tTurn}` and implies `j < i`, it is reverse. -/
theorem unique_up_to_reversal_rev {tTurn : Nat}
    (prec : Nat → Nat → Prop)
    (htotal : ∀ i j, i ≤ tTurn → j ≤ tTurn → i ≠ j → prec i j ∨ prec j i)
    (hantitone : ∀ i j, prec i j → j < i) :
    ∀ i j, i ≤ tTurn → j ≤ tTurn → (prec i j ↔ revPrecedes tTurn i j) := by
  intro i j hi hj
  constructor
  · intro hp
    exact ⟨hantitone i j hp, hi⟩
  · intro hr
    have hne : i ≠ j := Ne.symm (Nat.ne_of_lt hr.1)
    cases htotal i j hi hj hne with
    | inl hp => exact hp
    | inr hp =>
      exact absurd (hantitone j i hp) (Nat.lt_asymm hr.1)

/-- Package (axiom-free core): opposite addresses, interval–depth match,
swap archive = path, archive write order = forward index order on write slots,
forward/reverse exclusive, and uniqueness up to address reversal.

`capacity_along_interval` is available separately; it inherits `propext` from
`Nat.le` induction in the prelude. -/
theorem causal_order_reconstruction {tTurn i j : Nat}
    (hij : i ≤ j) (hj : j ≤ tTurn) :
    (precedes tTurn Address.forward i j ↔
      precedes tTurn Address.reverse j i)
    ∧ intervalCard i j = (bounceDepth tTurn j - bounceDepth tTurn i) + 1
    ∧ (∀ s : Bool, ∀ es : List Bool, (swapRun s es).2 = swapPriors s es)
    ∧ (∀ T a b : Nat, 0 < T →
        (archivePrecedes T a b ↔ fwdPrecedes (T - 1) a b))
    ∧ (fwdPrecedes tTurn i j → ¬ revPrecedes tTurn i j)
    ∧ (∀ prec : Nat → Nat → Prop,
        (∀ a, ¬ prec a a) →
        (∀ a b c, prec a b → prec b c → prec a c) →
        ((∀ a, a + 1 ≤ tTurn → prec a (a + 1))
          ∨ (∀ a, a + 1 ≤ tTurn → prec (a + 1) a)) →
        (∀ a b, a ≤ tTurn → b ≤ tTurn → (prec a b ↔ fwdPrecedes tTurn a b))
        ∨ (∀ a b, a ≤ tTurn → b ≤ tTurn →
            (prec a b ↔ revPrecedes tTurn a b))) :=
  ⟨address_reversal_opposes tTurn i j,
   interval_matches_depth hij hj,
   swap_archive_is_path,
   fun _ _ _ hT => archive_preceeds_iff_fwd hT,
   fun hf => fwd_rev_exclusive hf,
   fun prec hirr htr hun => unique_up_to_reversal prec hirr htr hun⟩

end Obs.CausalOrder

#print axioms Obs.CausalOrder.rev_is_opposite_fwd
#print axioms Obs.CausalOrder.address_reversal_opposes
#print axioms Obs.CausalOrder.interval_matches_depth
#print axioms Obs.CausalOrder.capacity_on_ascent
#print axioms Obs.CausalOrder.capacity_along_interval
#print axioms Obs.CausalOrder.archive_preceeds_iff_fwd
#print axioms Obs.CausalOrder.fwd_adjacent
#print axioms Obs.CausalOrder.rev_adjacent
#print axioms Obs.CausalOrder.monotone_of_adjacent
#print axioms Obs.CausalOrder.antitone_of_adjacent
#print axioms Obs.CausalOrder.direction_dichotomy
#print axioms Obs.CausalOrder.unique_up_to_reversal
#print axioms Obs.CausalOrder.unique_up_to_reversal_fwd
#print axioms Obs.CausalOrder.unique_up_to_reversal_rev
#print axioms Obs.CausalOrder.causal_order_reconstruction
