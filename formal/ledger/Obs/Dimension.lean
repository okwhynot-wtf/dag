import Obs.CausalOrder
import Obs.Recovery
import Geom.Bounce

/-!
# Obs.Dimension

Dimension / growth dictionary from the finite causal order of
`Obs.CausalOrder` and its capacity labels.

Two separate readings (do not identify them):

1. **Order dimension** — interval cardinality is linear in separation, so the
   ascent causal order is combinatorially 1-dimensional (a chain).
2. **Capacity growth rate** — on ascent, capacity multiplies by the merge
   alphabet `K` each tick (`K ^ t`).

Not a continuum Hausdorff dimension and not a Lorentzian metric.
-/

namespace Obs.Dimension

open Obs.CausalOrder
open Obs.Recovery
open Geom.Bounce

/-! ## Order dimension (= 1 for the ascent chain) -/

/-- Separation along the forward ascent. -/
def separation (i j : Nat) : Nat := j - i

/-- Interval card is exactly linear in separation: `|I(i,j)| = sep + 1`.

This conjunct is an arithmetic identity about the definitions
(`intervalCard i j = j - i + 1`, `separation i j = j - i`) and needs no
hypotheses. The ascent-specific content is `depth_gap_eq_separation`, which
does need `i ≤ j ≤ tTurn`. -/
theorem interval_linear (i j : Nat) :
    intervalCard i j = separation i j + 1 :=
  rfl

/-- Depth gap equals separation on ascent (order dim 1 scaling). -/
theorem depth_gap_eq_separation {tTurn i j : Nat}
    (hij : i ≤ j) (hj : j ≤ tTurn) :
    bounceDepth tTurn j - bounceDepth tTurn i = separation i j := by
  have hi : i ≤ tTurn := Nat.le_trans hij hj
  rw [ascent_depth tTurn j hj, ascent_depth tTurn i hi]
  rfl

/-- Forward order is total on distinct ascent events. -/
theorem ascent_total {tTurn i j : Nat}
    (hi : i ≤ tTurn) (hj : j ≤ tTurn) (hne : i ≠ j) :
    fwdPrecedes tTurn i j ∨ fwdPrecedes tTurn j i := by
  cases Nat.lt_or_gt_of_ne hne with
  | inl hij => exact Or.inl ⟨hij, hj⟩
  | inr hji => exact Or.inr ⟨hji, hi⟩

/-- Comparability: every distinct ascent pair is ordered (chain ⇒ dim 1). -/
theorem ascent_comparable {tTurn i j : Nat}
    (hi : i ≤ tTurn) (hj : j ≤ tTurn) (hne : i ≠ j) :
    precedes tTurn Obs.Recovery.Address.forward i j
      ∨ precedes tTurn Obs.Recovery.Address.forward j i :=
  ascent_total hi hj hne

/-! ### Dushnik--Miller dimension

Order dimension is the least size of a family of linear extensions whose
intersection, on the window, is the order. Dimension one is realised by a
single extension and has no size-zero realiser. -/

/-- `L` is a strict linear order on the window `{0,…,tTurn}`. -/
def StrictLinear (tTurn : Nat) (L : Nat → Nat → Prop) : Prop :=
  (∀ i, ¬ L i i)
  ∧ (∀ i j k, L i j → L j k → L i k)
  ∧ (∀ i j, i ≤ tTurn → j ≤ tTurn → i ≠ j → L i j ∨ L j i)

/-- `L` is an extension of `R`: everything `R` orders, `L` orders the same way. -/
def Extends (L R : Nat → Nat → Prop) : Prop := ∀ i j, R i j → L i j

/-- `Ls` realises `R` on the window: every member is a linear extension of
`R`, and any window pair on which *all* members agree is already ordered by
`R`. So `R` is exactly the intersection of the family. -/
def Realises (tTurn : Nat) (Ls : List (Nat → Nat → Prop))
    (R : Nat → Nat → Prop) : Prop :=
  (∀ L, L ∈ Ls → StrictLinear tTurn L ∧ Extends L R)
  ∧ (∀ i j, i ≤ tTurn → j ≤ tTurn → (∀ L, L ∈ Ls → L i j) → R i j)

/-- Dushnik--Miller order dimension at most `d`. -/
def OrderDimLE (tTurn : Nat) (R : Nat → Nat → Prop) (d : Nat) : Prop :=
  ∃ Ls : List (Nat → Nat → Prop), Ls.length ≤ d ∧ Realises tTurn Ls R

/-- Order dimension exactly `d`: realisable at `d`, at no smaller size. -/
def OrderDimEq (tTurn : Nat) (R : Nat → Nat → Prop) (d : Nat) : Prop :=
  OrderDimLE tTurn R d ∧ ∀ e, e < d → ¬ OrderDimLE tTurn R e

/-- The forward ascent order is a strict linear order on its window. -/
theorem fwd_strict_linear (tTurn : Nat) :
    StrictLinear tTurn (fwdPrecedes tTurn) :=
  ⟨fun i => fwd_irrefl tTurn i,
   fun _ _ _ hij hjk => fwd_trans hij hjk,
   fun _ _ hi hj hne => ascent_total hi hj hne⟩

/-- A chain realises itself: the one-element family `[<]` is a realiser. -/
theorem ascent_order_dim_le_one (tTurn : Nat) :
    OrderDimLE tTurn (fwdPrecedes tTurn) 1 := by
  refine ⟨[fwdPrecedes tTurn], Nat.le_refl 1, ?_, ?_⟩
  · intro L hL
    cases hL with
    | head => exact ⟨fwd_strict_linear tTurn, fun _ _ h => h⟩
    | tail _ h => cases h
  · intro i j _ _ hall
    exact hall (fwdPrecedes tTurn) (List.Mem.head _)

/-- No realiser of size zero: the empty intersection relates every window
pair, including `(0,0)`, which the irreflexive ascent order does not. -/
theorem ascent_order_dim_not_zero (tTurn : Nat) :
    ¬ OrderDimLE tTurn (fwdPrecedes tTurn) 0 := by
  intro h
  cases h with
  | intro Ls hLs =>
    cases Ls with
    | cons _ _ => exact absurd hLs.1 (Nat.not_succ_le_zero _)
    | nil =>
      have hall : ∀ L, L ∈ ([] : List (Nat → Nat → Prop)) → L 0 0 := by
        intro _ hL; cases hL
      exact fwd_irrefl tTurn 0
        (hLs.2.2 0 0 (Nat.zero_le _) (Nat.zero_le _) hall)

/-- **Order dimension of the ascent is exactly one.** -/
theorem ascent_order_dim_eq_one (tTurn : Nat) :
    OrderDimEq tTurn (fwdPrecedes tTurn) 1 := by
  refine ⟨ascent_order_dim_le_one tTurn, ?_⟩
  intro e he
  have h0 : e = 0 := Nat.le_zero.mp (Nat.le_of_lt_succ he)
  rw [h0]
  exact ascent_order_dim_not_zero tTurn

/-- Package: order dimension is 1 — a realiser of size one and none of size
zero — plus linear intervals, depth gap = separation, and totality of the
ascent chain. -/
theorem order_dimension_one {tTurn i j : Nat}
    (hij : i ≤ j) (hj : j ≤ tTurn) :
    OrderDimEq tTurn (fwdPrecedes tTurn) 1
    ∧ intervalCard i j = separation i j + 1
    ∧ bounceDepth tTurn j - bounceDepth tTurn i = separation i j
    ∧ (i ≠ j → (i ≤ tTurn → j ≤ tTurn →
        fwdPrecedes tTurn i j ∨ fwdPrecedes tTurn j i)) :=
  ⟨ascent_order_dim_eq_one tTurn,
   interval_linear i j,
   depth_gap_eq_separation hij hj,
   fun hne hi hj' => ascent_total hi hj' hne⟩

/-! ## Capacity growth rate (= merge alphabet K) -/

/-- One-step capacity growth on ascent: multiplies by `K`. -/
theorem capacity_step_growth {K tTurn t : Nat}
    (h : t + 1 ≤ tTurn) :
    capacityAt K tTurn (t + 1) = K * capacityAt K tTurn t := by
  have ht : t ≤ tTurn := Nat.le_of_succ_le h
  rw [capacity_on_ascent h, capacity_on_ascent ht, Nat.pow_succ, Nat.mul_comm]

/-- Capacity at tick `t` on ascent is exactly `K ^ t`. -/
theorem capacity_is_pow {K tTurn t : Nat} (h : t ≤ tTurn) :
    capacityAt K tTurn t = K ^ t :=
  capacity_on_ascent h

/-- Uniqueness of exponential capacity: any `c` with `c 0 = 1` and
`c (t+1) = K * c t` on the ascent equals `K ^ t`. -/
def StepGrowth (K tTurn : Nat) (c : Nat → Nat) : Prop :=
  c 0 = 1 ∧ ∀ t, t + 1 ≤ tTurn → c (t + 1) = K * c t

theorem step_growth_eq_pow {K tTurn : Nat} {c : Nat → Nat}
    (h : StepGrowth K tTurn c) :
    ∀ t, t ≤ tTurn → c t = K ^ t := by
  intro t ht
  induction t with
  | zero =>
    show c 0 = K ^ 0
    rw [h.1, Nat.pow_zero]
  | succ n ih =>
    have hn : n ≤ tTurn := Nat.le_of_succ_le ht
    rw [h.2 n ht, ih hn, Nat.pow_succ, Nat.mul_comm]

/-- Capacity labels realize the unique step-growth solution. -/
theorem capacity_unique_step_growth {K tTurn : Nat} :
    StepGrowth K tTurn (fun t => capacityAt K tTurn t)
    ∧ ∀ c, StepGrowth K tTurn c → ∀ t, t ≤ tTurn → c t = capacityAt K tTurn t := by
  refine ⟨?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · show capacityAt K tTurn 0 = 1
      rw [capacity_on_ascent (Nat.zero_le _), Nat.pow_zero]
    · intro t ht
      exact capacity_step_growth ht
  · intro c hc t ht
    have hc' := step_growth_eq_pow hc t ht
    have hcap := capacity_on_ascent (K := K) (tTurn := tTurn) ht
    rw [hc', hcap]

/-- Growth over an interval: capacity multiplies by `K ^ separation`. -/
theorem capacity_growth_over_interval {K tTurn i j : Nat}
    (hij : i ≤ j) (hj : j ≤ tTurn) :
    capacityAt K tTurn j = capacityAt K tTurn i * K ^ separation i j := by
  have hi : i ≤ tTurn := Nat.le_trans hij hj
  simp only [separation]
  rw [capacity_is_pow hj, capacity_is_pow hi]
  -- Name the gap first, rewrite RHS to use it, then replace `j` on the LHS.
  let d := j - i
  have hd : j - i = d := rfl
  have hsum : i + d = j := Nat.add_sub_of_le hij
  rw [hd, ← hsum]
  exact Nat.pow_add K i d

/-! ## Joint dictionary package -/

/-- Order dimension 1 + capacity growth rate `K`, from the causal-order
dictionary. Address reversal preserves the order reading. -/
theorem dimension_from_growth {K tTurn i j : Nat}
    (_hK : 2 ≤ K) (hij : i ≤ j) (hj : j ≤ tTurn) :
    OrderDimEq tTurn (fwdPrecedes tTurn) 1
    ∧ intervalCard i j = separation i j + 1
    ∧ capacityAt K tTurn j = capacityAt K tTurn i * K ^ separation i j
    ∧ (precedes tTurn Obs.Recovery.Address.forward i j ↔
        precedes tTurn Obs.Recovery.Address.reverse j i) :=
  ⟨ascent_order_dim_eq_one tTurn,
   interval_linear i j,
   capacity_growth_over_interval hij hj,
   address_reversal_opposes tTurn i j⟩

end Obs.Dimension

#print axioms Obs.Dimension.interval_linear
#print axioms Obs.Dimension.depth_gap_eq_separation
#print axioms Obs.Dimension.ascent_total
#print axioms Obs.Dimension.fwd_strict_linear
#print axioms Obs.Dimension.ascent_order_dim_le_one
#print axioms Obs.Dimension.ascent_order_dim_not_zero
#print axioms Obs.Dimension.ascent_order_dim_eq_one
#print axioms Obs.Dimension.order_dimension_one
#print axioms Obs.Dimension.capacity_step_growth
#print axioms Obs.Dimension.step_growth_eq_pow
#print axioms Obs.Dimension.capacity_unique_step_growth
#print axioms Obs.Dimension.capacity_growth_over_interval
#print axioms Obs.Dimension.dimension_from_growth
