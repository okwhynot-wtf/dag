/-!
# Geom.Bounce

Bounce capacity profile: depth grows to a turnaround then shrinks. For
`K ≥ 2`, the alive set is `{0,...,tTurn}` and exhaustion equals the turnaround.
-/

set_option linter.unusedSectionVars false

namespace Geom.Bounce

/-- Bounce depth: grow to `tTurn`, then shrink symmetrically to 0. -/
def bounceDepth (tTurn t : Nat) : Nat :=
  if t ≤ tTurn then t
  else if t ≤ 2 * tTurn then 2 * tTurn - t
  else 0

/-- On the ascending branch the depth is the tick itself. -/
theorem bounceDepth_asc {tTurn t : Nat} (h : t ≤ tTurn) :
    bounceDepth tTurn t = t :=
  if_pos h

/-- At the turnaround the depth equals the turnaround. -/
theorem bounceDepth_turn (tTurn : Nat) :
    bounceDepth tTurn tTurn = tTurn :=
  bounceDepth_asc (Nat.le_refl tTurn)

/-- Past twice the turnaround the depth is zero. -/
theorem bounceDepth_past {tTurn t : Nat} (h : 2 * tTurn < t) :
    bounceDepth tTurn t = 0 := by
  have hnt : ¬ t ≤ tTurn := fun hle =>
    Nat.lt_irrefl t (Nat.lt_of_le_of_lt
      (Nat.le_trans hle (Nat.le_mul_of_pos_left tTurn (Nat.succ_pos 1))) h)
  have hn2 : ¬ t ≤ 2 * tTurn := Nat.not_le_of_gt h
  show (if t ≤ tTurn then t
        else if t ≤ 2 * tTurn then 2 * tTurn - t else 0) = 0
  rw [if_neg hnt, if_neg hn2]

/-- On the descending branch, depth is `2 * tTurn - t`. -/
theorem bounceDepth_desc {tTurn t : Nat}
    (h1 : tTurn < t) (h2 : t ≤ 2 * tTurn) :
    bounceDepth tTurn t = 2 * tTurn - t := by
  have hnt : ¬ t ≤ tTurn := Nat.not_le_of_gt h1
  show (if t ≤ tTurn then t
        else if t ≤ 2 * tTurn then 2 * tTurn - t else 0) = 2 * tTurn - t
  rw [if_neg hnt, if_pos h2]

/-- Convert `¬ a ≤ b` to `b < a` via `decide`, axiom-free. -/
theorem lt_of_not_le {a b : Nat} (h : ¬ a ≤ b) : b < a := by
  cases hdec : decide (b < a) with
  | true => exact of_decide_eq_true hdec
  | false =>
    have hnba : ¬ b < a := of_decide_eq_false hdec
    have hba : a ≤ b := Nat.le_of_not_gt hnba
    exact absurd hba h

/-- Strict growth of powers for `K ≥ 2`: `K ^ n < K ^{n+1}`. -/
theorem pow_lt_succ {K : Nat} (hK : 2 ≤ K) (n : Nat) :
    K ^ n < K ^ (n + 1) := by
  show K ^ n < K ^ n * K
  have hpos : 0 < K ^ n := by
    induction n with
    | zero => exact Nat.zero_lt_one
    | succ n ih => exact Nat.mul_pos ih (Nat.lt_of_lt_of_le (by decide) hK)
  have hk : 1 < K := Nat.lt_of_lt_of_le (by decide) hK
  have h := Nat.mul_lt_mul_of_pos_left hk hpos
  rw [Nat.mul_one] at h
  exact h

/-- Monotonicity of powers in the exponent for `K ≥ 2`. -/
theorem pow_le_pow_of_le {K : Nat} (hK : 2 ≤ K) {a b : Nat} (h : a ≤ b) :
    K ^ a ≤ K ^ b :=
  Nat.pow_le_pow_right (Nat.lt_of_lt_of_le (by decide) hK) h

/-- Strict antitonicity: larger exponent, strictly larger power. -/
theorem pow_lt_pow_of_lt {K : Nat} (hK : 2 ≤ K) {a b : Nat} (h : a < b) :
    K ^ a < K ^ b := by
  have h' : a + 1 ≤ b := Nat.succ_le_of_lt h
  exact Nat.lt_of_lt_of_le (pow_lt_succ hK a) (pow_le_pow_of_le hK h')

/-- For `K ≥ 2`, `K ^ a ≤ K ^ b` iff `a ≤ b`. -/
theorem pow_le_pow_iff_le {K : Nat} (hK : 2 ≤ K) (a b : Nat) :
    K ^ a ≤ K ^ b ↔ a ≤ b := by
  apply Iff.intro
  · intro h
    cases hdec : decide (a ≤ b) with
    | true => exact of_decide_eq_true hdec
    | false =>
      have hab : ¬ a ≤ b := of_decide_eq_false hdec
      exact absurd h (Nat.not_le_of_gt (pow_lt_pow_of_lt hK (lt_of_not_le hab)))
  · intro h
    exact pow_le_pow_of_le hK h

/-- Alive at horizon `T` under the exponent bounce schedule means
`K ^ T ≤ K ^{bounceDepth tTurn T}`, i.e. `T ≤ bounceDepth tTurn T`. -/
def Alive (K tTurn T : Nat) : Prop :=
  K ^ T ≤ K ^ bounceDepth tTurn T

/-- Under `K ≥ 2`, alive iff the horizon does not exceed the depth. -/
theorem alive_iff_le_depth {K : Nat} (hK : 2 ≤ K) (tTurn T : Nat) :
    Alive K tTurn T ↔ T ≤ bounceDepth tTurn T :=
  pow_le_pow_iff_le hK T (bounceDepth tTurn T)

/-- **Ascending aliveness.** Every horizon up to the turnaround is alive. -/
theorem alive_upto_turn {K : Nat} (_hK : 2 ≤ K) (tTurn : Nat) :
    ∀ T : Nat, T ≤ tTurn → Alive K tTurn T := by
  intro T hT
  have hd : bounceDepth tTurn T = T := bounceDepth_asc hT
  show K ^ T ≤ K ^ bounceDepth tTurn T
  rw [hd]
  exact Nat.le_refl _

/-- `2 * n = n + n`, using only axiom-free core lemmas. -/
theorem two_mul_eq_add (n : Nat) : 2 * n = n + n := by
  show (Nat.succ 1) * n = n + n
  rw [Nat.succ_mul, Nat.one_mul]

/-- Local `a + (b - a) = b` under `a ≤ b` (core version carries `propext`). -/
theorem add_sub_of_le : ∀ {a b : Nat}, a ≤ b → a + (b - a) = b
  | 0, b, _ => by
    show 0 + (b - 0) = b
    rw [Nat.zero_add, Nat.sub_zero]
  | a + 1, 0, h => absurd h (Nat.not_succ_le_zero a)
  | a + 1, b + 1, h => by
    have ih := add_sub_of_le (Nat.le_of_succ_le_succ h)
    show (a + 1) + ((b + 1) - (a + 1)) = b + 1
    rw [Nat.succ_sub_succ, Nat.succ_add, ih]

/-- On the descending branch, `T ≤ 2*tTurn - T` forces `T ≤ tTurn`. -/
theorem desc_le_implies_le_turn {tTurn T : Nat}
    (h2 : T ≤ 2 * tTurn) (hDepth : T ≤ 2 * tTurn - T) :
    T ≤ tTurn := by
  have hadd := Nat.add_le_add_left hDepth T
  have hsum : T + (2 * tTurn - T) = 2 * tTurn := add_sub_of_le h2
  have h2T : T + T ≤ 2 * tTurn := by
    rw [← hsum]; exact hadd
  have hmul : 2 * T ≤ 2 * tTurn := by
    rw [two_mul_eq_add]; exact h2T
  exact Nat.le_of_mul_le_mul_left hmul (Nat.succ_pos 1)

/-- **Past the turnaround, dead.** For `T > tTurn`, the bounce schedule
is not alive at `T`. -/
theorem not_alive_past_turn {K : Nat} (hK : 2 ≤ K) (tTurn T : Nat)
    (hT : tTurn < T) : ¬ Alive K tTurn T := by
  intro hA
  have hDepth : T ≤ bounceDepth tTurn T :=
    (alive_iff_le_depth hK tTurn T).mp hA
  cases hdec : decide (T ≤ 2 * tTurn) with
  | true =>
    have h2 : T ≤ 2 * tTurn := of_decide_eq_true hdec
    have hd : bounceDepth tTurn T = 2 * tTurn - T :=
      bounceDepth_desc hT h2
    have hDepth' : T ≤ 2 * tTurn - T := by
      rw [← hd]; exact hDepth
    exact Nat.not_le_of_gt hT (desc_le_implies_le_turn h2 hDepth')
  | false =>
    have hn2 : ¬ T ≤ 2 * tTurn := of_decide_eq_false hdec
    have hlt : 2 * tTurn < T := lt_of_not_le hn2
    have hd : bounceDepth tTurn T = 0 := bounceDepth_past hlt
    have hDepth' : T ≤ 0 := by
      rw [← hd]; exact hDepth
    cases T with
    | zero => exact Nat.not_lt_zero tTurn hT
    | succ T => exact Nat.not_succ_le_zero T hDepth'

/-- **The exhaustion tick is the turnaround.** Under the exponent bounce
schedule with `K ≥ 2`, horizon `T` is alive if and only if `T ≤ tTurn`.
Hence `t* := max {T : Alive K tTurn T} = tTurn`. -/
theorem exhaustion_tick_eq_turnaround {K : Nat} (hK : 2 ≤ K)
    (tTurn T : Nat) :
    Alive K tTurn T ↔ T ≤ tTurn := by
  apply Iff.intro
  · intro hA
    cases hdec : decide (T ≤ tTurn) with
    | true => exact of_decide_eq_true hdec
    | false =>
      have hgt : ¬ T ≤ tTurn := of_decide_eq_false hdec
      exact absurd hA (not_alive_past_turn hK tTurn T (lt_of_not_le hgt))
  · intro hT
    exact alive_upto_turn hK tTurn T hT

/-- The turnaround itself is alive (and is the maximum alive horizon). -/
theorem turnaround_alive {K : Nat} (hK : 2 ≤ K) (tTurn : Nat) :
    Alive K tTurn tTurn :=
  (exhaustion_tick_eq_turnaround hK tTurn tTurn).mpr (Nat.le_refl tTurn)

end Geom.Bounce

-- #print axioms
#print axioms Geom.Bounce.bounceDepth_asc
#print axioms Geom.Bounce.bounceDepth_turn
#print axioms Geom.Bounce.bounceDepth_past
#print axioms Geom.Bounce.bounceDepth_desc
#print axioms Geom.Bounce.pow_lt_succ
#print axioms Geom.Bounce.pow_le_pow_of_le
#print axioms Geom.Bounce.pow_lt_pow_of_lt
#print axioms Geom.Bounce.pow_le_pow_iff_le
#print axioms Geom.Bounce.alive_iff_le_depth
#print axioms Geom.Bounce.alive_upto_turn
#print axioms Geom.Bounce.two_mul_eq_add
#print axioms Geom.Bounce.add_sub_of_le
#print axioms Geom.Bounce.desc_le_implies_le_turn
#print axioms Geom.Bounce.not_alive_past_turn
#print axioms Geom.Bounce.exhaustion_tick_eq_turnaround
#print axioms Geom.Bounce.turnaround_alive
