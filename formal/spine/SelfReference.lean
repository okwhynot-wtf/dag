import Interior
import OmegaDuration
import Density
import Ladder
import Diagonal
import TwoCycle

/-!
# SelfReference — corpus representing the corpus (Lawvere, not Gödel)

Reflexive application of the seal at **one** junction: the corpus as
mathematical object representing its own predicate structure.

## Junction discipline (five candidates; one chosen)

| Candidate | Status |
|---|---|
| World (if adopted) | refused — instantiation / dictionary, not spine |
| Corpus as mathematical object | **chosen** — this module |
| Symbolic law document | refused — prose enacting the ladder; observation only |
| Lean repository (git tree) | refused — host artifact, not an object language |
| Host logic under Lean | refused — Gödel's business; category error |

Further refusal: arithmetised Gödel (syntax + provability predicate).
The corpus refuses numbers-from-Bool as load-bearing metaphysics; the
semantic route (predicates, self-readings) already yields incompleteness
without a proof predicate. Meta-theory here is Lawvere throughout.

## Content

* `SelfReading` — `L_k → (L_k → Bool)`
* `seal_self` — dodge exists; no complete self-reading at any level
* `deficit_count` / `deficit_vanishes` — Cantor measure: names ≪ predicates
* `FairSchedule` — flagged enumeration **policy**; completeness-in-the-limit
* `lag_theorem` — finishing a self-portrait leaves a larger silence ahead
* `dodge_gauge_covariant` — label-swap covariance
* `corpus_not_universal` — □(sayable) ∧ ¬□(sayable now); colimit ≠ rung

No declared axioms.
-/
namespace SelfReference

open Diagonal
open Density
open Ladder

/-! ## Self-reading at a level -/

/-- A self-reading at level `k`: each name is assigned a Bool-predicate
    on the same level. Semantic representation — not a formula code. -/
def SelfReading (k : Nat) : Type :=
  Level k → Level k → Bool

/-- Unsayable mass: predicates minus name slots (Nat difference). -/
def unsayable (k : Nat) : Nat :=
  predicateCount k - levelCard k

/-! ## Seal on self-readings -/

/-- **seal_self.** Every self-reading misses its dodge. Banked on
    `Interior.self_opacity` / Lawvere. -/
theorem seal_self (k : Nat) (r : SelfReading k) :
    ¬ Interior.Articulates r (dodge r) :=
  Interior.self_opacity not TwoCycle.bool_fundamental.1 r

/-- No self-reading is point-surjective onto predicates of its level. -/
theorem incompleteness_unconditional (k : Nat) (r : SelfReading k) :
    ¬ PointSurjective r :=
  seal_bool r

/-- Canonical ladder self-reading is incomplete. -/
theorem ladder_rep_incomplete (k : Nat) :
    ¬ Interior.Articulates (rep k) (dodge (rep k)) ∧
    ¬ PointSurjective (rep k) :=
  ⟨seal_self k (rep k), incompleteness_unconditional k (rep k)⟩

/-! ## Arithmetic helpers -/

theorem pow2_succ (n : Nat) : 2 ^ (n + 1) = 2 * 2 ^ n := by
  rw [Nat.pow_succ', Nat.mul_comm]

/-- `n < 2^n` for `n ≥ 1`. -/
theorem n_lt_pow2 (n : Nat) (h : 1 ≤ n) : n < 2 ^ n := by
  match n with
  | 0 => cases h
  | n' + 1 =>
    induction n' with
    | zero => decide
    | succ n' ih =>
      have ih' : n' + 1 < 2 ^ (n' + 1) := ih (Nat.succ_le_succ (Nat.zero_le _))
      have hle : n' + 2 ≤ 2 ^ (n' + 1) := Nat.succ_le_of_lt ih'
      have hrw : 2 ^ (n' + 2) = 2 * 2 ^ (n' + 1) := pow2_succ (n' + 1)
      have hone : 0 < 2 ^ (n' + 1) := Nat.pow_pos (by decide : 0 < 2)
      have hlt : 2 ^ (n' + 1) < 2 * 2 ^ (n' + 1) := by
        have : 1 * 2 ^ (n' + 1) < 2 * 2 ^ (n' + 1) :=
          Nat.mul_lt_mul_of_pos_right (by decide : 1 < 2) hone
        simpa [Nat.one_mul] using this
      exact Nat.lt_of_le_of_lt hle (hrw ▸ hlt)

/-- `t ≤ 2^t`. -/
theorem t_le_pow2 : ∀ t : Nat, t ≤ 2 ^ t
  | 0 => by decide
  | 1 => by decide
  | t + 2 => by
    have ih : t + 1 ≤ 2 ^ (t + 1) := t_le_pow2 (t + 1)
    have hle : t + 2 ≤ 2 ^ (t + 1) + 1 := Nat.succ_le_succ ih
    have hone : 1 ≤ 2 ^ (t + 1) := Nat.succ_le_of_lt (Nat.pow_pos (by decide : 0 < 2))
    have hbound : 2 ^ (t + 1) + 1 ≤ 2 * 2 ^ (t + 1) := by
      have : 2 ^ (t + 1) + 1 ≤ 2 ^ (t + 1) + 2 ^ (t + 1) :=
        Nat.add_le_add_left hone _
      simpa [Nat.two_mul] using this
    exact Nat.le_trans hle (by simpa [pow2_succ] using hbound)

/-- `2*t + 3 ≤ 2^(t+2)`. -/
theorem two_mul_add3_le_pow : ∀ t : Nat, 2 * t + 3 ≤ 2 ^ (t + 2)
  | 0 => by decide
  | t + 1 => by
    have ih := two_mul_add3_le_pow t
    have lhs : 2 * (t + 1) + 3 = 2 * t + 3 + 2 := by
      simp [Nat.mul_succ, Nat.add_assoc]
    have hrw : 2 ^ (t + 3) = 2 ^ (t + 2) + 2 ^ (t + 2) := by
      rw [pow2_succ, Nat.two_mul]
    rw [lhs, hrw]
    refine Nat.add_le_add ih ?_
    have : 2 ^ 1 ≤ 2 ^ (t + 2) :=
      Nat.pow_le_pow_right (by decide : 0 < 2) (Nat.succ_le_succ (Nat.zero_le _))
    simpa using this

/-- Quadratic bound: `m*(m+2) < 2^(m+2)`. -/
theorem quad_lt_pow : ∀ m : Nat, m * (m + 2) < 2 ^ (m + 2)
  | 0 => by decide
  | m + 1 => by
    have ih := quad_lt_pow m
    have hex : (m + 1) * (m + 3) = m * (m + 2) + (m + 2) + (m + 1) := by
      calc
        (m + 1) * (m + 3)
            = (m + 1) * (m + 2) + (m + 1) := by
              rw [show m + 3 = (m + 2) + 1 from rfl, Nat.mul_add, Nat.mul_one]
        _ = m * (m + 2) + (m + 2) + (m + 1) := by
              rw [Nat.succ_mul, Nat.add_assoc]
    have hsum :
        m * (m + 2) + (m + 2) + (m + 1) < 2 ^ (m + 2) + (m + 2) + (m + 1) :=
      Nat.add_lt_add_right (Nat.add_lt_add_right ih (m + 2)) (m + 1)
    have hroom : (m + 2) + (m + 1) ≤ 2 ^ (m + 2) := by
      simpa [Nat.two_mul, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
        two_mul_add3_le_pow m
    have hbound : 2 ^ (m + 2) + (m + 2) + (m + 1) ≤ 2 ^ (m + 3) := by
      have : 2 ^ (m + 2) + ((m + 2) + (m + 1)) ≤ 2 ^ (m + 2) + 2 ^ (m + 2) :=
        Nat.add_le_add_left hroom _
      simpa [pow2_succ, Nat.two_mul, Nat.add_assoc] using this
    exact Nat.lt_of_lt_of_le (hex ▸ hsum) hbound

/-! ## Deficit count (Cantor measure) -/

theorem names_eq (k : Nat) : levelCard k = k + 2 :=
  levelCard_eq k

theorem predicates_eq (k : Nat) : predicateCount k = 2 ^ (k + 2) :=
  predicateCount_eq k

/-- Names are strictly fewer than predicates at every level. -/
theorem deficit_strict (k : Nat) :
    levelCard k < predicateCount k := by
  rw [levelCard_eq, predicateCount_eq]
  exact n_lt_pow2 (k + 2) (Nat.succ_le_succ (Nat.zero_le _))

theorem unsayable_pos (k : Nat) : 0 < unsayable k :=
  Nat.sub_pos_of_lt (deficit_strict k)

/-- **deficit_count.** Name supply vs predicate supply at level `k`. -/
theorem deficit_count (k : Nat) :
    levelCard k = k + 2 ∧
    predicateCount k = 2 ^ (k + 2) ∧
    levelCard k < predicateCount k ∧
    0 < unsayable k :=
  ⟨names_eq k, predicates_eq k, deficit_strict k, unsayable_pos k⟩

/-- Concrete vanishing: once `k ≥ N`, `N` times name-count undershoots predicates. -/
theorem mul_level_lt_pred (N k : Nat) (h : N ≤ k) :
    N * levelCard k < predicateCount k := by
  rw [levelCard_eq, predicateCount_eq]
  exact Nat.lt_of_le_of_lt (Nat.mul_le_mul_right (k + 2) h) (quad_lt_pow k)

/-- **deficit_vanishes.** For any scale `N`, past a threshold almost all
    predicates of the present level are unnamed at the present level. -/
theorem deficit_vanishes (N : Nat) :
    ∃ K, ∀ k, K ≤ k → N * levelCard k < predicateCount k :=
  ⟨N, fun k hk => mul_level_lt_pred N k hk⟩

/-! ## Fair naming schedule (policy, flagged) -/

/-- Enumeration **policy**: assign each predicate-index of level `k` a
    stage at which it is named. Not a law of the spine — a schedule.
    Completeness-in-the-limit is schedule-relative; incompleteness now
    is not. -/
structure FairSchedule (k : Nat) where
  /-- Predicate-index ↦ naming stage. -/
  stageOf : Nat → Nat
  /-- Naming occurs on the ascent at or after `k`. -/
  stage_ge : ∀ i, i < predicateCount k → k ≤ stageOf i
  /-- Distinct indices receive distinct stages. -/
  inj : ∀ i j, i < predicateCount k → j < predicateCount k →
          stageOf i = stageOf j → i = j

/-- Minimal fair schedule: name index `i` at stage `k + i`. -/
def minimalSchedule (k : Nat) : FairSchedule k where
  stageOf := fun i => k + i
  stage_ge := fun _i _hi => Nat.le_add_right k _
  inj := fun _i _j _hi _hj h => Nat.add_left_cancel h

/-- Completeness-in-the-limit is available as a policy (existence of a
    fair schedule), not as an unconditional law. -/
theorem completeness_in_limit_is_policy (k : Nat) :
    ∃ σ : FairSchedule k, ∀ i, i < predicateCount k → k ≤ σ.stageOf i :=
  ⟨minimalSchedule k, (minimalSchedule k).stage_ge⟩

/-- Under a fair schedule every predicate-index of level `k` is named at
    some finite later (or present) stage. -/
theorem eventually_sayable (k : Nat) (σ : FairSchedule k) :
    ∀ i, i < predicateCount k → ∃ t, σ.stageOf i = t ∧ k ≤ t := by
  intro i hi
  exact ⟨σ.stageOf i, rfl, σ.stage_ge i hi⟩

/-- Asymmetry package: incompleteness now is unconditional; eventual
    completeness is a policy. -/
theorem sayability_asymmetry (k : Nat) (r : SelfReading k) :
    (¬ PointSurjective r) ∧
    (∃ σ : FairSchedule k, ∀ i, i < predicateCount k → k ≤ σ.stageOf i) :=
  ⟨incompleteness_unconditional k r, completeness_in_limit_is_policy k⟩

/-- Minimal schedule reaches the one-name-per-tick completion bound. -/
theorem minimal_reaches_bound (k : Nat) :
    ∃ i, i < predicateCount k ∧
      (minimalSchedule k).stageOf i = k + predicateCount k - 1 := by
  refine ⟨predicateCount k - 1, ?_, ?_⟩
  · have hP : 0 < predicateCount k := by
      rw [predicateCount_eq]; exact Nat.pow_pos (by decide : 0 < 2)
    exact Nat.sub_lt hP (by decide : 0 < 1)
  · -- k+(P-1) = k+P-1
    simp only [minimalSchedule]
    have hP : 1 ≤ predicateCount k := by
      rw [predicateCount_eq]
      exact Nat.succ_le_of_lt (Nat.pow_pos (by decide : 0 < 2))
    exact (Nat.add_sub_assoc hP k).symm

/-! ## Articulation capacity (names behind the schedule)

`eventually_sayable` alone is a scheduling claim. The theorems below
ground it: one fresh name per tick means that by the completion bound
the ladder's fresh stock exactly covers the predicate supply of level
`k`, and an explicit injective allocation hands each predicate index a
distinct fresh slot, available by one tick past its stage. This is
capacity + assignment, not semantic interpretation; the policy flag on
`FairSchedule` stands. -/

/-- Fresh names accumulated between level `k` and level `m`. -/
def freshNames (k m : Nat) : Nat :=
  levelCard m - levelCard k

/-- One fresh name per tick: the stock grows by exactly the tick count. -/
theorem levelCard_add (k d : Nat) :
    levelCard (k + d) = levelCard k + d := by
  induction d with
  | zero => rfl
  | succ d ih =>
    have hstep : levelCard (k + (d + 1)) = levelCard (k + d) + 1 := rfl
    rw [hstep, ih]
    rfl

/-- **articulation_capacity.** At the completion bound
    `m = k + predicateCount k`, fresh names exactly cover the predicate
    supply of level `k`. -/
theorem articulation_capacity (k : Nat) :
    freshNames k (k + predicateCount k) = predicateCount k := by
  dsimp [freshNames]
  rw [levelCard_add]
  exact Nat.add_sub_cancel_left _ _

/-- Name-slot allocation: predicate index `i` of level `k` is assigned
    the `i`-th fresh name. -/
def nameSlot (k i : Nat) : Nat := levelCard k + i

/-- Slots are fresh: they lie past every name present at level `k`. -/
theorem nameSlot_fresh (k i : Nat) : levelCard k ≤ nameSlot k i :=
  Nat.le_add_right _ _

/-- Distinct predicate indices receive distinct slots. -/
theorem nameSlot_inj (k : Nat) :
    ∀ i j, nameSlot k i = nameSlot k j → i = j :=
  fun _ _ h => Nat.add_left_cancel h

/-- Every allocated slot exists within the level reached at the
    completion bound. -/
theorem nameSlot_in_range (k : Nat) :
    ∀ i, i < predicateCount k →
      nameSlot k i < levelCard (k + predicateCount k) := by
  intro i hi
  rw [levelCard_add]
  exact Nat.add_lt_add_left hi _

/-- **eventual_sayability_has_names.** The minimal fair schedule is
    backed by actual name capacity: each predicate index of level `k`
    owns a distinct fresh slot, in range at the completion bound and
    available by one tick past its stage. -/
theorem eventual_sayability_has_names (k : Nat) :
    (∀ i, i < predicateCount k →
      levelCard k ≤ nameSlot k i ∧
      nameSlot k i < levelCard (k + predicateCount k) ∧
      nameSlot k i < levelCard ((minimalSchedule k).stageOf i + 1)) ∧
    (∀ i j, nameSlot k i = nameSlot k j → i = j) := by
  refine ⟨fun i hi => ⟨nameSlot_fresh k i, nameSlot_in_range k i hi, ?_⟩,
    nameSlot_inj k⟩
  show levelCard k + i < levelCard (k + (i + 1))
  rw [levelCard_add]
  exact Nat.lt_succ_self _

/-! ## Lag theorem -/

/-- Lag arithmetic at the canonical completion lower bound
    `m = k + predicateCount k` (one new name per tick after `k`). -/
theorem lag_at_bound (k : Nat) :
    unsayable (k + predicateCount k) > predicateCount k := by
  have hP : predicateCount k = 2 ^ (k + 2) := predicateCount_eq k
  -- Work at the concrete Nat level `m = k + 2^(k+2)`.
  let m := k + 2 ^ (k + 2)
  have hm2 : m + 2 = (k + 2) + 2 ^ (k + 2) := by
    dsimp [m]
    rw [Nat.add_assoc, Nat.add_comm (2 ^ (k + 2)) 2, ← Nat.add_assoc]
  have hpow : 2 ^ (m + 2) = 2 ^ (k + 2) * 2 ^ (2 ^ (k + 2)) := by
    rw [hm2, Nat.pow_add]
  have h16 : 16 ≤ 2 ^ (2 ^ (k + 2)) := by
    have h4 : 4 ≤ 2 ^ (k + 2) :=
      Nat.pow_le_pow_right (by decide : 0 < 2)
        (Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le _)))
    exact Nat.pow_le_pow_right (by decide : 0 < 2) h4
  have hge : 16 * 2 ^ (k + 2) ≤ 2 ^ (m + 2) := by
    rw [hpow, Nat.mul_comm]; exact Nat.mul_le_mul_left _ h16
  have hk2 : k + 2 ≤ 2 ^ (k + 2) := t_le_pow2 (k + 2)
  have hm2_le : m + 2 ≤ 2 * 2 ^ (k + 2) := by
    rw [hm2, Nat.two_mul]; exact Nat.add_le_add hk2 (Nat.le_refl _)
  have hleft : 2 ^ (k + 2) + (m + 2) ≤ 3 * 2 ^ (k + 2) := by
    have h := Nat.add_le_add_left hm2_le (2 ^ (k + 2))
    -- 2^n + 2*(2^n) = 3*(2^n)
    have hEq : 2 ^ (k + 2) + 2 * 2 ^ (k + 2) = 3 * 2 ^ (k + 2) := by
      -- 1·a + 2·a = (1+2)·a
      simpa [Nat.one_mul] using (Nat.add_mul 1 2 (2 ^ (k + 2))).symm
    exact hEq ▸ h
  have h3lt16 : 3 * 2 ^ (k + 2) < 16 * 2 ^ (k + 2) :=
    Nat.mul_lt_mul_of_pos_right (by decide : 3 < 16)
      (Nat.pow_pos (by decide : 0 < 2))
  have hstrict : 2 ^ (k + 2) + (m + 2) < 2 ^ (m + 2) :=
    Nat.lt_of_le_of_lt hleft (Nat.lt_of_lt_of_le h3lt16 hge)
  have hmain : 2 ^ (k + 2) < 2 ^ (m + 2) - (m + 2) :=
    Nat.lt_sub_of_add_lt hstrict
  -- Transport back to `unsayable`.
  dsimp [unsayable]
  rw [levelCard_eq, hP, predicateCount_eq]
  -- goal: 2^(m+2) - (m+2) > 2^(k+2)  with m = k+2^(k+2)
  dsimp [m] at hmain ⊢
  exact hmain

/-- **lag_theorem.** Finishing a full naming of level-`k` predicates
    (under the one-name-per-tick lower bound) lands at a level whose
    unsayable mass exceeds the entire predicate supply of the past. -/
theorem lag_theorem (k : Nat) :
    unsayable (k + predicateCount k) > predicateCount k :=
  lag_at_bound k

/-- Restless quantified: the lag recedes — unsayable mass at the
    completion bound strictly exceeds unsayable mass at `k`. -/
theorem lag_recedes (k : Nat) :
    unsayable k < unsayable (k + predicateCount k) := by
  have h := lag_theorem k
  have hlt : unsayable k < predicateCount k := by
    rw [unsayable]
    have hp : 0 < predicateCount k := Nat.zero_lt_of_lt (deficit_strict k)
    have hc : 0 < levelCard k := by
      rw [levelCard_eq]; exact Nat.succ_pos _
    exact Nat.sub_lt hp hc
  exact Nat.lt_trans hlt h

/-! ## Gauge covariance -/

/-- Dodge commutes with pole/label swap on predicate values. -/
theorem dodge_gauge_covariant {A : Type} (r : A → A → Bool) (x : A) :
    dodge (fun a b => !(r a b)) x = !(dodge r x) :=
  rfl

/-! ## Assembly: corpus_not_universal -/

/-- **corpus_not_universal.** No level is a complete self-description.
    Eventual sayability is policy-shaped; present incompleteness is not.
    The only complete description of the system is the system; the
    colimit is duration, not a rung — mirroring
    `□(ascent) ∧ ¬□(direction)` as `□(sayable) ∧ ¬□(sayable now)`. -/
theorem corpus_not_universal :
    (∀ k (r : SelfReading k), ¬ PointSurjective r) ∧
    (∀ k (r : SelfReading k), ¬ Interior.Articulates r (dodge r)) ∧
    (∀ k, levelCard k < predicateCount k) ∧
    (∀ N, ∃ K, ∀ k, K ≤ k → N * levelCard k < predicateCount k) ∧
    (∀ k, ∃ σ : FairSchedule k,
      ∀ i, i < predicateCount k → k ≤ σ.stageOf i) ∧
    (∀ k, unsayable (k + predicateCount k) > predicateCount k) ∧
    (∀ k, unsayable k < unsayable (k + predicateCount k)) ∧
    (∀ k, ¬ ∃ (f : Limit.LevelOmega → Level k),
      ∀ x y, f x = f y → x = y) ∧
    (∀ {A : Type} (r : A → A → Bool) (x : A),
      dodge (fun a b => !(r a b)) x = !(dodge r x)) :=
  ⟨fun k r => incompleteness_unconditional k r,
   fun k r => seal_self k r,
   deficit_strict,
   deficit_vanishes,
   completeness_in_limit_is_policy,
   lag_theorem,
   lag_recedes,
   OmegaDuration.omega_not_a_rung,
   fun r x => dodge_gauge_covariant r x⟩

/-- Package aligned with the MetaProblem triad columns. -/
theorem meta_triad_quantitative (k : Nat) :
    (¬ Interior.Articulates (rep k) (dodge (rep k))) ∧
    (unsayable (k + predicateCount k) > predicateCount k) ∧
    (unsayable k < unsayable (k + predicateCount k)) ∧
    (¬ PointSurjective (rep k)) :=
  ⟨seal_self k (rep k), lag_theorem k, lag_recedes k,
   incompleteness_unconditional k (rep k)⟩

#print axioms SelfReference.seal_self
#print axioms SelfReference.deficit_count
#print axioms SelfReference.deficit_vanishes
#print axioms SelfReference.completeness_in_limit_is_policy
#print axioms SelfReference.articulation_capacity
#print axioms SelfReference.eventual_sayability_has_names
#print axioms SelfReference.lag_theorem
#print axioms SelfReference.corpus_not_universal
#print axioms SelfReference.meta_triad_quantitative

end SelfReference
