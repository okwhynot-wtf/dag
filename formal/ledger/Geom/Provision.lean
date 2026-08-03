import Geom.Exhaustion

/-!
# Geom.Provision

Expanding conveyor: blank capacity adjoined at the merge rate sustains stream
muteness. Perpetual merging with a mute stream forces unbounded capacity.
-/

set_option linter.unusedSectionVars false

namespace Geom.Provision

open Geom.Exhaustion

/-! ### List helpers -/

/-- Appending `[]` on the right is the identity. -/
theorem append_nil : ∀ l : List α, l ++ [] = l := by
  intro l
  induction l with
  | nil => rfl
  | cons x xs ih =>
    show x :: (xs ++ []) = x :: xs
    rw [ih]

/-- Associativity of append, reproved locally. -/
theorem append_assoc : ∀ l m n : List α, (l ++ m) ++ n = l ++ (m ++ n) := by
  intro l m n
  induction l with
  | nil => rfl
  | cons x xs ih =>
    show x :: ((xs ++ m) ++ n) = x :: (xs ++ (m ++ n))
    rw [ih]

/-- Membership introduction for `map`, axiom-free. -/
theorem mem_map_intro (f : α → β) {a : α} :
    ∀ {l : List α}, a ∈ l → f a ∈ l.map f := by
  intro l
  induction l with
  | nil => intro h; cases h
  | cons x xs ih =>
    intro h
    cases h with
    | head => exact mem_head _ _
    | tail _ hm => exact mem_tail _ (ih hm)

/-- Membership introduction for `joinMap`, axiom-free. -/
theorem mem_joinMap_intro {f : α → List β} {a : α} {b : β} :
    ∀ {l : List α}, a ∈ l → b ∈ f a → b ∈ joinMap f l := by
  intro l
  induction l with
  | nil => intro h _; cases h
  | cons x xs ih =>
    intro ha hb
    cases ha with
    | head => exact mem_append_left (joinMap f xs) hb
    | tail _ hm => exact mem_append_right (ih hm hb) (f x)

/-- A join of blocks each of length exactly `N` over an index list of
length `L` has length exactly `L * N`. -/
theorem length_joinMap_eq {f : α → List β} {N : Nat} :
    ∀ {l : List α}, (∀ a, a ∈ l → (f a).length = N) →
      (joinMap f l).length = l.length * N := by
  intro l
  induction l with
  | nil =>
    intro _
    show 0 = 0 * N
    rw [Nat.zero_mul]
  | cons x xs ih =>
    intro h
    show (f x ++ joinMap f xs).length = (xs.length + 1) * N
    rw [length_append, h x (mem_head x xs),
        ih (fun a ha => h a (mem_tail x ha)), Nat.succ_mul,
        Nat.add_comm N (xs.length * N)]

/-- The fresh-choice count is exact: when every tick below `T`
schedules an alphabet of size exactly `K`, the run offers exactly
`K ^ T` fresh-choice vectors. Sharpens
`Geom.Exhaustion.freshVecs_length_ge` to an identity. -/
theorem freshVecs_length_eq {Eout : Type} (es : Nat → List Eout) {K : Nat} :
    ∀ T : Nat, (∀ t, t < T → (es t).length = K) →
      (freshVecs es T).length = K ^ T := by
  intro T
  induction T with
  | zero => intro _; rfl
  | succ T ih =>
    intro h
    show (joinMap (fun v => (es T).map (fun e => v ++ [e]))
      (freshVecs es T)).length = K ^ T * K
    rw [length_joinMap_eq (N := K) (fun v _ => by
          rw [length_map_eq]
          exact h T (Nat.lt_succ_self T)),
        ih (fun t ht => h t (Nat.lt_succ_of_lt ht))]

/-! ### Growth arithmetic: bounded capacity is outrun by `K ≥ 2` -/

/-- Positivity of powers of two, reproved locally. -/
theorem two_pow_pos : ∀ n : Nat, 0 < 2 ^ n := by
  intro n
  induction n with
  | zero => exact Nat.zero_lt_one
  | succ k ih =>
    show 0 < 2 ^ k * 2
    exact Nat.mul_pos ih (by decide)

/-- Every natural is outrun by its own power of two: `n < 2 ^ n`. -/
theorem lt_two_pow : ∀ n : Nat, n < 2 ^ n := by
  intro n
  induction n with
  | zero => exact Nat.zero_lt_one
  | succ k ih =>
    have h1 : k + 1 ≤ 2 ^ k := Nat.succ_le_of_lt ih
    have h2 : 2 ^ k < 2 ^ (k + 1) := by
      show 2 ^ k < 2 ^ k * 2
      have := Nat.lt_add_of_pos_right (n := 2 ^ k) (two_pow_pos k)
      rw [Nat.mul_comm, Nat.succ_mul, Nat.one_mul]
      exact this
    exact Nat.lt_of_le_of_lt h1 h2

/-- Base monotonicity of powers: for `2 ≤ K`, `2 ^ n ≤ K ^ n`. -/
theorem two_pow_le_pow {K : Nat} (hK : 2 ≤ K) :
    ∀ n : Nat, 2 ^ n ≤ K ^ n := by
  intro n
  induction n with
  | zero => exact Nat.le_refl 1
  | succ k ih =>
    show 2 ^ k * 2 ≤ K ^ k * K
    exact Nat.mul_le_mul ih hK

/-- **Growth outruns any bound.** For `K ≥ 2` and any capacity bound
`C`, the tick-`C` demand already exceeds it: `C < K ^ C`. -/
theorem capacity_lt_pow {K : Nat} (hK : 2 ≤ K) (C : Nat) : C < K ^ C :=
  Nat.lt_of_lt_of_le (lt_two_pow C) (two_pow_le_pow hK C)

/-! ### The expanding conveyor

The constructive witness of sufficiency. The environment splits as in
`LedgerExhaustion`: a stream slot `Eout` and an internal buffer, here
`List Eout` -- the archive as a growing tape. Each tick *adjoins* one
slot of capacity `|A|` (blank adjunction: the tape grows by one cell)
and files the tick's fresh unit into it; the stream slot ships the
constant `blank`. The system marches under any injective `g`. -/

variable {S Eout : Type}

/-- The expanding step: system marches under `g`, the stream slot is
constantly `blank` (mute), and the incoming fresh unit is filed at the
newly adjoined tape address. -/
def expandStep (g : S → S) (blank : Eout) :
    S × Eout × List Eout → S × Eout × List Eout :=
  fun p => (g p.1, blank, p.2.2 ++ [p.2.1])

/-- Iteration of the system march (the scheduled trajectory). -/
def gIter (g : S → S) (s0 : S) : Nat → S
  | 0 => s0
  | t + 1 => g (gIter g s0 t)

/-- The expanding step is injective whenever the march is: the adjoined
address recovers both the filed unit and the prior tape. -/
theorem expand_inj {g : S → S} (hg : ∀ a b : S, g a = g b → a = b)
    (blank : Eout) : Inj (expandStep g blank) := by
  intro a b h
  have h1 : g a.1 = g b.1 := congrArg (fun p => p.1) h
  have h3 : a.2.2 ++ [a.2.1] = b.2.2 ++ [b.2.1] :=
    congrArg (fun p => p.2.2) h
  match snoc_inj a.2.2 b.2.2 a.2.1 b.2.1 h3 with
  | ⟨hbuf, he⟩ => exact triple_ext (hg a.1 b.1 h1) he hbuf

section Conveyor

variable (g : S → S) (blank : Eout) (s0 : S) (A : List Eout)

/-- The expanding schedule: full alphabet every tick, capacity the
fresh-choice vectors themselves -- the tape states reachable by `t`
adjunctions. -/
def expandCaps : Nat → List (List Eout) := freshVecs (fun _ => A)

/-- **Every tick merges.** The scheduled fresh units all land the
system on the marched target, whatever the tape held: the `K`-merge
clause of the horizon schedule, satisfied at every tick. -/
theorem expand_merges_at : ∀ t : Nat,
    MergesAt (expandStep g blank) (gIter g s0) (fun _ => A)
      (expandCaps A) t :=
  fun _ _ _ _ _ => rfl

/-- **Every tick is fresh.** The stream slot ships the constant
`blank`: mute, whatever arrived and whatever the tape held. -/
theorem expand_fresh_at : ∀ t : Nat,
    FreshAt (expandStep g blank) (gIter g s0) (fun _ => A)
      (expandCaps A) t :=
  fun _ _ _ _ _ _ _ _ _ => rfl

/-- **Every tick is confined.** Filing the fresh unit at the adjoined
address lands the tape in the tick-`t+1` capacity: growth is exactly
what confinement costs. -/
theorem expand_confined : ∀ t : Nat,
    Confined (expandStep g blank) (gIter g s0) (fun _ => A)
      (expandCaps A) t :=
  fun _ _e he _i hi => mem_joinMap_intro hi (mem_map_intro _ he)

/-- **Capacity production.** Each tick multiplies capacity by the
adjunction rate `|A|`: one blank slot of `|A|` values adjoined per
tick. -/
theorem capacity_production : ∀ t : Nat,
    (expandCaps (Eout := Eout) A (t + 1)).length =
      (expandCaps A t).length * A.length :=
  fun _t => length_joinMap_eq (fun v _ => length_map_eq (fun e => v ++ [e]) A)

/-- **Exact capacity.** After `T` ticks of blank adjunction the
capacity is exactly `|A| ^ T`: the everywhere-saturated schedule,
production equal to demand. -/
theorem expand_capacity : ∀ T : Nat,
    (expandCaps (Eout := Eout) A T).length = A.length ^ T :=
  fun T => freshVecs_length_eq (fun _ => A) T (fun _ _ => rfl)

/-- **The alive set is all of ℕ.** The exhaustion bound
`K ^ T ≤ |caps T|` of the horizon clause holds at every horizon, with
equality: the exhaustion tick `t*` of `LedgerExhaustion` does not
exist for an expanding archive -- its Page time is at infinity. -/
theorem alive_everywhere : ∀ T : Nat,
    A.length ^ T ≤ (expandCaps (Eout := Eout) A T).length :=
  fun T => Nat.le_of_eq (expand_capacity A T).symm

/-- **Provision (sufficiency, packaged).** The expanding conveyor is
an injective joint step whose schedule merges the full alphabet at
every tick, keeps the stream mute at every tick, respects its own
growing capacity at every tick, and whose capacity meets the ledger
bound with equality at every horizon. Blank adjunction at rate
`K = |A|` sustains freshness forever. -/
theorem provision {g : S → S} (hg : ∀ a b : S, g a = g b → a = b)
    (blank : Eout) (s0 : S) (A : List Eout) :
    Inj (expandStep g blank)
    ∧ (∀ t, MergesAt (expandStep g blank) (gIter g s0) (fun _ => A)
        (expandCaps A) t)
    ∧ (∀ t, FreshAt (expandStep g blank) (gIter g s0) (fun _ => A)
        (expandCaps A) t)
    ∧ (∀ t, Confined (expandStep g blank) (gIter g s0) (fun _ => A)
        (expandCaps A) t)
    ∧ (∀ T, (expandCaps (Eout := Eout) A T).length = A.length ^ T) :=
  ⟨expand_inj hg blank, expand_merges_at g blank s0 A,
   expand_fresh_at g blank s0 A, expand_confined g blank s0 A,
   expand_capacity A⟩

/-! ### The adjunction identity: the archive is the transcript -/

/-- Threading the tape through a run appends the run: the expanding
conveyor's buffer evolution is concatenation. -/
theorem evolve_expand_append :
    ∀ (v : List Eout) (t : Nat) (i : List Eout),
      evolve (expandStep g blank) (gIter g s0) t i v = i ++ v := by
  intro v
  induction v with
  | nil => intro t i; exact (append_nil i).symm
  | cons e v' ih =>
    intro t i
    show evolve (expandStep g blank) (gIter g s0) (t + 1)
      (i ++ [e]) v' = i ++ (e :: v')
    rw [ih (t + 1) (i ++ [e]), append_assoc]
    rfl

/-- **The archive is the transcript.** From the blank tape, the archive
after any run of the expanding conveyor is the run's fresh-choice
vector, verbatim: the slot adjoined at tick `t` holds the tick-`t`
unit, forever. Registration is total, address-ordered, and coincides
with adjunction -- the fresh end of the archive is the birth of each
slot, not a boundary in time. -/
theorem archive_is_transcript (v : List Eout) :
    evolve (expandStep g blank) (gIter g s0) 0 [] v = v :=
  evolve_expand_append g blank s0 v 0 []

/-- Blankness at birth, counted: after `t` adjunctions the tape has
exactly `t` addresses -- the address written at tick `t` did not exist
before tick `t`. -/
theorem archive_length {t : Nat} {v : List Eout}
    (hv : v ∈ freshVecs (fun _ => A) t) :
    (evolve (expandStep g blank) (gIter g s0) 0 [] v).length = t := by
  rw [archive_is_transcript]
  exact freshVecs_length_mem (fun _ => A) hv

end Conveyor

/-! ### Necessity: eternal aliveness requires an expanding archive -/

section Necessity

variable {Eout Eint : Type}
variable (U : S × Eout × Eint → S × Eout × Eint)
variable (σ : Nat → S) (es : Nat → List Eout) (caps : Nat → List Eint)

/-- **Necessity (the headline).** A run that merges `K ≥ 2` scheduled
fresh units at the marginal at every tick, with a mute stream and a
confined buffer at every tick, has unbounded capacity: for every bound
`C`, tick `C` already exceeds it. Perpetual freshness under perpetual
merging *is* capacity production -- eternal aliveness requires an
expanding archive. -/
theorem eternal_aliveness_needs_expansion [DecidableEq Eint]
    (hU : Inj U) {K : Nat} (hK : 2 ≤ K)
    (hm : ∀ t, MergesAt U σ es caps t)
    (hf : ∀ t, FreshAt U σ es caps t)
    (hc : ∀ t, Confined U σ es caps t)
    (hdes : ∀ t, Distinct (es t))
    (hKlen : ∀ t, K ≤ (es t).length)
    (i₀ : Eint) (hi₀ : i₀ ∈ caps 0) :
    ∀ C : Nat, C < (caps C).length := by
  intro C
  have hex : K ^ C ≤ (caps C).length :=
    exhaustion U σ es caps hU C K (fun t _ => hm t) (fun t _ => hf t)
      (fun t _ => hc t) (fun t _ => hdes t) (fun t _ => hKlen t) i₀ hi₀
  exact Nat.lt_of_lt_of_le (capacity_lt_pow hK C) hex

/-- **Necessity, contrapositive (no static eternal aliveness).** A run
whose capacity is bounded by `C` throughout, merging `K ≥ 2` scheduled
fresh units per tick with a confined buffer, loses stream-freshness by
tick `C`: at some tick `t < C` the stream slot distinguishes a merged
datum. The failing tick is found by decidable bounded search
(`Geom.Exhaustion.freshness_fails`); no classical axioms. -/
theorem no_static_eternal_aliveness [DecidableEq Eout] [DecidableEq Eint]
    (hU : Inj U) {K C : Nat} (hK : 2 ≤ K)
    (hm : ∀ t, MergesAt U σ es caps t)
    (hc : ∀ t, Confined U σ es caps t)
    (hdes : ∀ t, Distinct (es t))
    (hKlen : ∀ t, K ≤ (es t).length)
    (hbound : ∀ t, (caps t).length ≤ C)
    (i₀ : Eint) (hi₀ : i₀ ∈ caps 0) :
    ∃ t, t < C ∧ ∃ e, e ∈ es t ∧ ∃ e', e' ∈ es t ∧
      ∃ i, i ∈ caps t ∧ ∃ i', i' ∈ caps t ∧
        (U (σ t, e, i)).2.1 ≠ (U (σ t, e', i')).2.1 :=
  freshness_fails U σ es caps hU C K (fun t _ => hm t) (fun t _ => hc t)
    (fun t _ => hdes t) (fun t _ => hKlen t) i₀ hi₀
    (Nat.lt_of_le_of_lt (hbound C) (capacity_lt_pow hK C))

end Necessity

/-!
# Geom.Provision

Expanding conveyor: blank capacity adjoined at the merge rate sustains stream
muteness. Perpetual merging with a mute stream forces unbounded capacity.
-/

/-- The expanding tick, Budget orientation: the merged fiber is the
incoming fresh unit; the record is the outgoing (stream, tape) pair. -/
def expandTick (g : S → S) (blank : Eout) :
    Eout × (S × List Eout) → S × (Eout × List Eout) :=
  fun p => (g p.2.1, blank, p.2.2 ++ [p.1])

/-- The expanding tick is injective (for an injective march). -/
theorem expandTick_inj {g : S → S} (hg : ∀ a b : S, g a = g b → a = b)
    (blank : Eout) :
    ∀ a b : Eout × (S × List Eout),
      expandTick g blank a = expandTick g blank b → a = b := by
  intro a b h
  have h1 : g a.2.1 = g b.2.1 := congrArg (fun p => p.1) h
  have h3 : a.2.2 ++ [a.1] = b.2.2 ++ [b.1] :=
    congrArg (fun p => p.2.2) h
  match snoc_inj a.2.2 b.2.2 a.1 b.1 h3 with
  | ⟨hbuf, he⟩ =>
    match a, b with
    | (e, s, buf), (e', s', buf') =>
      cases he
      cases hbuf
      cases hg s s' h1
      rfl

/-- The per-tick record alphabet actually consumed by the expanding
tick at context `(s, buf)`. -/
def expandRecords (blank : Eout) (buf : List Eout) (A : List Eout) :
    List (Eout × List Eout) :=
  A.map (fun e => (blank, buf ++ [e]))

/-- The consumed alphabet has exactly `|A|` letters: what a tick mints
(one slot of `|A|` values) is exactly what its records consume. -/
theorem expandRecords_length (blank : Eout) (buf : List Eout)
    (A : List Eout) :
    (expandRecords blank buf A).length = A.length :=
  length_map_eq _ A

end Geom.Provision

-- #print axioms
#print axioms Geom.Provision.append_nil
#print axioms Geom.Provision.append_assoc
#print axioms Geom.Provision.mem_map_intro
#print axioms Geom.Provision.mem_joinMap_intro
#print axioms Geom.Provision.length_joinMap_eq
#print axioms Geom.Provision.freshVecs_length_eq
#print axioms Geom.Provision.two_pow_pos
#print axioms Geom.Provision.lt_two_pow
#print axioms Geom.Provision.two_pow_le_pow
#print axioms Geom.Provision.capacity_lt_pow
#print axioms Geom.Provision.expand_inj
#print axioms Geom.Provision.expand_merges_at
#print axioms Geom.Provision.expand_fresh_at
#print axioms Geom.Provision.expand_confined
#print axioms Geom.Provision.capacity_production
#print axioms Geom.Provision.expand_capacity
#print axioms Geom.Provision.alive_everywhere
#print axioms Geom.Provision.provision
#print axioms Geom.Provision.evolve_expand_append
#print axioms Geom.Provision.archive_is_transcript
#print axioms Geom.Provision.archive_length
#print axioms Geom.Provision.eternal_aliveness_needs_expansion
#print axioms Geom.Provision.no_static_eternal_aliveness
#print axioms Geom.Provision.expandTick_inj
#print axioms Geom.Provision.expandRecords_length
