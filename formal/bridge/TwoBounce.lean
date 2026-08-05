import Orbit
import Density
import Geom.Registration

/-!
# TwoBounce — I-1 losslessness as two arena bounces

Classical fact (finite carriers): a self-map is bijective iff it factors as
a composition of two involutions. Spine acts are involutions
(`SymmetricStep`); ledger joint steps `U` are forward-composing.

Results:
* involution ⇒ lossless ⇒ ¬Erasing (spine packaging)
* two-bounce ⇒ `Lossless` / product-`Inj` (converse half)
* existence when `U` is already an involution (`U = U ∘ id`)
* existence on `Bool` (every injection is an involution)
* existence for ledger `swapStep`
* existence for every injection on `Fin n` (cycle-wise reflect)

Also:
* canonicity fails (essential non-uniqueness of `(φ, σ)`)
* involutive reordering is T-7-shaped; Fin-3 axis choice is a larger
  factorization gauge, not a second dictionary ℤ/2 face
* factor-swap covers step reversal (`channel_swap_is_reversal`): labels
  conventional, exchange real
* the `Fin n` construction is computable: collisions, periods, basepoints,
  and indices are extracted by bounded structural search; `factor_fin` and
  `i1_two_bounce_fragment` are axiom-free (no `Classical.choice`, no
  `propext`, no `Quot.sound`); the only remaining `propext` in this file
  sits in the `Fin 3` gauge exhibits (literal-pattern matcher) and the
  leaf lemma `iter_mod_period`
-/
namespace Bridge.TwoBounce

open Orbit

/-! ## Involutions -/

/-- An involution: `f ∘ f = id`. Spine `SymmetricStep` is this shape. -/
def IsInvolution {α : Type} (f : α → α) : Prop :=
  ∀ x, f (f x) = x

theorem involution_of_symmetric {α : Type} (act : α → α)
    (hs : SymmetricStep act) : IsInvolution act :=
  (symmetricStep_iff_involutive act).mp hs

theorem symmetric_of_involution {α : Type} (act : α → α)
    (h : IsInvolution act) : SymmetricStep act :=
  (symmetricStep_iff_involutive act).mpr h

/-- Involutions are injective (= lossless). -/
theorem involution_injective {α : Type} (f : α → α) (h : IsInvolution f) :
    Lossless f := by
  intro x y heq
  have := congrArg f heq
  rw [h x, h y] at this
  exact this

/-- Involutive acts cannot erase. -/
theorem involution_not_erasing {α : Type} (f : α → α) (h : IsInvolution f) :
    ¬ Erasing f := by
  intro ⟨x, y, hne, heq⟩
  exact hne (involution_injective f h x y heq)

/-- Spine packaging: `SymmetricStep` excludes `Erasing`. -/
theorem symmetric_excludes_erase {α : Type} (act : α → α)
    (hs : SymmetricStep act) : ¬ Erasing act :=
  involution_not_erasing act (involution_of_symmetric act hs)

/-! ## Two-bounce factorisation -/

/-- Witness that `U` factors as `σ ∘ φ` with both factors involutions. -/
structure TwoBounceFactor {α : Type} (U : α → α) where
  /-- First bounce. -/
  φ : α → α
  /-- Second bounce. -/
  σ : α → α
  φ_inv : IsInvolution φ
  σ_inv : IsInvolution σ
  factor : ∀ x, U x = σ (φ x)

/-- Converse: two-bounce form ⇒ lossless. -/
theorem lossless_of_two_bounce {α : Type} (U : α → α)
    (f : TwoBounceFactor U) : Lossless U := by
  intro a b h
  have hσ : f.σ (f.φ a) = f.σ (f.φ b) := by
    rw [← f.factor a, ← f.factor b, h]
  have hφ : f.φ a = f.φ b := involution_injective f.σ f.σ_inv _ _ hσ
  exact involution_injective f.φ f.φ_inv _ _ hφ

/-- On a product carrier, two-bounce ⇒ ledger `Inj`. -/
theorem inj_of_two_bounce {S E : Type} (U : S × E → S × E)
    (f : TwoBounceFactor U) : Geom.Registration.Inj U :=
  lossless_of_two_bounce U f

/-- Any involution is already a two-bounce (`U = U ∘ id`). -/
def factor_involution {α : Type} (U : α → α) (h : IsInvolution U) :
    TwoBounceFactor U where
  φ := id
  σ := U
  φ_inv := fun _ => rfl
  σ_inv := h
  factor := fun _ => rfl

/-- Reverse packing of an involution (`U = id ∘ U`). -/
def factor_involution_rev {α : Type} (U : α → α) (h : IsInvolution U) :
    TwoBounceFactor U where
  φ := U
  σ := id
  φ_inv := h
  σ_inv := fun _ => rfl
  factor := fun _ => rfl

/-! ## `Bool` and ledger examples -/

/-- Endomap injectivity (carrier-agnostic). -/
def EndoInj {α : Type} (U : α → α) : Prop :=
  ∀ a b, U a = U b → a = b

theorem bool_inj_involution (U : Bool → Bool) (h : EndoInj U) :
    IsInvolution U := by
  intro x
  cases hf : U false with
  | false =>
    cases ht : U true with
    | false =>
      have : false = true := h false true (hf.trans ht.symm)
      cases this
    | true =>
      cases x with
      | false => rw [hf, hf]
      | true => rw [ht, ht]
  | true =>
    cases ht : U true with
    | false =>
      cases x with
      | false => rw [hf, ht]
      | true => rw [ht, hf]
    | true =>
      have : false = true := h false true (hf.trans ht.symm)
      cases this

def factor_bool (U : Bool → Bool) (h : EndoInj U) :
    TwoBounceFactor U :=
  factor_involution U (bool_inj_involution U h)

theorem swapStep_involution :
    IsInvolution Geom.Registration.swapStep := by
  intro p; cases p; rfl

def factor_swapStep : TwoBounceFactor Geom.Registration.swapStep :=
  factor_involution _ swapStep_involution

/-! ## `Fin n`: cycle-wise reflect -/

/-! ### Axiom-free `Nat` subtraction toolkit

The current core toolchain proves several subtraction and modulus lemmas
by automation that deposits `propext` in their footprint. The variants
below are proved from `rfl`-grade primitives (`Nat.le.dest`,
`Nat.succ_sub_succ`, `Nat.sub_succ`, `Nat.add_assoc`), so every
downstream declaration in this file can stay axiom-free. -/

theorem nat_sub_self_add (n m : Nat) : (n + m) - m = n := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [Nat.add_succ, Nat.succ_sub_succ]
    exact ih

theorem nat_add_sub_cancel_left (n m : Nat) : (n + m) - n = m := by
  rw [Nat.add_comm]
  exact nat_sub_self_add m n

theorem nat_add_one_right (n m : Nat) : n + (m + 1) = (n + m) + 1 :=
  Nat.add_succ n m

theorem nat_sub_one_right (n m : Nat) : n - (m + 1) = n - m - 1 :=
  Nat.sub_succ n m

theorem nat_sub_add_cancel {a b : Nat} (h : a ≤ b) : b - a + a = b := by
  obtain ⟨k, hk⟩ := Nat.le.dest h
  subst hk
  rw [nat_add_sub_cancel_left]
  exact Nat.add_comm k a

theorem nat_add_sub_of_le {a b : Nat} (h : a ≤ b) : a + (b - a) = b := by
  obtain ⟨k, hk⟩ := Nat.le.dest h
  subst hk
  rw [nat_add_sub_cancel_left]

theorem nat_sub_pos_of_lt {a b : Nat} (h : a < b) : 0 < b - a := by
  obtain ⟨k, hk⟩ := Nat.le.dest h
  subst hk
  rw [Nat.succ_add, ← Nat.add_succ, nat_add_sub_cancel_left]
  exact Nat.succ_pos k

theorem nat_sub_sub (a b : Nat) : ∀ c, a - b - c = a - (b + c)
  | 0 => rfl
  | c + 1 => by
    have h1 : a - b - (c + 1) = (a - b - c) - 1 := Nat.sub_succ (a - b) c
    have h2 : b + (c + 1) = (b + c) + 1 := Nat.add_succ b c
    have h3 : a - ((b + c) + 1) = (a - (b + c)) - 1 := Nat.sub_succ a (b + c)
    rw [h1, h2, h3, nat_sub_sub a b c]

theorem nat_sub_sub_self {a b : Nat} (h : a ≤ b) : b - (b - a) = a := by
  obtain ⟨k, hk⟩ := Nat.le.dest h
  subst hk
  rw [nat_add_sub_cancel_left]
  exact nat_sub_self_add a k

theorem nat_sub_le_sub_left {a b : Nat} (h : a ≤ b) (c : Nat) :
    c - b ≤ c - a := by
  obtain ⟨k, hk⟩ := Nat.le.dest h
  subst hk
  rw [← nat_sub_sub]
  exact Nat.sub_le (c - a) k

theorem nat_sub_add_comm {a b c : Nat} (h : c ≤ a) :
    a + b - c = a - c + b := by
  obtain ⟨k, hk⟩ := Nat.le.dest h
  subst hk
  rw [nat_add_sub_cancel_left c k, Nat.add_assoc,
    nat_add_sub_cancel_left c (k + b)]

/-! ### Bounded search toolkit (computable witness extraction)

`firstBelow p bound` returns the least `k < bound` with `p k = true`;
`pairFind test bound` returns the least pair `i < j < bound` with
`test i j = true` (least `j`, then least `i`). Both are structural
recursions with soundness and completeness lemmas, so every witness
below is computed rather than chosen. -/

/-- Least `k < bound` with `p k = true`, if any. -/
def firstBelow (p : Nat → Bool) : Nat → Option Nat
  | 0 => none
  | bound + 1 =>
    match firstBelow p bound with
    | some k => some k
    | none =>
      match p bound with
      | true => some bound
      | false => none

theorem firstBelow_some (p : Nat → Bool) :
    ∀ (bound k : Nat), firstBelow p bound = some k → k < bound ∧ p k = true
  | 0, _, h => nomatch h
  | bound + 1, k, h => by
    simp only [firstBelow] at h
    split at h
    · rename_i k' heq
      injection h with h'
      subst h'
      obtain ⟨hlt, hp⟩ := firstBelow_some p bound k' heq
      exact ⟨Nat.lt_succ_of_lt hlt, hp⟩
    · rename_i heq₁
      split at h
      · rename_i hpb
        injection h with h'
        subst h'
        exact ⟨Nat.lt_succ_self bound, hpb⟩
      · exact nomatch h

theorem firstBelow_none (p : Nat → Bool) :
    ∀ (bound : Nat), firstBelow p bound = none →
      ∀ k, k < bound → p k = false
  | 0, _, k, hk => absurd hk (Nat.not_lt_zero k)
  | bound + 1, h, k, hk => by
    simp only [firstBelow] at h
    split at h
    · exact nomatch h
    · rename_i heq₁
      split at h
      · exact nomatch h
      · rename_i hpb
        cases Nat.lt_succ_iff_lt_or_eq.mp hk with
        | inl hkb => exact firstBelow_none p bound heq₁ k hkb
        | inr hkb => subst hkb; exact hpb

theorem firstBelow_least (p : Nat → Bool) :
    ∀ (bound k : Nat), firstBelow p bound = some k →
      ∀ i, i < k → p i = false
  | 0, _, h => nomatch h
  | bound + 1, k, h => by
    simp only [firstBelow] at h
    split at h
    · rename_i k' heq
      injection h with h'
      subst h'
      exact firstBelow_least p bound k' heq
    · rename_i heq₁
      split at h
      · rename_i hpb
        injection h with h'
        subst h'
        exact fun i hi => firstBelow_none p bound heq₁ i hi
      · exact nomatch h

/-- Least colliding pair below `bound`: least `j`, then least `i < j`. -/
def pairFind (test : Nat → Nat → Bool) : Nat → Option (Nat × Nat)
  | 0 => none
  | bound + 1 =>
    match pairFind test bound with
    | some ij => some ij
    | none =>
      match firstBelow (fun i => test i bound) bound with
      | some i => some (i, bound)
      | none => none

theorem pairFind_some (test : Nat → Nat → Bool) :
    ∀ (bound i j : Nat), pairFind test bound = some (i, j) →
      i < j ∧ j < bound ∧ test i j = true
  | 0, _, _, h => nomatch h
  | bound + 1, i, j, h => by
    simp only [pairFind] at h
    split at h
    · rename_i ij heq
      cases ij with
      | mk i' j' =>
        injection h with h'
        injection h' with hi hj
        subst hi
        subst hj
        obtain ⟨hij, hjb, ht⟩ := pairFind_some test bound i' j' heq
        exact ⟨hij, Nat.lt_succ_of_lt hjb, ht⟩
    · rename_i heq₁
      split at h
      · rename_i i' heq₂
        injection h with h'
        injection h' with hi hj
        subst hi
        subst hj
        obtain ⟨hilt, hp⟩ :=
          firstBelow_some (fun t => test t bound) bound i' heq₂
        exact ⟨hilt, Nat.lt_succ_self bound, hp⟩
      · exact nomatch h

theorem pairFind_none (test : Nat → Nat → Bool) :
    ∀ (bound : Nat), pairFind test bound = none →
      ∀ i j, i < j → j < bound → test i j = false
  | 0, _, _, j, _, hj => absurd hj (Nat.not_lt_zero j)
  | bound + 1, h, i, j, hij, hj => by
    simp only [pairFind] at h
    split at h
    · exact nomatch h
    · rename_i heq₁
      split at h
      · exact nomatch h
      · rename_i heq₂
        cases Nat.lt_succ_iff_lt_or_eq.mp hj with
        | inl hjb => exact pairFind_none test bound heq₁ i j hij hjb
        | inr hjb =>
          subst hjb
          exact firstBelow_none (fun t => test t j) j heq₂ i hij

/-- Constructive pigeonhole: an explicit collision with `j ≤ n`, found by
    bounded search. -/
theorem fin_collides_bounded {n : Nat} (U : Fin n → Fin n) (z : Fin n) :
    ∃ i j, i < j ∧ j ≤ n ∧ iter U i z = iter U j z := by
  cases hpf : pairFind (fun i j => decide (iter U i z = iter U j z)) (n + 1) with
  | some ij =>
    cases ij with
    | mk i j =>
      obtain ⟨hij, hjb, ht⟩ :=
        pairFind_some (fun i j => decide (iter U i z = iter U j z))
          (n + 1) i j hpf
      exact ⟨i, j, hij, Nat.le_of_lt_succ hjb, of_decide_eq_true ht⟩
  | none =>
    exfalso
    have hcomp :=
      pairFind_none (fun i j => decide (iter U i z = iter U j z)) (n + 1) hpf
    let f : Nat → Nat := fun i => (iter U i z).val
    have hb : ∀ i, i < n + 1 → f i < n := fun i _ => (iter U i z).isLt
    have hinj : ∀ i j, i < n + 1 → j < n + 1 → f i = f j → i = j := by
      intro i j hi hj heq
      have he : iter U i z = iter U j z := Fin.eq_of_val_eq heq
      cases Nat.lt_trichotomy i j with
      | inl hlt =>
        have hfalse := hcomp i j hlt hj
        exact Bool.noConfusion (hfalse.symm.trans (decide_eq_true he))
      | inr hrest =>
        cases hrest with
        | inl heqij => exact heqij
        | inr hgt =>
          have hfalse := hcomp j i hgt hi
          exact Bool.noConfusion (hfalse.symm.trans (decide_eq_true he.symm))
    exact Density.no_distinct_large n f hb hinj

/-- On a finite carrier every orbit collides. -/
theorem fin_collides {n : Nat} (U : Fin n → Fin n) (z : Fin n) :
    Collides U z := by
  obtain ⟨i, j, hij, _hjn, he⟩ := fin_collides_bounded U z
  exact ⟨i, j, hij, he⟩

/-- Injectivity + finitude ⇒ every seed returns. -/
theorem fin_returns {n : Nat} (U : Fin n → Fin n) (h : EndoInj U) (z : Fin n) :
    ∃ p : Nat, 0 < p ∧ iter U p z = z :=
  collision_returns U h z (fin_collides U z)

/-- Return within the carrier bound: some `0 < q ≤ n` with `iter U q z = z`. -/
theorem fin_returns_le {n : Nat} (U : Fin n → Fin n) (h : EndoInj U)
    (z : Fin n) :
    ∃ q : Nat, 0 < q ∧ q ≤ n ∧ iter U q z = z := by
  obtain ⟨i, j, hij, hjn, he⟩ := fin_collides_bounded U z
  refine ⟨j - i, nat_sub_pos_of_lt hij,
    Nat.le_trans (Nat.sub_le j i) hjn, ?_⟩
  have hsum : i + (j - i) = j := nat_add_sub_of_le (Nat.le_of_lt hij)
  have hstep : iter U i (iter U (j - i) z) = iter U i z := by
    rw [← iter_add, hsum]
    exact he.symm
  exact iter_lossless U h i _ _ hstep

/-- Least positive return time at `z`, computed by bounded search. -/
def minPeriod {n : Nat} (U : Fin n → Fin n) (h : EndoInj U)
    (z : Fin n) : Nat :=
  match firstBelow (fun k => decide (iter U (k + 1) z = z)) n with
  | some k => k + 1
  | none => 1

theorem minPeriod_spec {n : Nat} (U : Fin n → Fin n) (h : EndoInj U)
    (z : Fin n) :
    0 < minPeriod U h z ∧ iter U (minPeriod U h z) z = z ∧
      ∀ k, 0 < k → k < minPeriod U h z → iter U k z ≠ z := by
  cases hfb : firstBelow (fun k => decide (iter U (k + 1) z = z)) n with
  | none =>
    exfalso
    obtain ⟨q, hq0, hqn, hqret⟩ := fin_returns_le U h z
    have hqlt : q - 1 < n :=
      Nat.lt_of_lt_of_le (Nat.sub_lt hq0 Nat.zero_lt_one) hqn
    have hq1 : (q - 1) + 1 = q := nat_sub_add_cancel (Nat.succ_le_of_lt hq0)
    have hfalse := firstBelow_none _ n hfb (q - 1) hqlt
    have htrue : decide (iter U ((q - 1) + 1) z = z) = true :=
      decide_eq_true (by rw [hq1]; exact hqret)
    exact Bool.noConfusion (hfalse.symm.trans htrue)
  | some k =>
    have hmp : minPeriod U h z = k + 1 := by
      unfold minPeriod
      rw [hfb]
    obtain ⟨_hkn, hpk⟩ := firstBelow_some _ n k hfb
    refine ⟨?_, ?_, ?_⟩
    · rw [hmp]; exact Nat.succ_pos k
    · rw [hmp]; exact of_decide_eq_true hpk
    · intro m hm0 hmlt heq
      rw [hmp] at hmlt
      have hmk : m ≤ k := Nat.le_of_lt_succ hmlt
      have hm1lt : m - 1 < k :=
        Nat.lt_of_lt_of_le (Nat.sub_lt hm0 Nat.zero_lt_one) hmk
      have hm1 : (m - 1) + 1 = m := nat_sub_add_cancel (Nat.succ_le_of_lt hm0)
      have hfalse := firstBelow_least _ n k hfb (m - 1) hm1lt
      have htrue : decide (iter U ((m - 1) + 1) z = z) = true :=
        decide_eq_true (by rw [hm1]; exact heq)
      exact Bool.noConfusion (hfalse.symm.trans htrue)

theorem minPeriod_pos {n : Nat} (U : Fin n → Fin n) (h : EndoInj U)
    (z : Fin n) : 0 < minPeriod U h z :=
  (minPeriod_spec U h z).1

theorem minPeriod_return {n : Nat} (U : Fin n → Fin n) (h : EndoInj U)
    (z : Fin n) : iter U (minPeriod U h z) z = z :=
  (minPeriod_spec U h z).2.1

theorem minPeriod_least {n : Nat} (U : Fin n → Fin n) (h : EndoInj U)
    (z : Fin n) : ∀ k, 0 < k → k < minPeriod U h z → iter U k z ≠ z :=
  (minPeriod_spec U h z).2.2

/-- Existence form, retained for the audit surface: now a projection of
    the computed period rather than an input to a choice principle. -/
theorem exists_min_period {n : Nat} (U : Fin n → Fin n) (h : EndoInj U)
    (z : Fin n) :
    ∃ p : Nat, 0 < p ∧ iter U p z = z ∧
      ∀ k, 0 < k → k < p → iter U k z ≠ z :=
  ⟨minPeriod U h z, minPeriod_spec U h z⟩

/-- Reduce any iterate exponent below the period, by strong induction:
    an axiom-free replacement for modulus arithmetic on the main chain. -/
theorem iter_reduce {n : Nat} (U : Fin n → Fin n) (h : EndoInj U)
    (z : Fin n) (t : Nat) :
    ∃ r, r < minPeriod U h z ∧ iter U t z = iter U r z := by
  refine Nat.strongRecOn t ?_
  intro t ih
  cases Nat.lt_or_ge t (minPeriod U h z) with
  | inl hlt => exact ⟨t, hlt, rfl⟩
  | inr hge =>
    have hp : 0 < minPeriod U h z := minPeriod_pos U h z
    have ht0 : 0 < t := Nat.lt_of_lt_of_le hp hge
    have hlt' : t - minPeriod U h z < t := Nat.sub_lt ht0 hp
    obtain ⟨r, hr, hiter⟩ := ih (t - minPeriod U h z) hlt'
    refine ⟨r, hr, ?_⟩
    have hsum : (t - minPeriod U h z) + minPeriod U h z = t :=
      nat_sub_add_cancel hge
    calc iter U t z
        = iter U ((t - minPeriod U h z) + minPeriod U h z) z := by
          rw [hsum]
      _ = iter U (t - minPeriod U h z) (iter U (minPeriod U h z) z) := by
          rw [iter_add]
      _ = iter U (t - minPeriod U h z) z := by
          rw [minPeriod_return U h z]
      _ = iter U r z := hiter

/-- First `p` iterates from a least-period seed are pairwise distinct. -/
theorem orbit_distinct {n : Nat} (U : Fin n → Fin n) (h : EndoInj U)
    (z : Fin n) :
    ∀ i j, i < minPeriod U h z → j < minPeriod U h z →
      iter U i z = iter U j z → i = j := by
  intro i j hi hj heq
  cases Nat.lt_trichotomy i j with
  | inl hlt =>
    have hdpos : 0 < j - i := nat_sub_pos_of_lt hlt
    have hdlt : j - i < minPeriod U h z :=
      Nat.lt_of_le_of_lt (Nat.sub_le j i) hj
    have hsum : i + (j - i) = j := nat_add_sub_of_le (Nat.le_of_lt hlt)
    have hstep : iter U i (iter U (j - i) z) = iter U i z := by
      rw [← iter_add, hsum, heq]
    have key : iter U (j - i) z = z := iter_lossless U h i _ _ hstep
    exact absurd key (minPeriod_least U h z (j - i) hdpos hdlt)
  | inr hrest =>
    cases hrest with
    | inl heqij => exact heqij
    | inr hgt =>
      have hdpos : 0 < i - j := nat_sub_pos_of_lt hgt
      have hdlt : i - j < minPeriod U h z :=
        Nat.lt_of_le_of_lt (Nat.sub_le i j) hi
      have hsum : j + (i - j) = i := nat_add_sub_of_le (Nat.le_of_lt hgt)
      have hstep : iter U j (iter U (i - j) z) = iter U j z := by
        rw [← iter_add, hsum, heq.symm]
      have key : iter U (i - j) z = z := iter_lossless U h j _ _ hstep
      exact absurd key (minPeriod_least U h z (i - j) hdpos hdlt)

/-- Period is invariant under moving along the orbit. -/
theorem minPeriod_iter {n : Nat} (U : Fin n → Fin n) (h : EndoInj U)
    (z : Fin n) (t : Nat) :
    minPeriod U h (iter U t z) = minPeriod U h z := by
  let p := minPeriod U h z
  let q := minPeriod U h (iter U t z)
  have hp : 0 < p := minPeriod_pos U h z
  have hq : 0 < q := minPeriod_pos U h (iter U t z)
  have hret_p : iter U p z = z := minPeriod_return U h z
  have hret_q : iter U q (iter U t z) = iter U t z :=
    minPeriod_return U h (iter U t z)
  have hret_p' : iter U p (iter U t z) = iter U t z := by
    rw [← iter_add, Nat.add_comm, iter_add, hret_p]
  have hret_q_z : iter U q z = z := by
    have : iter U t (iter U q z) = iter U t z := by
      have h := hret_q
      rw [← iter_add, Nat.add_comm q t, iter_add] at h
      exact h
    exact iter_lossless U h t _ _ this
  have hle_qp : q ≤ p := by
    cases Nat.lt_or_ge p q with
    | inl hpq =>
      exact absurd hret_p' (minPeriod_least U h (iter U t z) p hp hpq)
    | inr hge => exact hge
  have hle_pq : p ≤ q := by
    cases Nat.lt_or_ge q p with
    | inl hqp =>
      exact absurd hret_q_z (minPeriod_least U h z q hq hqp)
    | inr hge => exact hge
  exact Nat.le_antisymm hle_qp hle_pq

theorem iter_mul_period {n : Nat} (U : Fin n → Fin n) (h : EndoInj U)
    (z : Fin n) : ∀ q : Nat, iter U (minPeriod U h z * q) z = z
  | 0 => rfl
  | q + 1 => by
    have hret := minPeriod_return U h z
    rw [Nat.mul_succ, Nat.add_comm, iter_add, iter_mul_period U h z q, hret]

theorem iter_mod_period {n : Nat} (U : Fin n → Fin n) (h : EndoInj U)
    (z : Fin n) (i : Nat) :
    iter U i z = iter U (i % minPeriod U h z) z := by
  let p := minPeriod U h z
  have hp : 0 < p := minPeriod_pos U h z
  have hdiv : p * (i / p) + i % p = i := Nat.div_add_mod i p
  rw [← hdiv]
  have hmod : (p * (i / p) + i % p) % p = i % p := by
    rw [Nat.mul_add_mod_self_left, Nat.mod_eq_of_lt (Nat.mod_lt i hp)]
  rw [hmod, Nat.add_comm (p * (i / p)), iter_add, iter_mul_period U h z]

/-- Argmin of `f` on `{0, …, p-1}`. -/
theorem exists_argmin :
    ∀ (p : Nat) (_hp : 0 < p) (f : Nat → Nat),
      ∃ k, k < p ∧ ∀ j, j < p → f k ≤ f j
  | 0, hp, _f => absurd hp (Nat.lt_irrefl 0)
  | 1, _hp, f => by
    refine ⟨0, Nat.zero_lt_one, ?_⟩
    intro j hj
    have : j = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ hj)
    subst this
    exact Nat.le_refl _
  | p' + 2, _hp, f => by
    obtain ⟨k, hk, hmin⟩ :=
      exists_argmin (p' + 1) (Nat.zero_lt_succ p') f
    cases Nat.lt_or_ge (f (p' + 1)) (f k) with
    | inl hlt =>
      refine ⟨p' + 1, Nat.lt_succ_self _, ?_⟩
      intro j hj
      cases Nat.lt_succ_iff_lt_or_eq.mp hj with
      | inl hj' => exact Nat.le_trans (Nat.le_of_lt hlt) (hmin j hj')
      | inr hj' => subst hj'; exact Nat.le_refl _
    | inr hge =>
      refine ⟨k, Nat.lt_succ_of_lt hk, ?_⟩
      intro j hj
      cases Nat.lt_succ_iff_lt_or_eq.mp hj with
      | inl hj' => exact hmin j hj'
      | inr hj' => subst hj'; exact hge

/-- Computable argmin of `f` on `{0, …, p-1}`: first index attaining the
    running minimum, scanning upward. -/
def argminBelow (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | 1 => 0
  | p + 2 =>
    if f (p + 1) < f (argminBelow f (p + 1)) then p + 1
    else argminBelow f (p + 1)

theorem argminBelow_lt (f : Nat → Nat) :
    ∀ p, 0 < p → argminBelow f p < p
  | 0, hp => absurd hp (Nat.lt_irrefl 0)
  | 1, _ => Nat.zero_lt_one
  | p + 2, _ => by
    unfold argminBelow
    split
    · exact Nat.lt_succ_self _
    · exact Nat.lt_succ_of_lt (argminBelow_lt f (p + 1) (Nat.zero_lt_succ p))

theorem argminBelow_min (f : Nat → Nat) :
    ∀ p j, j < p → f (argminBelow f p) ≤ f j
  | 0, j, hj => absurd hj (Nat.not_lt_zero j)
  | 1, j, hj => by
    have hj0 : j = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ hj)
    subst hj0
    exact Nat.le_refl _
  | p + 2, j, hj => by
    unfold argminBelow
    split
    · rename_i hlt
      cases Nat.lt_succ_iff_lt_or_eq.mp hj with
      | inl hj' =>
        exact Nat.le_trans (Nat.le_of_lt hlt)
          (argminBelow_min f (p + 1) j hj')
      | inr hj' =>
        subst hj'
        exact Nat.le_refl _
    · rename_i hge
      cases Nat.lt_succ_iff_lt_or_eq.mp hj with
      | inl hj' => exact argminBelow_min f (p + 1) j hj'
      | inr hj' =>
        subst hj'
        exact Nat.le_of_not_lt hge

/-- Least-`val` point on the cycle of `z`. -/
theorem exists_orbit_base {n : Nat} (U : Fin n → Fin n) (h : EndoInj U)
    (z : Fin n) :
    ∃ (b : Fin n),
      (∃ t, t < minPeriod U h z ∧ iter U t z = b) ∧
      ∀ j, j < minPeriod U h z → b.val ≤ (iter U j z).val := by
  let p := minPeriod U h z
  have hp : 0 < p := minPeriod_pos U h z
  obtain ⟨t, ht, hmin⟩ := exists_argmin p hp (fun k => (iter U k z).val)
  exact ⟨iter U t z, ⟨t, ht, rfl⟩, hmin⟩

/-- Canonical basepoint of the cycle through `z`: the least-`val` iterate
    within one period, computed by `argminBelow`. -/
def orbitBase {n : Nat} (U : Fin n → Fin n) (h : EndoInj U)
    (z : Fin n) : Fin n :=
  iter U (argminBelow (fun k => (iter U k z).val) (minPeriod U h z)) z

theorem orbitBase_mem {n : Nat} (U : Fin n → Fin n) (h : EndoInj U)
    (z : Fin n) :
    ∃ t, t < minPeriod U h z ∧ iter U t z = orbitBase U h z :=
  ⟨argminBelow (fun k => (iter U k z).val) (minPeriod U h z),
   argminBelow_lt _ _ (minPeriod_pos U h z), rfl⟩

theorem orbitBase_min {n : Nat} (U : Fin n → Fin n) (h : EndoInj U)
    (z : Fin n) :
    ∀ j, j < minPeriod U h z →
      (orbitBase U h z).val ≤ (iter U j z).val := by
  intro j hj
  exact argminBelow_min (fun k => (iter U k z).val) (minPeriod U h z) j hj

/-- Arithmetic identity for wrapping around a cycle. -/
theorem cycle_add_id (p r s : Nat) (hsr : s ≤ r) (hrp : r ≤ p) :
    p - (r - s) + r = p + s := by
  have hle : r - s ≤ p := Nat.le_trans (Nat.sub_le r s) hrp
  have h1 : p - (r - s) + (r - s) = p := nat_sub_add_cancel hle
  have h2 : (r - s) + s = r := nat_sub_add_cancel hsr
  calc p - (r - s) + r
      = p - (r - s) + ((r - s) + s) := by rw [h2]
    _ = (p - (r - s) + (r - s)) + s := by rw [← Nat.add_assoc]
    _ = p + s := by rw [h1]

/-- Reach any cycle point from any other by a forward step of length `< p`. -/
theorem cycle_reach {n : Nat} (U : Fin n → Fin n) (h : EndoInj U)
    (z : Fin n) (t s : Nat) (hs : s < minPeriod U h z) :
    ∃ k, k < minPeriod U h z ∧
      iter U k (iter U t z) = iter U s z := by
  let p := minPeriod U h z
  have hp : 0 < p := minPeriod_pos U h z
  obtain ⟨r, hr, ht_eq⟩ := iter_reduce U h z t
  rw [ht_eq]
  cases Nat.le_total r s with
  | inl hrs =>
    refine ⟨s - r, Nat.lt_of_le_of_lt (Nat.sub_le s r) hs, ?_⟩
    rw [← iter_add, nat_sub_add_cancel hrs]
  | inr hsr =>
    if heq : r = s then
      refine ⟨0, hp, ?_⟩
      change iter U r z = iter U s z
      rw [heq]
    else
      have hrs_lt : s < r := Nat.lt_of_le_of_ne hsr (Ne.symm heq)
      have hdiff : 0 < r - s := nat_sub_pos_of_lt hrs_lt
      let k := p - (r - s)
      have hklt : k < p := Nat.sub_lt hp hdiff
      refine ⟨k, hklt, ?_⟩
      have hsum : k + r = p + s :=
        cycle_add_id p r s (Nat.le_of_lt hrs_lt) (Nat.le_of_lt hr)
      have hiter : iter U k (iter U r z) = iter U (k + r) z := by
        rw [← iter_add]
      rw [hiter, hsum, Nat.add_comm p s, iter_add]
      have hret : iter U p z = z := minPeriod_return U h z
      rw [hret]

/-- The cycle basepoint is invariant under moving along the orbit. -/
theorem orbitBase_iter {n : Nat} (U : Fin n → Fin n) (h : EndoInj U)
    (z : Fin n) (t : Nat) :
    orbitBase U h (iter U t z) = orbitBase U h z := by
  apply Fin.eq_of_val_eq
  apply Nat.le_antisymm
  · -- val(orbitBase (iter t z)) ≤ val(orbitBase z)
    obtain ⟨t0, ht0, hiter0⟩ := orbitBase_mem U h z
    obtain ⟨k, hk, hkiter⟩ := cycle_reach U h z t t0 ht0
    have hp_eq : minPeriod U h (iter U t z) = minPeriod U h z :=
      minPeriod_iter U h z t
    have hb : orbitBase U h z = iter U k (iter U t z) :=
      (hkiter.trans hiter0).symm
    have hk' : k < minPeriod U h (iter U t z) := by
      rw [hp_eq]; exact hk
    have hle := orbitBase_min U h (iter U t z) k hk'
    rw [← hb] at hle
    exact hle
  · -- val(orbitBase z) ≤ val(orbitBase (iter t z))
    obtain ⟨t1, _ht1, hiter1⟩ := orbitBase_mem U h (iter U t z)
    have h1 : orbitBase U h (iter U t z) = iter U t1 (iter U t z) :=
      Eq.symm hiter1
    have h2 : iter U t1 (iter U t z) = iter U (t1 + t) z := by
      rw [← iter_add]
    obtain ⟨r, hmod, h3⟩ := iter_reduce U h z (t1 + t)
    have hb' : orbitBase U h (iter U t z) = iter U r z :=
      h1.trans (h2.trans h3)
    have hle := orbitBase_min U h z r hmod
    rw [← hb'] at hle
    exact hle

theorem orbitBase_idem {n : Nat} (U : Fin n → Fin n) (h : EndoInj U)
    (z : Fin n) : orbitBase U h (orbitBase U h z) = orbitBase U h z := by
  obtain ⟨t, _, ht⟩ := orbitBase_mem U h z
  calc
    orbitBase U h (orbitBase U h z)
        = orbitBase U h (iter U t z) := by rw [ht]
      _ = orbitBase U h z := orbitBase_iter U h z t

/-- Index of `x` on its cycle, measured from `orbitBase`. -/
theorem exists_index {n : Nat} (U : Fin n → Fin n) (h : EndoInj U)
    (x : Fin n) :
    ∃ k, k < minPeriod U h (orbitBase U h x) ∧
      iter U k (orbitBase U h x) = x := by
  obtain ⟨t, ht, hiter⟩ := orbitBase_mem U h x
  have hp_eq : minPeriod U h (orbitBase U h x) = minPeriod U h x := by
    rw [← hiter, minPeriod_iter]
  obtain ⟨k, hk, hkiter⟩ :=
    cycle_reach U h x t 0 (minPeriod_pos U h x)
  refine ⟨k, ?_, ?_⟩
  · rw [hp_eq]; exact hk
  · have : iter U k (orbitBase U h x) = iter U 0 x := by
      rw [← hiter]; exact hkiter
    exact this

/-- Least index of `x` from its cycle basepoint, by bounded search. -/
def indexOf {n : Nat} (U : Fin n → Fin n) (h : EndoInj U)
    (x : Fin n) : Nat :=
  match firstBelow (fun k => decide (iter U k (orbitBase U h x) = x))
      (minPeriod U h (orbitBase U h x)) with
  | some k => k
  | none => 0

theorem indexOf_spec {n : Nat} (U : Fin n → Fin n) (h : EndoInj U)
    (x : Fin n) :
    indexOf U h x < minPeriod U h (orbitBase U h x) ∧
      iter U (indexOf U h x) (orbitBase U h x) = x := by
  cases hfb : firstBelow (fun k => decide (iter U k (orbitBase U h x) = x))
      (minPeriod U h (orbitBase U h x)) with
  | none =>
    exfalso
    obtain ⟨k, hk, hkiter⟩ := exists_index U h x
    have hfalse := firstBelow_none _ _ hfb k hk
    have htrue : decide (iter U k (orbitBase U h x) = x) = true :=
      decide_eq_true hkiter
    exact Bool.noConfusion (hfalse.symm.trans htrue)
  | some k =>
    have hidx : indexOf U h x = k := by
      unfold indexOf
      rw [hfb]
    obtain ⟨hk, hp⟩ := firstBelow_some _ _ k hfb
    rw [hidx]
    exact ⟨hk, of_decide_eq_true hp⟩

theorem indexOf_lt {n : Nat} (U : Fin n → Fin n) (h : EndoInj U)
    (x : Fin n) : indexOf U h x < minPeriod U h (orbitBase U h x) :=
  (indexOf_spec U h x).1

theorem indexOf_iter {n : Nat} (U : Fin n → Fin n) (h : EndoInj U)
    (x : Fin n) : iter U (indexOf U h x) (orbitBase U h x) = x :=
  (indexOf_spec U h x).2

/-- Reflect index: `k ↦ p - 1 - k` on a period-`p` cycle. -/
theorem reflect_idx (p k : Nat) (hk : k < p) : p - 1 - k < p := by
  have hp : 0 < p := Nat.zero_lt_of_lt hk
  exact Nat.lt_of_le_of_lt (Nat.sub_le (p - 1) k) (Nat.pred_lt_of_lt hp)

theorem reflect_idx_involutive (p k : Nat) (hk : k < p) :
    p - 1 - (p - 1 - k) = k := by
  have hk' : k ≤ p - 1 := Nat.le_pred_of_lt hk
  exact nat_sub_sub_self hk'

theorem succ_pred_idx (p k : Nat) (hk : k < p) :
    (p - 1 - k) + 1 = p - k := by
  have hp : 0 < p := Nat.zero_lt_of_lt hk
  have hk' : k ≤ p - 1 := Nat.le_pred_of_lt hk
  have h1 : p - 1 - k + 1 = p - 1 + 1 - k := (nat_sub_add_comm hk').symm
  have h2 : p - 1 + 1 = p := nat_sub_add_cancel (Nat.succ_le_of_lt hp)
  rw [h1, h2]

/-- Cycle-wise reflect: first bounce. -/
def bounceφ {n : Nat} (U : Fin n → Fin n) (h : EndoInj U) :
    Fin n → Fin n :=
  fun x =>
    iter U (minPeriod U h (orbitBase U h x) - 1 - indexOf U h x)
      (orbitBase U h x)

/-- Second bounce: `U ∘ φ`. -/
def bounceσ {n : Nat} (U : Fin n → Fin n) (h : EndoInj U) :
    Fin n → Fin n :=
  fun x => U (bounceφ U h x)

theorem orbitBase_of_bounceφ {n : Nat} (U : Fin n → Fin n) (h : EndoInj U)
    (x : Fin n) :
    orbitBase U h (bounceφ U h x) = orbitBase U h x := by
  dsimp [bounceφ]
  rw [orbitBase_iter, orbitBase_idem]

theorem indexOf_bounceφ {n : Nat} (U : Fin n → Fin n) (h : EndoInj U)
    (x : Fin n) :
    indexOf U h (bounceφ U h x) =
      minPeriod U h (orbitBase U h x) - 1 - indexOf U h x := by
  let b := orbitBase U h x
  let p := minPeriod U h b
  let k := indexOf U h x
  have hk : k < p := indexOf_lt U h x
  have hbφ : orbitBase U h (bounceφ U h x) = b := orbitBase_of_bounceφ U h x
  have hφ : bounceφ U h x = iter U (p - 1 - k) b := rfl
  have hspec :
      indexOf U h (bounceφ U h x) <
        minPeriod U h (orbitBase U h (bounceφ U h x)) ∧
      iter U (indexOf U h (bounceφ U h x))
        (orbitBase U h (bounceφ U h x)) = bounceφ U h x :=
    ⟨indexOf_lt U h (bounceφ U h x), indexOf_iter U h (bounceφ U h x)⟩
  have hpφ : minPeriod U h (orbitBase U h (bounceφ U h x)) = p := by
    rw [hbφ]
  have hlt : indexOf U h (bounceφ U h x) < p :=
    Nat.lt_of_lt_of_eq hspec.1 hpφ
  have heq :
      iter U (indexOf U h (bounceφ U h x)) b = iter U (p - 1 - k) b := by
    have h1 : iter U (indexOf U h (bounceφ U h x)) b =
        iter U (indexOf U h (bounceφ U h x))
          (orbitBase U h (bounceφ U h x)) := by rw [hbφ]
    have h2 : iter U (indexOf U h (bounceφ U h x))
        (orbitBase U h (bounceφ U h x)) = bounceφ U h x := hspec.2
    exact h1.trans (h2.trans hφ)
  exact orbit_distinct U h b _ _ hlt (reflect_idx p k hk) heq

theorem bounceφ_involution {n : Nat} (U : Fin n → Fin n) (h : EndoInj U) :
    IsInvolution (bounceφ U h) := by
  intro x
  let b := orbitBase U h x
  let p := minPeriod U h b
  let k := indexOf U h x
  have hk : k < p := indexOf_lt U h x
  have hx : iter U k b = x := indexOf_iter U h x
  have hbφ : orbitBase U h (bounceφ U h x) = b := orbitBase_of_bounceφ U h x
  have hidx : indexOf U h (bounceφ U h x) = p - 1 - k :=
    indexOf_bounceφ U h x
  have hpφ : minPeriod U h (orbitBase U h (bounceφ U h x)) = p := by
    rw [hbφ]
  have hunfold :
      bounceφ U h (bounceφ U h x) =
        iter U
          (minPeriod U h (orbitBase U h (bounceφ U h x)) - 1 -
            indexOf U h (bounceφ U h x))
          (orbitBase U h (bounceφ U h x)) := rfl
  rw [hunfold, hpφ, hidx, hbφ, reflect_idx_involutive p k hk, hx]

theorem bounceσ_eq_iter {n : Nat} (U : Fin n → Fin n) (h : EndoInj U)
    (x : Fin n) :
    bounceσ U h x =
      iter U (minPeriod U h (orbitBase U h x) - indexOf U h x)
        (orbitBase U h x) := by
  let b := orbitBase U h x
  let p := minPeriod U h b
  let k := indexOf U h x
  have hk : k < p := indexOf_lt U h x
  dsimp [bounceσ, bounceφ]
  have : iter U ((p - 1 - k) + 1) b = U (iter U (p - 1 - k) b) := rfl
  rw [← this, succ_pred_idx p k hk]

theorem bounceσ_involution {n : Nat} (U : Fin n → Fin n) (h : EndoInj U) :
    IsInvolution (bounceσ U h) := by
  intro x
  let b := orbitBase U h x
  let p := minPeriod U h b
  let k := indexOf U h x
  have hk : k < p := indexOf_lt U h x
  have hx : iter U k b = x := indexOf_iter U h x
  have hp : 0 < p := minPeriod_pos U h b
  have hσx : bounceσ U h x = iter U (p - k) b := bounceσ_eq_iter U h x
  cases Nat.eq_zero_or_pos k with
  | inl hk0 =>
    -- k = 0: x = b and σ x = iter p b = b = x
    have hx0 : x = b := by
      have := hx
      rw [hk0] at this
      exact this.symm
    have hσ : bounceσ U h x = x := by
      rw [hσx, hk0, Nat.sub_zero, minPeriod_return U h b, hx0]
    rw [hσ, hσ]
  | inr hk0 =>
    have hpk : p - k < p := Nat.sub_lt hp hk0
    have hbσ : orbitBase U h (bounceσ U h x) = b := by
      rw [hσx, orbitBase_iter, orbitBase_idem]
    have hidxσ : indexOf U h (bounceσ U h x) = p - k := by
      have hspec :
          indexOf U h (bounceσ U h x) <
            minPeriod U h (orbitBase U h (bounceσ U h x)) ∧
          iter U (indexOf U h (bounceσ U h x))
            (orbitBase U h (bounceσ U h x)) = bounceσ U h x :=
        ⟨indexOf_lt U h (bounceσ U h x), indexOf_iter U h (bounceσ U h x)⟩
      have hpσ : minPeriod U h (orbitBase U h (bounceσ U h x)) = p := by
        rw [hbσ]
      have hlt : indexOf U h (bounceσ U h x) < p :=
        Nat.lt_of_lt_of_eq hspec.1 hpσ
      have heq :
          iter U (indexOf U h (bounceσ U h x)) b = iter U (p - k) b := by
        have h1 : iter U (indexOf U h (bounceσ U h x)) b =
            iter U (indexOf U h (bounceσ U h x))
              (orbitBase U h (bounceσ U h x)) := by rw [hbσ]
        have h2 : iter U (indexOf U h (bounceσ U h x))
            (orbitBase U h (bounceσ U h x)) = bounceσ U h x := hspec.2
        exact h1.trans (h2.trans hσx)
      exact orbit_distinct U h b _ _ hlt hpk heq
    have hφσ :
        bounceφ U h (bounceσ U h x) = iter U (p - 1 - (p - k)) b := by
      have hunfold :
          bounceφ U h (bounceσ U h x) =
            iter U
              (minPeriod U h (orbitBase U h (bounceσ U h x)) - 1 -
                indexOf U h (bounceσ U h x))
              (orbitBase U h (bounceσ U h x)) := rfl
      have hpσ : minPeriod U h (orbitBase U h (bounceσ U h x)) = p := by
        rw [hbσ]
      rw [hunfold, hpσ, hidxσ, hbσ]
    have hrefl : p - 1 - (p - k) = k - 1 := by
      have hkle : k ≤ p := Nat.le_of_lt hk
      have h1 : p - (p - k) = k := nat_sub_sub_self hkle
      have hle : p - k ≤ p - 1 :=
        nat_sub_le_sub_left (Nat.succ_le_of_lt hk0) p
      have hsucc' : p - 1 - (p - k) + 1 = k := by
        have hcomm : p - 1 - (p - k) + 1 = p - 1 + 1 - (p - k) :=
          (nat_sub_add_comm hle).symm
        have h2 : p - 1 + 1 = p := nat_sub_add_cancel (Nat.succ_le_of_lt hp)
        rw [hcomm, h2, h1]
      exact Nat.succ.inj
        (hsucc'.trans (Nat.succ_pred_eq_of_pos hk0).symm)
    show bounceσ U h (bounceσ U h x) = x
    have hσσ : bounceσ U h (bounceσ U h x) =
        U (bounceφ U h (bounceσ U h x)) := rfl
    rw [hσσ, hφσ, hrefl]
    have hstep : iter U ((k - 1) + 1) b = U (iter U (k - 1) b) := rfl
    have hks : (k - 1) + 1 = k := nat_sub_add_cancel (Nat.succ_le_of_lt hk0)
    rw [← hstep, hks, hx]

/-- Every injective endomap on `Fin n` factors as two involutions.
    The construction is computable and the proof is axiom-free. -/
def factor_fin {n : Nat} (U : Fin n → Fin n) (h : EndoInj U) :
    TwoBounceFactor U where
  φ := bounceφ U h
  σ := bounceσ U h
  φ_inv := bounceφ_involution U h
  σ_inv := bounceσ_involution U h
  factor := by
    intro x
    -- U x = σ (φ x) = U (φ (φ x)) = U x
    dsimp [bounceσ]
    rw [bounceφ_involution U h x]

/-! ## Canonicity fails (essential non-uniqueness)

Two factorisations of the same `U` need not share `φ` (or `σ`). The
involutive Bool case already kills uniqueness; its binary reordering is
T-7-shaped (ordered bounce pair), not a new dictionary face. On `Fin 3`
distinct reflection axes give factorisations unrelated by mere swap,
so the I-1 factorization gauge properly exceeds ℤ/2 while T-7 stays one ℤ/2. -/

theorem not_involution : IsInvolution (not : Bool → Bool) := by
  intro b; cases b <;> rfl

theorem not_endoInj : EndoInj (not : Bool → Bool) := by
  intro a b h
  cases a <;> cases b <;> first | rfl | cases h

/-- Pointwise inequality of first factors. -/
def FactorsDisagree {α : Type} {U : α → α}
    (f g : TwoBounceFactor U) : Prop :=
  (∃ x, f.φ x ≠ g.φ x) ∨ (∃ x, f.σ x ≠ g.σ x)

/-- Involutive reordering: `(id, U)` and `(U, id)` both factor `U`. -/
theorem involutive_factor_reorder {α : Type} (U : α → α)
    (h : IsInvolution U) :
    FactorsDisagree (factor_involution U h) (factor_involution_rev U h) ↔
      ∃ x, U x ≠ x := by
  constructor
  · intro hd
    cases hd with
    | inl hφ =>
      obtain ⟨x, hx⟩ := hφ
      exact ⟨x, fun heq => hx (Eq.symm heq)⟩
    | inr hσ =>
      obtain ⟨x, hx⟩ := hσ
      exact ⟨x, fun heq => hx heq⟩
  · intro ⟨x, hx⟩
    exact Or.inl ⟨x, fun heq => hx (Eq.symm heq)⟩

/-- **Canonicity fails.** `not` admits two disagreeing two-bounce
    factorisations (`not∘id` and `id∘not`). -/
theorem canonicity_fails :
    ∃ (U : Bool → Bool) (f g : TwoBounceFactor U),
      EndoInj U ∧ FactorsDisagree f g :=
  ⟨not,
   factor_involution not not_involution,
   factor_involution_rev not not_involution,
   not_endoInj,
   Or.inl ⟨false, by decide⟩⟩

/-- Bounce-swap of an ordered factor pair: `(φ,σ) ↦ (σ,φ)`. -/
def IsBounceSwap {α : Type} {U : α → α}
    (f g : TwoBounceFactor U) : Prop :=
  (∀ x, f.φ x = g.σ x) ∧ (∀ x, f.σ x = g.φ x)

/-! ## Factor-swap covers step reversal

If `U = σ ∘ φ` with involutions, then `φ ∘ σ` is the two-sided inverse of
`U`, and `(σ, φ)` is a two-bounce presentation of that reverse step.
Channel labels stay conventional; the *exchange* is the real content
(T-7 channel column at proved grade). -/

/-- Left inverse of `U` from any two-bounce factorisation. -/
theorem left_inv_of_factor {α : Type} (U : α → α) (f : TwoBounceFactor U) :
    ∀ x, f.φ (f.σ (U x)) = x := by
  intro x
  rw [f.factor x, f.σ_inv, f.φ_inv]

/-- Right inverse of `U` from any two-bounce factorisation. -/
theorem right_inv_of_factor {α : Type} (U : α → α) (f : TwoBounceFactor U) :
    ∀ x, U (f.φ (f.σ x)) = x := by
  intro x
  rw [f.factor, f.φ_inv, f.σ_inv]

/-- Reverse step recovered as `φ ∘ σ`. -/
def reverseOf {α : Type} {U : α → α} (f : TwoBounceFactor U) : α → α :=
  fun x => f.φ (f.σ x)

/-- Swap the bounce order: presentation of the reverse step. -/
def swapFactor {α : Type} {U : α → α} (f : TwoBounceFactor U) :
    TwoBounceFactor (reverseOf f) where
  φ := f.σ
  σ := f.φ
  φ_inv := f.σ_inv
  σ_inv := f.φ_inv
  factor := fun _ => rfl

/-- **Channel-swap is reversal.** Exchanging the two factors of any
    two-bounce presentation of `U` yields a two-bounce presentation of
    `U⁻¹` (`φ∘σ`), independently of which factorisation was chosen. -/
theorem channel_swap_is_reversal {α : Type} (U : α → α)
    (f : TwoBounceFactor U) :
    (∀ x, reverseOf f (U x) = x) ∧
    (∀ x, U (reverseOf f x) = x) ∧
    Nonempty (TwoBounceFactor (reverseOf f)) :=
  ⟨left_inv_of_factor U f, right_inv_of_factor U f, ⟨swapFactor f⟩⟩

/-- On an involution the reverse step equals `U`, so factor-swap
    re-presents the same step (T-7-shaped reorder). -/
theorem reverseOf_eq_of_involution {α : Type} (U : α → α)
    (h : IsInvolution U) (f : TwoBounceFactor U) :
    ∀ x, reverseOf f x = U x := by
  intro x
  have hinv : U (reverseOf f x) = x := right_inv_of_factor U f x
  calc
    reverseOf f x = U (U (reverseOf f x)) := (h _).symm
    _ = U x := by rw [hinv]

/-! ### Fin 3: axis choice exceeds bounce-swap -/

/-- The 3-cycle `(0 1 2)`. -/
def cycle3 : Fin 3 → Fin 3
  | ⟨0, _⟩ => ⟨1, by decide⟩
  | ⟨1, _⟩ => ⟨2, by decide⟩
  | ⟨2, _⟩ => ⟨0, by decide⟩

theorem cycle3_inj : EndoInj cycle3 := by
  intro a b h
  match a, b with
  | ⟨0, _⟩, ⟨0, _⟩ => rfl
  | ⟨0, _⟩, ⟨1, _⟩ => cases h
  | ⟨0, _⟩, ⟨2, _⟩ => cases h
  | ⟨1, _⟩, ⟨0, _⟩ => cases h
  | ⟨1, _⟩, ⟨1, _⟩ => rfl
  | ⟨1, _⟩, ⟨2, _⟩ => cases h
  | ⟨2, _⟩, ⟨0, _⟩ => cases h
  | ⟨2, _⟩, ⟨1, _⟩ => cases h
  | ⟨2, _⟩, ⟨2, _⟩ => rfl

/-- Reflect through `0` (fix 0, swap 1↔2). -/
def reflect0 : Fin 3 → Fin 3
  | ⟨0, _⟩ => ⟨0, by decide⟩
  | ⟨1, _⟩ => ⟨2, by decide⟩
  | ⟨2, _⟩ => ⟨1, by decide⟩

/-- Reflect through `1` (fix 1, swap 0↔2). -/
def reflect1 : Fin 3 → Fin 3
  | ⟨0, _⟩ => ⟨2, by decide⟩
  | ⟨1, _⟩ => ⟨1, by decide⟩
  | ⟨2, _⟩ => ⟨0, by decide⟩

theorem reflect0_involution : IsInvolution reflect0 := by
  intro x; exact (by decide : ∀ y : Fin 3, reflect0 (reflect0 y) = y) x

theorem reflect1_involution : IsInvolution reflect1 := by
  intro x; exact (by decide : ∀ y : Fin 3, reflect1 (reflect1 y) = y) x

theorem cycle3_reflect0_involution :
    IsInvolution (fun x => cycle3 (reflect0 x)) := by
  intro x
  exact (by decide : ∀ y : Fin 3,
    cycle3 (reflect0 (cycle3 (reflect0 y))) = y) x

theorem cycle3_reflect1_involution :
    IsInvolution (fun x => cycle3 (reflect1 x)) := by
  intro x
  exact (by decide : ∀ y : Fin 3,
    cycle3 (reflect1 (cycle3 (reflect1 y))) = y) x

def factor_cycle3_axis0 : TwoBounceFactor cycle3 where
  φ := reflect0
  σ := fun x => cycle3 (reflect0 x)
  φ_inv := reflect0_involution
  σ_inv := cycle3_reflect0_involution
  factor := fun x => by rw [reflect0_involution x]

def factor_cycle3_axis1 : TwoBounceFactor cycle3 where
  φ := reflect1
  σ := fun x => cycle3 (reflect1 x)
  φ_inv := reflect1_involution
  σ_inv := cycle3_reflect1_involution
  factor := fun x => by rw [reflect1_involution x]

/-- Axis choice: two Fin-3 factorisations disagree, and one is not the
    bounce-swap of the other. (I-1 factorization gauge > ℤ/2 reorder.) -/
theorem factorization_gauge_exceeds_swap :
    FactorsDisagree factor_cycle3_axis0 factor_cycle3_axis1 ∧
    ¬ IsBounceSwap factor_cycle3_axis0 factor_cycle3_axis1 := by
  constructor
  · refine Or.inl ⟨⟨0, by decide⟩, ?_⟩
    decide
  · intro h
    have hx := h.2 ⟨0, by decide⟩
    -- σ₀ 0 = 1, φ₁ 0 = 2
    revert hx
    decide

/-- **I-1 canonicity package.** Uniqueness fails; involutive reorder is
    available whenever `U` moves a point; Fin-3 axis choice exceeds
    bounce-swap; factor-swap covers step reversal. -/
theorem i1_canonicity_package :
    (∃ (U : Bool → Bool) (f g : TwoBounceFactor U),
      EndoInj U ∧ FactorsDisagree f g) ∧
    (∀ {α : Type} (U : α → α) (h : IsInvolution U),
      (∃ x, U x ≠ x) →
        FactorsDisagree (factor_involution U h) (factor_involution_rev U h)) ∧
    (FactorsDisagree factor_cycle3_axis0 factor_cycle3_axis1 ∧
      ¬ IsBounceSwap factor_cycle3_axis0 factor_cycle3_axis1) ∧
    (∀ {α : Type} (U : α → α) (f : TwoBounceFactor U),
      (∀ x, reverseOf f (U x) = x) ∧
      (∀ x, U (reverseOf f x) = x) ∧
      Nonempty (TwoBounceFactor (reverseOf f))) :=
  ⟨canonicity_fails,
   fun U h hx => (involutive_factor_reorder U h).mpr hx,
   factorization_gauge_exceeds_swap,
   fun U f => channel_swap_is_reversal U f⟩

/-- **I-1 two-bounce fragment.** Converse + spine ¬erase + existence on
    involutions / Bool / swapStep / every injection on `Fin n` +
    canonicity failure + channel-swap-is-reversal. -/
theorem i1_two_bounce_fragment :
    (∀ {α : Type} (U : α → α) (_f : TwoBounceFactor U), Lossless U) ∧
    (∀ {S E : Type} (U : S × E → S × E) (_f : TwoBounceFactor U),
      Geom.Registration.Inj U) ∧
    (∀ {α : Type} (U : α → α), IsInvolution U →
      Nonempty (TwoBounceFactor U)) ∧
    (∀ U : Bool → Bool, EndoInj U → Nonempty (TwoBounceFactor U)) ∧
    Nonempty (TwoBounceFactor Geom.Registration.swapStep) ∧
    (∀ {α : Type} (act : α → α), SymmetricStep act → ¬ Erasing act) ∧
    (∀ {n : Nat} (U : Fin n → Fin n), EndoInj U →
      Nonempty (TwoBounceFactor U)) ∧
    (∃ (U : Bool → Bool) (f g : TwoBounceFactor U),
      EndoInj U ∧ FactorsDisagree f g) ∧
    (∀ {α : Type} (U : α → α) (f : TwoBounceFactor U),
      (∀ x, reverseOf f (U x) = x) ∧
      (∀ x, U (reverseOf f x) = x) ∧
      Nonempty (TwoBounceFactor (reverseOf f))) :=
  ⟨fun _U => lossless_of_two_bounce _,
   fun _U => inj_of_two_bounce _,
   fun _U h => ⟨factor_involution _ h⟩,
   fun U h => ⟨factor_bool U h⟩,
   ⟨factor_swapStep⟩,
   fun act hs => symmetric_excludes_erase act hs,
   fun U h => ⟨factor_fin U h⟩,
   canonicity_fails,
   fun U f => channel_swap_is_reversal U f⟩

#print axioms Bridge.TwoBounce.symmetric_excludes_erase
#print axioms Bridge.TwoBounce.lossless_of_two_bounce
#print axioms Bridge.TwoBounce.inj_of_two_bounce
#print axioms Bridge.TwoBounce.factor_bool
#print axioms Bridge.TwoBounce.factor_fin
#print axioms Bridge.TwoBounce.canonicity_fails
#print axioms Bridge.TwoBounce.channel_swap_is_reversal
#print axioms Bridge.TwoBounce.i1_canonicity_package
#print axioms Bridge.TwoBounce.i1_two_bounce_fragment

end Bridge.TwoBounce
