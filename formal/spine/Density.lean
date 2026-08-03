import Canon
import Ladder

/-!
# Density — three counting identities of the structure

Nat-arithmetic consequences of fundamentality, liveness, and the ω-ladder.
No `Rat`/`Real`, no asymptotics library, no `Fintype` cardinality proofs.

* **1/4** (`fundamental_density`, `fundamentals_only_at_two`): among the four
  Bool endomaps exactly one is a fundamental (`¬`); fundamentals on `Fin n` exist
  only at `n = 2`. Checked by enumeration.
* **Live count** (`liveCount`, `endoCount`): the *combinatorial* counts
  `(n-1)^n` and `n^n`. These are definitions, not a proof that
  `| { f : Fin n → Fin n // Live f } | = (n-1)^n`. The fundamental case
  `liveCount 2 = 1`, `endoCount 2 = 4` matches the Bool enumeration.
  The analytic limit `(1-1/n)^n → 1/e` is **not** formalised here.
* **3/2** (`articulation_mass`, `levelCard_eq`): level `k` has `k+2`
  elements; the partial-sum closed form
  `articNum (N+1) + (N+4) = 3 * 2^(N+1)` is the cleared Nat form of
  `Σ_{k=0}^{N} (k+2)/2^(k+2) = 3/2 − (N+4)/2^(N+2)`. The infinite-sum
  reading is **not** a Lean theorem about reals.

No declared axioms.
-/
namespace Density

open Orbit

/-! ## Fundamental density 1/4 (`fundamental_density`) -/

/-- The four endomaps on the two-point carrier. -/
inductive BoolEndo
  | identity
  | constFalse
  | constTrue
  | negate
  deriving DecidableEq

/-- Interpret a `BoolEndo` as a function. -/
def BoolEndo.apply : BoolEndo → (Bool → Bool)
  | .identity => id
  | .constFalse => fun _ => false
  | .constTrue => fun _ => true
  | .negate => not

/-- Every Bool endomap is one of the four. -/
theorem boolEndo_complete (f : Bool → Bool) :
    ∃ e : BoolEndo, ∀ b, f b = e.apply b := by
  cases hf : f false with
  | false =>
    cases ht : f true with
    | false =>
      refine ⟨.constFalse, ?_⟩
      intro b; cases b <;> (first | exact hf | exact ht)
    | true =>
      refine ⟨.identity, ?_⟩
      intro b; cases b <;> (first | exact hf | exact ht)
  | true =>
    cases ht : f true with
    | false =>
      refine ⟨.negate, ?_⟩
      intro b; cases b <;> (first | exact hf | exact ht)
    | true =>
      refine ⟨.constTrue, ?_⟩
      intro b; cases b <;> (first | exact hf | exact ht)

/-- Pointwise equality with `not` yields fundamentality, without `funext`. -/
theorem bool_isFundamental_of_eq_not (f : Bool → Bool) (hf : ∀ b, f b = !b) :
    Canon.IsFundamental f := by
  refine ⟨?unoriented, ⟨true, ?surj, ?inj⟩⟩
  · intro x y h
    change y = f x at h
    subst h
    show x = f (f x)
    calc
      x = !(!x) := by cases x <;> rfl
      _ = !(f x) := by rw [hf x]
      _ = f (f x) := by rw [hf (f x)]
  · intro x
    cases x with
    | true => exact ⟨true, rfl⟩
    | false => exact ⟨false, hf true⟩
  · intro b b' h
    cases b with
    | true =>
      cases b' with
      | true => rfl
      | false =>
        change true = f true at h
        exact Bool.noConfusion (h.trans (hf true))
    | false =>
      cases b' with
      | true =>
        change f true = true at h
        exact Bool.noConfusion ((hf true).symm.trans h)
      | false => rfl

/-- On Bool, fundamentality coincides with reading as `not`. -/
theorem bool_fundamental_iff_not (f : Bool → Bool) :
    Canon.IsFundamental f ↔ ∀ b, f b = !b := by
  constructor
  · intro h b; exact TwoCycle.bool_live_is_not f h.live b
  · exact bool_isFundamental_of_eq_not f

/-- Exactly one of the four Bool endomaps is a fundamental. -/
theorem boolEndo_fundamental_iff (e : BoolEndo) :
    Canon.IsFundamental e.apply ↔ e = .negate := by
  constructor
  · intro h
    have hf : ∀ b, e.apply b = !b := (bool_fundamental_iff_not e.apply).mp h
    cases e with
    | identity => exact absurd (hf false) (by decide)
    | constFalse => exact absurd (hf false) (by decide)
    | constTrue => exact absurd (hf true) (by decide)
    | negate => rfl
  · intro he
    cases he
    exact Canon.canon_is_fundamental

/-- Non-fundamentals among the four each rest somewhere (rest / erasure). -/
theorem boolEndo_excluded_rests (e : BoolEndo) (hne : e ≠ .negate) :
    ∃ x : Bool, e.apply x = x := by
  cases e with
  | identity => exact ⟨false, rfl⟩
  | constFalse => exact ⟨false, rfl⟩
  | constTrue => exact ⟨true, rfl⟩
  | negate => exact absurd rfl hne

theorem boolEndo_apply_ext (e e' : BoolEndo) (h : ∀ b, e.apply b = e'.apply b) :
    e = e' := by
  cases e <;> cases e' <;> first
    | rfl
    | exact absurd (h false) (by decide)
    | exact absurd (h true) (by decide)

/-- Fundamental density: four Bool endomaps, exactly one fundamental (`¬`);
    the other three rest somewhere. -/
theorem fundamental_density :
    (∀ f : Bool → Bool, ∃ e : BoolEndo, ∀ b, f b = e.apply b) ∧
    (∀ e : BoolEndo, Canon.IsFundamental e.apply ↔ e = BoolEndo.negate) ∧
    (∀ e : BoolEndo, e ≠ BoolEndo.negate → ∃ x, e.apply x = x) :=
  ⟨boolEndo_complete, boolEndo_fundamental_iff, boolEndo_excluded_rests⟩

/-- Fundamentality forces the carrier to have exactly two elements. -/
theorem fundamental_two_elements {α : Type} (act : α → α) (h : Canon.IsFundamental act) :
    ∃ a b : α, a ≠ b ∧ ∀ x : α, x = a ∨ x = b := by
  obtain ⟨z, hsurj, _hinj⟩ := h.iso_at
  refine ⟨z, act z, (h.live z).symm, ?_⟩
  intro x
  obtain ⟨bx, hbx⟩ := hsurj x
  cases bx with
  | true => exact Or.inl hbx.symm
  | false => exact Or.inr hbx.symm

theorem fin_val_ne {n : Nat} {i j : Fin n} (h : i.val ≠ j.val) : i ≠ j :=
  fun heq => h (congrArg Fin.val heq)

/-- No fundamental exists on `Fin n` for `n ≥ 3`. -/
theorem no_fundamental_fin_ge_three (n : Nat) (hn : 3 ≤ n) (act : Fin n → Fin n) :
    ¬ Canon.IsFundamental act := by
  intro h
  obtain ⟨a, b, _hab, hall⟩ := fundamental_two_elements act h
  have h0 : 0 < n := Nat.lt_of_lt_of_le (by decide : 0 < 3) hn
  have h1 : 1 < n := Nat.lt_of_lt_of_le (by decide : 1 < 3) hn
  have h2 : 2 < n := Nat.lt_of_lt_of_le (by decide : 2 < 3) hn
  let x0 : Fin n := ⟨0, h0⟩
  let x1 : Fin n := ⟨1, h1⟩
  let x2 : Fin n := ⟨2, h2⟩
  have d01 : x0 ≠ x1 := fin_val_ne (by decide : (0 : Nat) ≠ 1)
  have d02 : x0 ≠ x2 := fin_val_ne (by decide : (0 : Nat) ≠ 2)
  have d12 : x1 ≠ x2 := fin_val_ne (by decide : (1 : Nat) ≠ 2)
  match hall x0, hall x1, hall x2 with
  | .inl e0, .inl e1, _ => exact d01 (e0.trans e1.symm)
  | .inl e0, .inr _, .inl e2 => exact d02 (e0.trans e2.symm)
  | .inl _, .inr e1, .inr e2 => exact d12 (e1.trans e2.symm)
  | .inr e0, .inl e1, .inl e2 => exact d12 (e1.trans e2.symm)
  | .inr e0, .inl _, .inr e2 => exact d02 (e0.trans e2.symm)
  | .inr e0, .inr e1, _ => exact d01 (e0.trans e1.symm)

theorem fin_one_eq (x y : Fin 1) : x = y :=
  Fin.eq_of_val_eq (Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ x.isLt)
    |>.trans (Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ y.isLt)).symm)

/-- Fundamentals on `Fin n` exist only at size `n = 2`. -/
theorem fundamentals_only_at_two (n : Nat) (act : Fin n → Fin n) :
    Canon.IsFundamental act → n = 2 := by
  intro h
  match n with
  | 0 =>
    obtain ⟨z, _, _⟩ := h.iso_at
    exact Fin.elim0 z
  | 1 =>
    exact absurd (fin_one_eq (act ⟨0, by decide⟩) ⟨0, by decide⟩)
      (h.live ⟨0, by decide⟩)
  | 2 => rfl
  | n + 3 =>
    exact absurd h (no_fundamental_fin_ge_three (n + 3) (Nat.le_add_left 3 n) act)

/-! ## Combinatorial live / endomap counts

`endoCount n := n ^ n` and `liveCount n := (n - 1) ^ n` are the standard
product counts (choose any / any non-fixed image at each of `n` points).
They are **definitions**. There is no theorem here identifying them with
`Fintype.card` of function spaces. What is checked: the definitions, the
fundamental values `1` and `4`, and agreement with the Bool enumeration. -/

/-- Combinatorial product count of endomaps on an `n`-element carrier. -/
def endoCount (n : Nat) : Nat := n ^ n

/-- Combinatorial product count of fixed-point-free assignments on an
    `n`-element carrier (`n − 1` choices at each of `n` points). -/
def liveCount (n : Nat) : Nat := (n - 1) ^ n

/-- Unfolding the combinatorial definitions (definitional, not a
    cardinality-of-functions theorem). -/
theorem live_count_formula (n : Nat) :
    liveCount n = (n - 1) ^ n ∧ endoCount n = n ^ n :=
  ⟨rfl, rfl⟩

/-- At carrier size two, the combinatorial counts are `1` and `4`. -/
theorem live_count_at_fundamental :
    liveCount 2 = 1 ∧ endoCount 2 = 4 ∧ liveCount 2 * 4 = endoCount 2 := by
  decide

/-- The combinatorial fundamental counts match the Bool enumeration:
    exactly one of the four endomaps is live. -/
theorem liveCount_matches_bool_enum :
    liveCount 2 = 1 ∧
    (∀ e : BoolEndo, Live e.apply ↔ e = BoolEndo.negate) := by
  refine ⟨rfl, ?_⟩
  intro e
  constructor
  · intro hl
    have : Canon.IsFundamental e.apply := bool_isFundamental_of_eq_not e.apply
      (TwoCycle.bool_live_is_not e.apply hl)
    exact (boolEndo_fundamental_iff e).mp this
  · intro he
    cases he
    exact TwoCycle.bool_fundamental.1

/-- Package: combinatorial identities plus fundamental case matching the
    Bool enumeration. No analytic limit is claimed. -/
theorem live_count_package :
    (∀ n, liveCount n = (n - 1) ^ n ∧ endoCount n = n ^ n) ∧
    (liveCount 2 = 1 ∧ endoCount 2 = 4) ∧
    (∀ e : BoolEndo, Live e.apply ↔ e = BoolEndo.negate) :=
  ⟨live_count_formula,
   And.intro live_count_at_fundamental.1 live_count_at_fundamental.2.1,
   fun e => (liveCount_matches_bool_enum).2 e⟩

/-- Deprecated name for `live_count_at_fundamental`. -/
theorem live_density_at_fundamental :
    liveCount 2 = 1 ∧ endoCount 2 = 4 ∧ liveCount 2 * 4 = endoCount 2 :=
  live_count_at_fundamental

/-- Deprecated name for the combinatorial package (no `1/e` claim). -/
theorem live_density_package :
    (∀ n, liveCount n = (n - 1) ^ n ∧ endoCount n = n ^ n) ∧
    (liveCount 2 = 1 ∧ endoCount 2 = 4) :=
  ⟨live_count_formula, And.intro live_count_at_fundamental.1 live_count_at_fundamental.2.1⟩

/-! ## Articulation mass 3/2 -/

/-- Cardinality of `Ladder.Level k`, matching the Option-tower. -/
def levelCard : Nat → Nat
  | 0 => 2
  | k + 1 => levelCard k + 1

theorem levelCard_eq (k : Nat) : levelCard k = k + 2 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    calc
      levelCard (k + 1) = levelCard k + 1 := rfl
      _ = (k + 2) + 1 := by rw [ih]
      _ = (k + 1) + 2 := by
        rw [Nat.add_assoc, Nat.add_comm 2 1, ← Nat.add_assoc]

/-! ## No retraction

The past embeds forward; no injection runs from a level back to its
predecessor. Encoding levels as bounded Nats yields a pigeonhole. -/

/-- Enumerate `Level k` as a Nat in `0 .. k+1`. -/
def levelToNat : (k : Nat) → Ladder.Level k → Nat
  | 0, true => 0
  | 0, false => 1
  | _ + 1, none => 0
  | k + 1, some a => levelToNat k a + 1

theorem levelToNat_lt : ∀ (k : Nat) (x : Ladder.Level k), levelToNat k x < k + 2
  | 0, true => by decide
  | 0, false => by decide
  | k + 1, none => Nat.zero_lt_succ (k + 2)
  | k + 1, some a => Nat.succ_lt_succ (levelToNat_lt k a)

/-- Decode a Nat below `k+2` back to `Level k`. -/
def natToLevel : (k : Nat) → (n : Nat) → n < k + 2 → Ladder.Level k
  | 0, 0, _ => true
  | 0, 1, _ => false
  | 0, n + 2, h =>
    False.elim (Nat.not_lt_zero n
      (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ h)))
  | _ + 1, 0, _ => none
  | k + 1, n + 1, h => some (natToLevel k n (Nat.lt_of_succ_lt_succ h))

theorem levelToNat_natToLevel :
    ∀ (k : Nat) (n : Nat) (h : n < k + 2),
      levelToNat k (natToLevel k n h) = n
  | 0, 0, _ => rfl
  | 0, 1, _ => rfl
  | 0, n + 2, h =>
    False.elim (Nat.not_lt_zero n
      (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ h)))
  | _ + 1, 0, _ => rfl
  | k + 1, n + 1, h =>
    show levelToNat k (natToLevel k n (Nat.lt_of_succ_lt_succ h)) + 1 = n + 1 from
      congrArg Nat.succ (levelToNat_natToLevel k n (Nat.lt_of_succ_lt_succ h))

theorem levelToNat_inj :
    ∀ (k : Nat) (x y : Ladder.Level k),
      levelToNat k x = levelToNat k y → x = y
  | 0, true, true, _ => rfl
  | 0, true, false, h => by cases h
  | 0, false, true, h => by cases h
  | 0, false, false, _ => rfl
  | _ + 1, none, none, _ => rfl
  | _ + 1, none, some _, h => by cases h
  | _ + 1, some _, none, h => by cases h
  | k + 1, some a, some b, h =>
    congrArg some (levelToNat_inj k a b (Nat.succ.inj h))

/-- Among `f 0`, …, `f n`, some value equals `target`, or none does. -/
theorem find_target_or_miss (n : Nat) (target : Nat) (f : Nat → Nat) :
    (∃ t, t < n + 1 ∧ f t = target) ∨ (∀ t, t < n + 1 → f t ≠ target) := by
  induction n with
  | zero =>
    if h : f 0 = target then
      exact Or.inl ⟨0, Nat.zero_lt_one, h⟩
    else
      apply Or.inr
      intro t ht
      match t with
      | 0 => exact h
      | t + 1 =>
        exact absurd (Nat.lt_of_succ_lt_succ ht) (Nat.not_lt_zero t)
  | succ n ih =>
    cases ih with
    | inl hex =>
      obtain ⟨t, ht, he⟩ := hex
      exact Or.inl ⟨t, Nat.lt_trans ht (Nat.lt_succ_self (n + 1)), he⟩
    | inr hmiss =>
      if h : f (n + 1) = target then
        exact Or.inl ⟨n + 1, Nat.lt_succ_self (n + 1), h⟩
      else
        apply Or.inr
        intro t ht
        if htn : t = n + 1 then
          rw [htn]; exact h
        else
          have ht' : t < n + 1 := Nat.lt_of_le_of_ne (Nat.le_of_lt_succ ht) htn
          exact hmiss t ht'

/-- No injection of `n+1` distinct Nats into `{0, …, n-1}`. -/
theorem no_distinct_large :
    ∀ (n : Nat) (f : Nat → Nat),
      (∀ i, i < n + 1 → f i < n) →
      (∀ i j, i < n + 1 → j < n + 1 → f i = f j → i = j) →
      False
  | 0, f, hb, _hinj =>
    Nat.not_lt_zero (f 0) (hb 0 Nat.zero_lt_one)
  | n + 1, f, hb, hinj => by
    cases find_target_or_miss (n + 1) n f with
    | inr hmiss =>
      have hb' : ∀ i, i < n + 1 → f i < n := by
        intro i hi
        have hbound := hb i (Nat.lt_trans hi (Nat.lt_succ_self (n + 1)))
        have hne := hmiss i (Nat.lt_trans hi (Nat.lt_succ_self (n + 1)))
        exact Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hbound) hne
      have hinj' : ∀ i j, i < n + 1 → j < n + 1 → f i = f j → i = j := by
        intro i j hi hj he
        exact hinj i j (Nat.lt_trans hi (Nat.lt_succ_self (n + 1)))
          (Nat.lt_trans hj (Nat.lt_succ_self (n + 1))) he
      exact no_distinct_large n f hb' hinj'
    | inl hex =>
      obtain ⟨t, ht, hft⟩ := hex
      let skip (i : Nat) : Nat := if i < t then i else i + 1
      let f' (i : Nat) : Nat := f (skip i)
      have hskip_bound : ∀ i, i < n + 1 → skip i < n + 2 := by
        intro i hi
        dsimp [skip]
        split
        · next h => exact Nat.lt_trans h ht
        · next _ => exact Nat.succ_lt_succ hi
      have hb' : ∀ i, i < n + 1 → f' i < n := by
        intro i hi
        have hsi : skip i < n + 2 := hskip_bound i hi
        have hbound : f (skip i) < n + 1 := hb (skip i) hsi
        have hne_t : skip i ≠ t := by
          dsimp [skip]; split
          · next h => exact Nat.ne_of_lt h
          · next h => exact Nat.ne_of_gt (Nat.lt_succ_of_le (Nat.le_of_not_lt h))
        have hne : f (skip i) ≠ n := by
          intro he
          exact hne_t (hinj (skip i) t hsi ht (he.trans hft.symm))
        exact Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hbound) hne
      have hinj' : ∀ i j, i < n + 1 → j < n + 1 → f' i = f' j → i = j := by
        intro i j hi hj heq
        have hi' := hskip_bound i hi
        have hj' := hskip_bound j hj
        have hskip_eq : skip i = skip j := hinj (skip i) (skip j) hi' hj' heq
        dsimp [skip] at hskip_eq
        split at hskip_eq
        · next hi_lt =>
          split at hskip_eq
          · next hj_lt => exact hskip_eq
          · next hj_ge =>
            have : j + 1 < t := by rw [← hskip_eq]; exact hi_lt
            exact absurd (Nat.le_trans (Nat.le_of_lt this) (Nat.le_of_not_lt hj_ge))
              (Nat.not_succ_le_self j)
        · next hi_ge =>
          split at hskip_eq
          · next hj_lt =>
            have : i + 1 < t := by rw [hskip_eq]; exact hj_lt
            exact absurd (Nat.le_trans (Nat.le_of_lt this) (Nat.le_of_not_lt hi_ge))
              (Nat.not_succ_le_self i)
          · next hj_ge =>
            exact Nat.succ.inj hskip_eq
      exact no_distinct_large n f' hb' hinj'

/-- No injection from Level `k+1` into Level `k`: each tick strictly
    outgrows its predecessor, so self-articulation is irreversible. -/
theorem no_retraction (k : Nat) :
    ¬ ∃ (f : Ladder.Level (k + 1) → Ladder.Level k),
      ∀ x y, f x = f y → x = y := by
  intro ⟨f, hinj⟩
  let g (i : Nat) : Nat :=
    if h : i < k + 3 then levelToNat k (f (natToLevel (k + 1) i h)) else 0
  have hg : ∀ i (hi : i < k + 3),
      g i = levelToNat k (f (natToLevel (k + 1) i hi)) := by
    intro i hi; exact dif_pos hi
  have hb : ∀ i, i < (k + 2) + 1 → g i < k + 2 := by
    intro i hi; rw [hg i hi]; exact levelToNat_lt k _
  have hginj : ∀ i j, i < (k + 2) + 1 → j < (k + 2) + 1 → g i = g j → i = j := by
    intro i j hi hj heq
    have heq' : levelToNat k (f (natToLevel (k + 1) i hi)) =
                levelToNat k (f (natToLevel (k + 1) j hj)) := by
      rw [← hg i hi, ← hg j hj, heq]
    have hlev := levelToNat_inj k _ _ heq'
    have hdom := hinj _ _ hlev
    have hnat := congrArg (fun x => levelToNat (k + 1) x) hdom
    rw [levelToNat_natToLevel, levelToNat_natToLevel] at hnat
    exact hnat
  exact no_distinct_large (k + 2) g hb hginj

/-- Number of Bool-valued predicates on level `k`. -/
def predicateCount (k : Nat) : Nat := 2 ^ levelCard k

theorem predicateCount_eq (k : Nat) : predicateCount k = 2 ^ (k + 2) := by
  rw [predicateCount, levelCard_eq]

/-- Numerator of the partial articulation sum
    `Σ_{k < n} (k+2)/2^{k+2}` when written over denominator `2^{n+1}`. -/
def articNum : Nat → Nat
  | 0 => 0
  | n + 1 => 2 * articNum n + (n + 2)

theorem two_three_pow (n : Nat) :
    2 * (3 * 2 ^ n) = 3 * 2 ^ (n + 1) := by
  have h : 2 * (3 * 2 ^ n) = 3 * (2 * 2 ^ n) := by
    rw [Nat.two_mul (3 * 2 ^ n), Nat.two_mul (2 ^ n), Nat.mul_add]
  rw [h, ← Nat.pow_succ']

theorem artic_add_helper (n : Nat) :
    n + 2 + (n + 4) = 2 * (n + 3) := by
  calc
    n + 2 + (n + 4) = n + (2 + (n + 4)) := Nat.add_assoc n 2 (n + 4)
    _ = n + (n + (2 + 4)) := by
      rw [Nat.add_comm 2 (n + 4), Nat.add_assoc]
    _ = n + (n + 6) := rfl
    _ = (n + n) + 6 := (Nat.add_assoc n n 6).symm
    _ = 2 * n + 6 := by rw [Nat.two_mul]
    _ = 2 * n + 2 * 3 := rfl
    _ = 2 * (n + 3) := (Nat.mul_add 2 n 3).symm

/-- Closed Nat form: `articNum n + (n+3) = 3 · 2^n`.
    Equivalent (over denominator `2^{n+1}`) to
    `Σ_{k < n} (k+2)/2^{k+2} = 3/2 − (n+3)/2^{n+1}`.
    No real-analytic infinite sum is claimed. -/
theorem articulation_mass (n : Nat) :
    articNum n + (n + 3) = 3 * 2 ^ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have ih2 : 2 * articNum n + 2 * (n + 3) = 2 * (3 * 2 ^ n) := by
      rw [← Nat.mul_add, ih]
    calc
      articNum (n + 1) + (n + 4)
        = 2 * articNum n + (n + 2) + (n + 4) := rfl
      _ = 2 * articNum n + (n + 2 + (n + 4)) := Nat.add_assoc _ _ _
      _ = 2 * articNum n + 2 * (n + 3) := by rw [artic_add_helper]
      _ = 2 * (3 * 2 ^ n) := ih2
      _ = 3 * 2 ^ (n + 1) := two_three_pow n

/-- Inclusive indexing: cleared form of
    `Σ_{k=0}^{N} (k+2)/2^{k+2} = 3/2 − (N+4)/2^{N+2}`. -/
theorem articulation_partial_sum (N : Nat) :
    articNum (N + 1) + (N + 4) = 3 * 2 ^ (N + 1) :=
  articulation_mass (N + 1)

/-- Unarticulated raw count at level `k`: predicates minus elements. -/
def unarticCount (k : Nat) : Nat := 2 ^ (k + 2) - (k + 2)

/-! ## Package -/

/-- The three checked counting identities, gathered. -/
theorem three_constants :
    ((∀ f : Bool → Bool, ∃ e : BoolEndo, ∀ b, f b = e.apply b) ∧
      (∀ e : BoolEndo, Canon.IsFundamental e.apply ↔ e = BoolEndo.negate)) ∧
    (liveCount 2 = 1 ∧ endoCount 2 = 4) ∧
    (∀ n, articNum n + (n + 3) = 3 * 2 ^ n) ∧
    (∀ k, levelCard k = k + 2) :=
  ⟨⟨boolEndo_complete, boolEndo_fundamental_iff⟩,
   And.intro live_count_at_fundamental.1 live_count_at_fundamental.2.1,
   articulation_mass,
   levelCard_eq⟩

end Density
