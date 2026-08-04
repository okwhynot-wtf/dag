/-!
# Geom.Exhaustion

Under injective joint dynamics with scheduled merges, stream muteness, and
buffer confinement, capacity must satisfy `K ^ T ≤ |caps T|`. The constructive
contrapositive exhibits a failing tick.
-/

set_option linter.unusedSectionVars false

namespace Geom.Exhaustion

/-- List membership helpers. -/
theorem mem_head (a : α) (l : List α) : a ∈ a :: l := List.Mem.head l
theorem mem_tail (b : α) {a : α} {l : List α} (h : a ∈ l) : a ∈ b :: l :=
  List.Mem.tail b h

/-! ### List helpers -/

/-- Pairwise distinctness of a list. -/
def Distinct : List α → Prop
  | [] => True
  | x :: xs => (∀ y, y ∈ xs → x ≠ y) ∧ Distinct xs

/-- Removal of one occurrence (prelude-safe). -/
def remove [DecidableEq α] (a : α) : List α → List α
  | [] => []
  | x :: xs => if a = x then xs else x :: remove a xs

theorem length_remove_of_mem [DecidableEq α] {a : α} {l : List α}
    (h : a ∈ l) : (remove a l).length + 1 = l.length := by
  induction l with
  | nil => cases h
  | cons x xs ih =>
    by_cases hax : a = x
    · show (if a = x then xs else x :: remove a xs).length + 1 = xs.length + 1
      rw [if_pos hax]
    · show (if a = x then xs else x :: remove a xs).length + 1 = xs.length + 1
      rw [if_neg hax]
      have hmem : a ∈ xs := by
        cases h with
        | head => exact absurd rfl hax
        | tail _ hm => exact hm
      show (remove a xs).length + 1 + 1 = xs.length + 1
      rw [ih hmem]

theorem mem_remove [DecidableEq α] {a b : α} {l : List α}
    (hb : b ∈ l) (hne : b ≠ a) : b ∈ remove a l := by
  induction l with
  | nil => cases hb
  | cons x xs ih =>
    by_cases hax : a = x
    · show b ∈ (if a = x then xs else x :: remove a xs)
      rw [if_pos hax]
      cases hb with
      | head => exact absurd hax.symm hne
      | tail _ hm => exact hm
    · show b ∈ (if a = x then xs else x :: remove a xs)
      rw [if_neg hax]
      cases hb with
      | head => exact mem_head b _
      | tail _ hm => exact mem_tail x (ih hm)

/-- Pigeonhole: a pairwise-distinct list drawn from an alphabet is no
longer than the alphabet. -/
theorem length_le_of_distinct_mem [DecidableEq α] {l : List α} :
    ∀ {al : List α}, Distinct l → (∀ x, x ∈ l → x ∈ al) →
      l.length ≤ al.length := by
  induction l with
  | nil => intro al _ _; exact Nat.zero_le _
  | cons x xs ih =>
    intro al hd hmem
    have hx : x ∈ al := hmem x (mem_head x xs)
    have hsub : ∀ y, y ∈ xs → y ∈ remove x al := fun y hy =>
      mem_remove (hmem y (mem_tail x hy))
        (fun hyx => hd.1 y hy hyx.symm)
    have hlen := ih hd.2 hsub
    rw [← length_remove_of_mem hx]
    exact Nat.succ_le_succ hlen

/-- Membership elimination for `map`, axiom-free. -/
theorem exists_of_mem_map {f : α → β} {b : β} :
    ∀ {l : List α}, b ∈ l.map f → ∃ a, a ∈ l ∧ f a = b := by
  intro l
  induction l with
  | nil => intro h; cases h
  | cons x xs ih =>
    intro h
    have h' : b ∈ f x :: xs.map f := h
    cases h' with
    | head => exact ⟨x, mem_head x xs, rfl⟩
    | tail _ hm =>
      match ih hm with
      | ⟨a, ha, hfa⟩ => exact ⟨a, mem_tail x ha, hfa⟩

/-- Length of `map`, axiom-free. -/
theorem length_map_eq (f : α → β) :
    ∀ l : List α, (l.map f).length = l.length := by
  intro l
  induction l with
  | nil => rfl
  | cons x xs ih =>
    show (xs.map f).length + 1 = xs.length + 1
    rw [ih]

/-- Membership in an append, left side. -/
theorem mem_append_left (m : List α) {a : α} :
    ∀ {l : List α}, a ∈ l → a ∈ l ++ m := by
  intro l
  induction l with
  | nil => intro h; cases h
  | cons x xs ih =>
    intro h
    cases h with
    | head => exact mem_head a (xs ++ m)
    | tail _ h' => exact mem_tail x (ih h')

/-- Membership in an append, right side. -/
theorem mem_append_right {m : List α} {a : α} (h : a ∈ m) :
    ∀ l : List α, a ∈ l ++ m := by
  intro l
  induction l with
  | nil => exact h
  | cons x xs ih => exact mem_tail x ih

/-- Membership in an append, eliminated. -/
theorem mem_append_elim {a : α} :
    ∀ {l m : List α}, a ∈ l ++ m → a ∈ l ∨ a ∈ m := by
  intro l
  induction l with
  | nil => intro m h; exact Or.inr h
  | cons x xs ih =>
    intro m h
    have h' : a ∈ x :: (xs ++ m) := h
    cases h' with
    | head => exact Or.inl (mem_head a xs)
    | tail _ h'' =>
      match ih h'' with
      | Or.inl h1 => exact Or.inl (mem_tail x h1)
      | Or.inr h2 => exact Or.inr h2

/-- Length of an append, axiom-free. -/
theorem length_append :
    ∀ l m : List α, (l ++ m).length = l.length + m.length := by
  intro l m
  induction l with
  | nil =>
    show m.length = 0 + m.length
    rw [Nat.zero_add]
  | cons x xs ih =>
    show (xs ++ m).length + 1 = (xs.length + 1) + m.length
    rw [ih]
    calc xs.length + m.length + 1
        = xs.length + (m.length + 1) := Nat.add_assoc _ _ _
      _ = xs.length + (1 + m.length) := by rw [Nat.add_comm m.length 1]
      _ = xs.length + 1 + m.length := (Nat.add_assoc _ _ _).symm

/-- An append of distinct lists with no cross-membership is distinct. -/
theorem distinct_append :
    ∀ {l m : List α}, Distinct l → Distinct m →
      (∀ a, a ∈ l → a ∈ m → False) → Distinct (l ++ m) := by
  intro l
  induction l with
  | nil => intro m _ hm _; exact hm
  | cons x xs ih =>
    intro m hl hm hd
    refine ⟨?_, ?_⟩
    · intro y hy hxy
      match mem_append_elim hy with
      | Or.inl h1 => exact hl.1 y h1 hxy
      | Or.inr h2 => exact hd x (mem_head x xs) (hxy.symm ▸ h2)
    · exact ih hl.2 hm (fun a ha => hd a (mem_tail x ha))

/-- A map by a function injective on the list preserves distinctness. -/
theorem distinct_map_of_inj {f : α → β} :
    ∀ {l : List α}, Distinct l →
      (∀ a a', a ∈ l → a' ∈ l → f a = f a' → a = a') →
      Distinct (l.map f) := by
  intro l
  induction l with
  | nil => intro _ _; exact True.intro
  | cons x xs ih =>
    intro hd hinj
    refine ⟨?_, ?_⟩
    · intro y hy hxy
      match exists_of_mem_map hy with
      | ⟨a, ha, hfa⟩ =>
        exact hd.1 a ha
          (hinj x a (mem_head x xs) (mem_tail x ha) (hxy.trans hfa.symm))
    · exact ih hd.2
        (fun a a' ha ha' => hinj a a' (mem_tail x ha) (mem_tail x ha'))

/-- Concatenation of the images of a list-valued map (prelude flat-map). -/
def joinMap (f : α → List β) : List α → List β
  | [] => []
  | x :: xs => f x ++ joinMap f xs

theorem mem_joinMap {f : α → List β} {b : β} :
    ∀ {l : List α}, b ∈ joinMap f l → ∃ a, a ∈ l ∧ b ∈ f a := by
  intro l
  induction l with
  | nil => intro h; cases h
  | cons x xs ih =>
    intro h
    match mem_append_elim h with
    | Or.inl h1 => exact ⟨x, mem_head x xs, h1⟩
    | Or.inr h2 =>
      match ih h2 with
      | ⟨a, ha, hb⟩ => exact ⟨a, mem_tail x ha, hb⟩

/-- A join of per-point distinct blocks over a distinct index list with
pairwise-disjoint blocks is distinct. -/
theorem distinct_joinMap {f : α → List β} :
    ∀ {l : List α}, Distinct l →
      (∀ a, a ∈ l → Distinct (f a)) →
      (∀ a a', a ∈ l → a' ∈ l → a ≠ a' →
        ∀ b, b ∈ f a → b ∈ f a' → False) →
      Distinct (joinMap f l) := by
  intro l
  induction l with
  | nil => intro _ _ _; exact True.intro
  | cons x xs ih =>
    intro hl hf hdisj
    show Distinct (f x ++ joinMap f xs)
    apply distinct_append (hf x (mem_head x xs))
      (ih hl.2 (fun a ha => hf a (mem_tail x ha))
        (fun a a' ha ha' => hdisj a a' (mem_tail x ha) (mem_tail x ha')))
    intro b hbx hbj
    match mem_joinMap hbj with
    | ⟨a, ha, hba⟩ =>
      exact hdisj x a (mem_head x xs) (mem_tail x ha) (hl.1 a ha) b hbx hba

/-- A join of blocks each of length at least `N` over an index list of
length `L` has length at least `L * N`. -/
theorem length_joinMap_ge {f : α → List β} {N : Nat} :
    ∀ {l : List α}, (∀ a, a ∈ l → N ≤ (f a).length) →
      l.length * N ≤ (joinMap f l).length := by
  intro l
  induction l with
  | nil =>
    intro _
    show 0 * N ≤ 0
    rw [Nat.zero_mul]
    exact Nat.le_refl 0
  | cons x xs ih =>
    intro h
    show (xs.length + 1) * N ≤ (f x ++ joinMap f xs).length
    rw [length_append]
    have hs : (xs.length + 1) * N = xs.length * N + N := by
      rw [Nat.mul_comm (xs.length + 1) N, Nat.mul_add, Nat.mul_one,
          Nat.mul_comm N xs.length]
    rw [hs, Nat.add_comm (f x).length (joinMap f xs).length]
    exact Nat.add_le_add (ih (fun a ha => h a (mem_tail x ha)))
      (h x (mem_head x xs))

/-- Appending one element on the right is injective in both arguments. -/
theorem snoc_inj :
    ∀ (v w : List α) (e f : α), v ++ [e] = w ++ [f] → v = w ∧ e = f := by
  intro v
  induction v with
  | nil =>
    intro w e f h
    match w with
    | [] =>
      injection h with h1 _
      exact ⟨rfl, h1⟩
    | x :: w' =>
      injection h with _ h2
      match w' with
      | [] => injection h2
      | y :: w'' => injection h2
  | cons x v' ih =>
    intro w e f h
    match w with
    | [] =>
      injection h with _ h2
      match v' with
      | [] => injection h2
      | y :: v'' => injection h2
    | y :: w' =>
      injection h with h1 h2
      match ih w' e f h2 with
      | ⟨hvw, hef⟩ => exact ⟨by rw [h1, hvw], hef⟩

/-- `(t + 1) + m = t + (m + 1)`, reproved locally to keep the audit
independent of core arithmetic lemma footprints. -/
theorem succ_add_eq (t m : Nat) : (t + 1) + m = t + (m + 1) := by
  induction m with
  | zero => rfl
  | succ k ih =>
    show ((t + 1) + k) + 1 = (t + (k + 1)) + 1
    rw [ih]

/-- Monotonicity of `K ^ ·` for `K ≥ 1`, reproved locally. -/
theorem pow_mono {K : Nat} (hK : 1 ≤ K) :
    ∀ {s t : Nat}, s ≤ t → K ^ s ≤ K ^ t := by
  intro s t
  induction t with
  | zero =>
    intro hst
    cases Nat.eq_zero_of_le_zero hst
    exact Nat.le_refl _
  | succ n ih =>
    intro hst
    by_cases h : s = n + 1
    · rw [h]
      exact Nat.le_refl _
    · have hs' : s ≤ n := Nat.le_of_lt_succ (Nat.lt_of_le_of_ne hst h)
      have hstep : K ^ n * 1 ≤ K ^ n * K := Nat.mul_le_mul_left (K ^ n) hK
      rw [Nat.mul_one] at hstep
      show K ^ s ≤ K ^ n * K
      exact Nat.le_trans (ih hs') hstep

/-- Bounded search: a decidably failing bounded-`∀` over `Nat` yields a
witness below the bound (no classical axioms). -/
theorem exists_lt_not_of_not_forall {P : Nat → Prop} [DecidablePred P] :
    ∀ T : Nat, ¬ (∀ t, t < T → P t) → ∃ t, t < T ∧ ¬ P t := by
  intro T
  induction T with
  | zero =>
    intro h
    exact absurd (fun t ht => absurd ht (Nat.not_lt_zero t)) h
  | succ T ih =>
    intro h
    by_cases hT : P T
    · have h' : ¬ (∀ t, t < T → P t) := by
        intro hall
        apply h
        intro t ht
        by_cases htT : t = T
        · rw [htT]; exact hT
        · exact hall t (Nat.lt_of_le_of_ne (Nat.le_of_lt_succ ht) htT)
      match ih h' with
      | ⟨t, ht, hnp⟩ => exact ⟨t, Nat.lt_succ_of_lt ht, hnp⟩
    · exact ⟨T, Nat.lt_succ_self T, hT⟩

/-- Bounded search over a list: a decidably failing bounded-`∀` yields a
member witness (generalizes the spine's `exists_mem_not_of_not_ball`). -/
theorem exists_mem_not_of_not_ball {l : List α} {p : α → Prop}
    [DecidablePred p] (h : ¬ ∀ x, x ∈ l → p x) : ∃ x, x ∈ l ∧ ¬ p x := by
  induction l with
  | nil => exact absurd (fun x hx => nomatch hx) h
  | cons y ys ih =>
    by_cases hy : p y
    · have h' : ¬ ∀ x, x ∈ ys → p x := by
        intro hall
        apply h
        intro x hx
        cases hx with
        | head => exact hy
        | tail _ hm => exact hall x hm
      match ih h' with
      | ⟨x, hx, hnp⟩ => exact ⟨x, mem_tail y hx, hnp⟩
    · exact ⟨y, mem_head y ys, hy⟩

/-! ### The split environment: stream slot and internal buffer -/

variable {S Eout Eint : Type}

/-- The joint step is injective. -/
def Inj (U : S × Eout × Eint → S × Eout × Eint) : Prop :=
  ∀ a b, U a = U b → a = b

/-- Triple extensionality, prelude-safe. -/
theorem triple_ext {a b : S × Eout × Eint}
    (h1 : a.1 = b.1) (h2 : a.2.1 = b.2.1) (h3 : a.2.2 = b.2.2) : a = b := by
  match a, b with
  | (s, e, i), (t, f, j) =>
    cases h1
    cases h2
    cases h3
    rfl

/-- **Theorem A1, pairwise (the buffer absorbs what the stream
declines).** Under an injective joint step, a merged pair the stream slot
does not distinguish is distinguished by the internal buffer: Thm 3.1
with environment `Eout × Eint`, the record forced into the `Eint`
coordinate. Registration happens now; only its address is negotiable. -/
theorem buffer_absorbs {U : S × Eout × Eint → S × Eout × Eint}
    (hU : Inj U) {a b : S × Eout × Eint} (hab : a ≠ b)
    (hm : (U a).1 = (U b).1) (hs : (U a).2.1 = (U b).2.1) :
    (U a).2.2 ≠ (U b).2.2 :=
  fun hi => hab (hU a b (triple_ext hm hs hi))

/-- A1, distinctness clause: a merged fiber with a mute stream slot
writes pairwise-distinct buffer records. -/
theorem buffer_records_distinct {U : S × Eout × Eint → S × Eout × Eint}
    (hU : Inj U) (s : S) (r : Eout) :
    ∀ xs : List (S × Eout × Eint), Distinct xs →
      (∀ x, x ∈ xs → (U x).1 = s) →
      (∀ x, x ∈ xs → (U x).2.1 = r) →
      Distinct (xs.map (fun x => (U x).2.2)) := by
  intro xs
  induction xs with
  | nil => intro _ _ _; exact True.intro
  | cons x rest ih =>
    intro hd hsys hstr
    refine ⟨?_, ?_⟩
    · intro y hy hxy
      match exists_of_mem_map hy with
      | ⟨z, hz, hzy⟩ =>
        exact buffer_absorbs hU (hd.1 z hz)
          ((hsys x (mem_head x rest)).trans (hsys z (mem_tail x hz)).symm)
          ((hstr x (mem_head x rest)).trans (hstr z (mem_tail x hz)).symm)
          (hxy.trans hzy.symm)
    · exact ih hd.2 (fun z hz => hsys z (mem_tail x hz))
        (fun z hz => hstr z (mem_tail x hz))

/-- **Theorem A1 (buffer capacity bound).** `K ≤ |Eint|`, list form: a
`K`-fiber merged at the system marginal whose stream slot is mute has its
buffer records pairwise distinct inside any declared buffer alphabet, so
`K` is at most that alphabet's size. The ledger, aimed inward. -/
theorem buffer_capacity_bound [DecidableEq Eint]
    {U : S × Eout × Eint → S × Eout × Eint} (hU : Inj U) (s : S) (r : Eout)
    (xs : List (S × Eout × Eint)) (hd : Distinct xs)
    (hsys : ∀ x, x ∈ xs → (U x).1 = s)
    (hstr : ∀ x, x ∈ xs → (U x).2.1 = r)
    (Is : List Eint) (halph : ∀ x, x ∈ xs → (U x).2.2 ∈ Is) :
    xs.length ≤ Is.length := by
  have hdm := buffer_records_distinct hU s r xs hd hsys hstr
  have hlm : ∀ y, y ∈ xs.map (fun x => (U x).2.2) → y ∈ Is := fun y hy =>
    match exists_of_mem_map hy with
    | ⟨z, hz, hzy⟩ => hzy ▸ halph z hz
  have h := length_le_of_distinct_mem hdm hlm
  rw [length_map_eq] at h
  exact h

/-! ### Exhaustion: freshness is a resource that counting spends

A run is scheduled by a system trajectory `σ`, per-tick lists `es t` of
scheduled fresh units and `caps t` of admissible buffer values (the
capacity schedule -- for a horizon, the shrinking area). Tick `t` acts by
`U (σ t, e, i)`. Three per-tick clauses keep every premise explicit. -/

section Run

variable (U : S × Eout × Eint → S × Eout × Eint)
variable (σ : Nat → S) (es : Nat → List Eout) (caps : Nat → List Eint)

/-- Tick `t` merges its scheduled fresh units at the system marginal:
every scheduled unit, on every admissible buffer value, lands the system
on `σ (t+1)`. This is the `K`-merge clause, kept as a hypothesis. -/
def MergesAt (t : Nat) : Prop :=
  ∀ e, e ∈ es t → ∀ i, i ∈ caps t → (U (σ t, e, i)).1 = σ (t + 1)

/-- Stream muteness at tick `t`: outgoing unit constant across the merge
block. Alias: `Geom.Freshness.StreamMuteAt`. -/
def FreshAt (t : Nat) : Prop :=
  ∀ e, e ∈ es t → ∀ e', e' ∈ es t → ∀ i, i ∈ caps t → ∀ i', i' ∈ caps t →
    (U (σ t, e, i)).2.1 = (U (σ t, e', i')).2.1

/-- The buffer respects the capacity schedule: what tick `t` writes into
the buffer lies in the tick-`t+1` capacity list (area-as-record-capacity,
imported as a hypothesis, never derived). -/
def Confined (t : Nat) : Prop :=
  ∀ e, e ∈ es t → ∀ i, i ∈ caps t → (U (σ t, e, i)).2.2 ∈ caps (t + 1)

instance freshAtDecidable [DecidableEq Eout] (t : Nat) :
    Decidable (FreshAt U σ es caps t) :=
  List.decidableBAll
    (fun e => ∀ e', e' ∈ es t → ∀ i, i ∈ caps t → ∀ i', i' ∈ caps t →
      (U (σ t, e, i)).2.1 = (U (σ t, e', i')).2.1) (es t)

/-- Buffer evolution: thread the buffer through the listed fresh units,
tick by tick from tick `t`. The iterated composition of dilated ticks,
restricted to the record sector. -/
def evolve : Nat → Eint → List Eout → Eint
  | _, i, [] => i
  | t, i, e :: v => evolve (t + 1) (U (σ t, e, i)).2.2 v

/-- The fresh-choice vectors of a `T`-tick run: one scheduled unit per
tick, the tick-`T` choice appended last. -/
def freshVecs : Nat → List (List Eout)
  | 0 => [[]]
  | T + 1 => joinMap (fun v => (es T).map (fun e => v ++ [e])) (freshVecs T)

theorem freshVecs_zero_mem {v : List Eout} (hv : v ∈ freshVecs es 0) :
    v = [] := by
  cases hv with
  | head => rfl
  | tail _ h => cases h

theorem freshVecs_length_mem :
    ∀ {T : Nat} {v : List Eout}, v ∈ freshVecs es T → v.length = T := by
  intro T
  induction T with
  | zero =>
    intro v hv
    rw [freshVecs_zero_mem es hv]
    rfl
  | succ T ih =>
    intro v hv
    match mem_joinMap hv with
    | ⟨w, hw, hv'⟩ =>
      match exists_of_mem_map hv' with
      | ⟨e, _, hev⟩ =>
        rw [← hev, length_append, ih hw]
        exact rfl

/-- Peeling one tick off the fresh end of the evolution. -/
theorem evolve_snoc :
    ∀ (v : List Eout) (t : Nat) (i : Eint) (e : Eout),
      evolve U σ t i (v ++ [e]) =
        (U (σ (t + v.length), e, evolve U σ t i v)).2.2 := by
  intro v
  induction v with
  | nil => intro t i e; rfl
  | cons f v' ih =>
    intro t i e
    show evolve U σ (t + 1) (U (σ t, f, i)).2.2 (v' ++ [e]) =
      (U (σ (t + (v'.length + 1)), e,
        evolve U σ (t + 1) (U (σ t, f, i)).2.2 v')).2.2
    rw [ih (t + 1) ((U (σ t, f, i)).2.2) e, succ_add_eq]

/-- Confinement transports along the run: a scheduled evolution from an
admissible seed stays in the capacity schedule. -/
theorem evolve_confined :
    ∀ T : Nat, (∀ t, t < T → Confined U σ es caps t) →
      ∀ v, v ∈ freshVecs es T → ∀ i, i ∈ caps 0 →
        evolve U σ 0 i v ∈ caps T := by
  intro T
  induction T with
  | zero =>
    intro _ v hv i hi
    rw [freshVecs_zero_mem es hv]
    exact hi
  | succ T ih =>
    intro hc v hv i hi
    match mem_joinMap hv with
    | ⟨w, hw, hv'⟩ =>
      match exists_of_mem_map hv' with
      | ⟨e, he, hev⟩ =>
        rw [← hev, evolve_snoc, Nat.zero_add, freshVecs_length_mem es hw]
        exact hc T (Nat.lt_succ_self T) e he _
          (ih (fun t ht => hc t (Nat.lt_succ_of_lt ht)) w hw i hi)

/-- The engine: on a merging, fresh, confined run, buffer evolution is
injective jointly in the seed and the fresh-choice vector. Per tick this
is exactly A1 (`buffer_absorbs`); the induction composes it. -/
theorem evolve_inj (hU : Inj U) :
    ∀ T : Nat,
      (∀ t, t < T → MergesAt U σ es caps t) →
      (∀ t, t < T → FreshAt U σ es caps t) →
      (∀ t, t < T → Confined U σ es caps t) →
      ∀ v, v ∈ freshVecs es T → ∀ w, w ∈ freshVecs es T →
      ∀ i, i ∈ caps 0 → ∀ j, j ∈ caps 0 →
      evolve U σ 0 i v = evolve U σ 0 j w → i = j ∧ v = w := by
  intro T
  induction T with
  | zero =>
    intro _ _ _ v hv w hw i _ j _ he
    have hv0 := freshVecs_zero_mem es hv
    have hw0 := freshVecs_zero_mem es hw
    rw [hv0, hw0] at he
    exact ⟨he, hv0.trans hw0.symm⟩
  | succ T ih =>
    intro hm hf hc v hv w hw i hi j hj he
    match mem_joinMap hv with
    | ⟨v', hv', hvv⟩ =>
      match exists_of_mem_map hvv with
      | ⟨e, hev, hveq⟩ =>
        match mem_joinMap hw with
        | ⟨w', hw', hww⟩ =>
          match exists_of_mem_map hww with
          | ⟨f, hfw, hweq⟩ =>
            rw [← hveq, ← hweq, evolve_snoc, evolve_snoc, Nat.zero_add,
                Nat.zero_add, freshVecs_length_mem es hv',
                freshVecs_length_mem es hw'] at he
            have hiv : evolve U σ 0 i v' ∈ caps T :=
              evolve_confined U σ es caps T
                (fun t ht => hc t (Nat.lt_succ_of_lt ht)) v' hv' i hi
            have hjw : evolve U σ 0 j w' ∈ caps T :=
              evolve_confined U σ es caps T
                (fun t ht => hc t (Nat.lt_succ_of_lt ht)) w' hw' j hj
            have hmerge : (U (σ T, e, evolve U σ 0 i v')).1 =
                (U (σ T, f, evolve U σ 0 j w')).1 :=
              (hm T (Nat.lt_succ_self T) e hev _ hiv).trans
                (hm T (Nat.lt_succ_self T) f hfw _ hjw).symm
            have hfresh : (U (σ T, e, evolve U σ 0 i v')).2.1 =
                (U (σ T, f, evolve U σ 0 j w')).2.1 :=
              hf T (Nat.lt_succ_self T) e hev f hfw _ hiv _ hjw
            have hjoint := hU (σ T, e, evolve U σ 0 i v')
              (σ T, f, evolve U σ 0 j w')
              (triple_ext hmerge hfresh he)
            have hef : e = f := congrArg (fun p => p.2.1) hjoint
            have hbuf : evolve U σ 0 i v' = evolve U σ 0 j w' :=
              congrArg (fun p => p.2.2) hjoint
            match ih (fun t ht => hm t (Nat.lt_succ_of_lt ht))
                (fun t ht => hf t (Nat.lt_succ_of_lt ht))
                (fun t ht => hc t (Nat.lt_succ_of_lt ht))
                v' hv' w' hw' i hi j hj hbuf with
            | ⟨hij, hvw⟩ =>
              refine ⟨hij, ?_⟩
              rw [← hveq, ← hweq, hvw, hef]

/-- The fresh-choice vectors are pairwise distinct. -/
theorem freshVecs_distinct :
    ∀ T : Nat, (∀ t, t < T → Distinct (es t)) →
      Distinct (freshVecs es T) := by
  intro T
  induction T with
  | zero => intro _; exact ⟨fun y hy => (nomatch hy), True.intro⟩
  | succ T ih =>
    intro hes
    show Distinct (joinMap (fun v => (es T).map (fun e => v ++ [e]))
      (freshVecs es T))
    apply distinct_joinMap
      (ih (fun t ht => hes t (Nat.lt_succ_of_lt ht)))
      (fun v _ => distinct_map_of_inj (hes T (Nat.lt_succ_self T))
        (fun e e' _ _ heq => (snoc_inj v v e e' heq).2))
    intro v v' _ _ hne b hb hb'
    match exists_of_mem_map hb, exists_of_mem_map hb' with
    | ⟨e, _, hbe⟩, ⟨e', _, hbe'⟩ =>
      exact hne (snoc_inj v v' e e' (hbe.trans hbe'.symm)).1

/-- The run offers at least `K ^ T` fresh-choice vectors when every tick
schedules at least `K` fresh units. -/
theorem freshVecs_length_ge {K : Nat} :
    ∀ T : Nat, (∀ t, t < T → K ≤ (es t).length) →
      K ^ T ≤ (freshVecs es T).length := by
  intro T
  induction T with
  | zero =>
    intro _
    show (1 : Nat) ≤ 1
    exact Nat.le_refl 1
  | succ T ih =>
    intro h
    show K ^ T * K ≤ (joinMap (fun v => (es T).map (fun e => v ++ [e]))
      (freshVecs es T)).length
    have h1 : K ^ T ≤ (freshVecs es T).length :=
      ih (fun t ht => h t (Nat.lt_succ_of_lt ht))
    have h2 : (freshVecs es T).length * K ≤
        (joinMap (fun v => (es T).map (fun e => v ++ [e]))
          (freshVecs es T)).length :=
      length_joinMap_ge (fun v _ => by
        rw [length_map_eq]
        exact h T (Nat.lt_succ_self T))
    exact Nat.le_trans (Nat.mul_le_mul_right K h1) h2

/-- **Theorem A2/A3 (exhaustion).** Freshness through `T` ticks prices
the buffer: if every tick below `T` merges `K` scheduled fresh units at
the marginal with a mute stream and a schedule-confined buffer, then
`K ^ T ≤ |caps T|`. Powers and cardinalities only -- no logs, no
division. With an antitone schedule this is the shrinking-area clause;
`exhaustion_const` below is the fixed-buffer reading. -/
theorem exhaustion [DecidableEq Eint] (hU : Inj U) (T K : Nat)
    (hm : ∀ t, t < T → MergesAt U σ es caps t)
    (hf : ∀ t, t < T → FreshAt U σ es caps t)
    (hc : ∀ t, t < T → Confined U σ es caps t)
    (hdes : ∀ t, t < T → Distinct (es t))
    (hK : ∀ t, t < T → K ≤ (es t).length)
    (i₀ : Eint) (hi₀ : i₀ ∈ caps 0) :
    K ^ T ≤ (caps T).length := by
  have hfd : Distinct (freshVecs es T) := freshVecs_distinct es T hdes
  have hmap : Distinct ((freshVecs es T).map (evolve U σ 0 i₀)) :=
    distinct_map_of_inj hfd (fun v w hv hw heq =>
      (evolve_inj U σ es caps hU T hm hf hc v hv w hw i₀ hi₀ i₀ hi₀ heq).2)
  have hmem : ∀ y, y ∈ (freshVecs es T).map (evolve U σ 0 i₀) →
      y ∈ caps T := fun y hy =>
    match exists_of_mem_map hy with
    | ⟨v, hv, hvy⟩ => hvy ▸ evolve_confined U σ es caps T hc v hv i₀ hi₀
  have hlen := length_le_of_distinct_mem hmap hmem
  rw [length_map_eq] at hlen
  exact Nat.le_trans (freshVecs_length_ge es T hK) hlen

/-- **A2, contrapositive.** If the marginal keeps merging its `K ≥ ·`
scheduled units and the buffer stays schedule-confined, but tick-`T`
capacity is smaller than `K ^ T`, then at some tick `t < T` the stream
slot distinguishes a merged datum. The failing tick is obtained by
decidable bounded search. -/
theorem freshness_fails [DecidableEq Eout] [DecidableEq Eint]
    (hU : Inj U) (T K : Nat)
    (hm : ∀ t, t < T → MergesAt U σ es caps t)
    (hc : ∀ t, t < T → Confined U σ es caps t)
    (hdes : ∀ t, t < T → Distinct (es t))
    (hK : ∀ t, t < T → K ≤ (es t).length)
    (i₀ : Eint) (hi₀ : i₀ ∈ caps 0)
    (hcap : (caps T).length < K ^ T) :
    ∃ t, t < T ∧ ∃ e, e ∈ es t ∧ ∃ e', e' ∈ es t ∧
      ∃ i, i ∈ caps t ∧ ∃ i', i' ∈ caps t ∧
        (U (σ t, e, i)).2.1 ≠ (U (σ t, e', i')).2.1 := by
  have hnf : ¬ ∀ t, t < T → FreshAt U σ es caps t := by
    intro hf
    exact absurd (exhaustion U σ es caps hU T K hm hf hc hdes hK i₀ hi₀)
      (Nat.not_le_of_gt hcap)
  match exists_lt_not_of_not_forall T hnf with
  | ⟨t, ht, hnp⟩ =>
    refine ⟨t, ht, ?_⟩
    have hnp' : ¬ ∀ e, e ∈ es t →
        (∀ e', e' ∈ es t → ∀ i, i ∈ caps t → ∀ i', i' ∈ caps t →
          (U (σ t, e, i)).2.1 = (U (σ t, e', i')).2.1) := hnp
    match exists_mem_not_of_not_ball hnp' with
    | ⟨e, he, h1⟩ =>
      match exists_mem_not_of_not_ball h1 with
      | ⟨e', he', h2⟩ =>
        match exists_mem_not_of_not_ball h2 with
        | ⟨i, hi, h3⟩ =>
          match exists_mem_not_of_not_ball h3 with
          | ⟨i', hi', h4⟩ =>
            exact ⟨e, he, e', he', i, hi, i', hi', h4⟩

end Run

/-- **Theorem A2 (fixed buffer).** The constant-capacity reading:
`K ^ T ≤ |Eint|` for a fixed declared buffer alphabet `Is`. -/
theorem exhaustion_const [DecidableEq Eint]
    {U : S × Eout × Eint → S × Eout × Eint}
    (σ : Nat → S) (es : Nat → List Eout) (Is : List Eint)
    (hU : Inj U) (T K : Nat)
    (hm : ∀ t, t < T → MergesAt U σ es (fun _ => Is) t)
    (hf : ∀ t, t < T → FreshAt U σ es (fun _ => Is) t)
    (hc : ∀ t, t < T → Confined U σ es (fun _ => Is) t)
    (hdes : ∀ t, t < T → Distinct (es t))
    (hK : ∀ t, t < T → K ≤ (es t).length)
    (i₀ : Eint) (hi₀ : i₀ ∈ Is) :
    K ^ T ≤ Is.length :=
  exhaustion U σ es (fun _ => Is) hU T K hm hf hc hdes hK i₀ hi₀

/-! ### A3, the schedule clauses: the exhaustion tick is well defined
and antitone in the capacity schedule.

Read `c t` as `(caps t).length`. The set of *alive* horizons
`{T : K ^ T ≤ c T}` is downward closed for `K ≥ 1` and an antitone
schedule, so `t* := max {T : K ^ T ≤ c T}` -- the exhaustion tick, the
model's Page time -- is well defined; and a pointwise smaller schedule
keeps no horizon alive that the larger one kills. -/

/-- Downward closure of the alive set: for `K ≥ 1` and an antitone
capacity schedule, a horizon below an alive horizon is alive. -/
theorem alive_downclosed {c : Nat → Nat}
    (hc : ∀ s t : Nat, s ≤ t → c t ≤ c s) {K : Nat} (hK : 1 ≤ K)
    {s t : Nat} (hst : s ≤ t) (halive : K ^ t ≤ c t) : K ^ s ≤ c s :=
  Nat.le_trans (pow_mono hK hst) (Nat.le_trans halive (hc s t hst))

/-- The exhaustion tick is antitone in the capacity schedule
(comparison form): every horizon alive under the smaller schedule is
alive under the larger, so `t*` cannot grow when capacity shrinks. -/
theorem exhaustion_tick_antitone {c c' : Nat → Nat}
    (h : ∀ t, c' t ≤ c t) {K T : Nat}
    (halive : K ^ T ≤ c' T) : K ^ T ≤ c T :=
  Nat.le_trans halive (h T)

end Geom.Exhaustion

-- #print axioms
#print axioms Geom.Exhaustion.length_remove_of_mem
#print axioms Geom.Exhaustion.mem_remove
#print axioms Geom.Exhaustion.length_le_of_distinct_mem
#print axioms Geom.Exhaustion.exists_of_mem_map
#print axioms Geom.Exhaustion.length_map_eq
#print axioms Geom.Exhaustion.mem_append_left
#print axioms Geom.Exhaustion.mem_append_right
#print axioms Geom.Exhaustion.mem_append_elim
#print axioms Geom.Exhaustion.length_append
#print axioms Geom.Exhaustion.distinct_append
#print axioms Geom.Exhaustion.distinct_map_of_inj
#print axioms Geom.Exhaustion.mem_joinMap
#print axioms Geom.Exhaustion.distinct_joinMap
#print axioms Geom.Exhaustion.length_joinMap_ge
#print axioms Geom.Exhaustion.snoc_inj
#print axioms Geom.Exhaustion.succ_add_eq
#print axioms Geom.Exhaustion.pow_mono
#print axioms Geom.Exhaustion.exists_lt_not_of_not_forall
#print axioms Geom.Exhaustion.exists_mem_not_of_not_ball
#print axioms Geom.Exhaustion.triple_ext
#print axioms Geom.Exhaustion.buffer_absorbs
#print axioms Geom.Exhaustion.buffer_records_distinct
#print axioms Geom.Exhaustion.buffer_capacity_bound
#print axioms Geom.Exhaustion.freshVecs_zero_mem
#print axioms Geom.Exhaustion.freshVecs_length_mem
#print axioms Geom.Exhaustion.evolve_snoc
#print axioms Geom.Exhaustion.evolve_confined
#print axioms Geom.Exhaustion.evolve_inj
#print axioms Geom.Exhaustion.freshVecs_distinct
#print axioms Geom.Exhaustion.freshVecs_length_ge
#print axioms Geom.Exhaustion.exhaustion
#print axioms Geom.Exhaustion.freshness_fails
#print axioms Geom.Exhaustion.exhaustion_const
#print axioms Geom.Exhaustion.alive_downclosed
#print axioms Geom.Exhaustion.exhaustion_tick_antitone
