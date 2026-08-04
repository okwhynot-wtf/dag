import Geom.Ledger

/-!
# Obs.Selection

Observer selection on a finite swap conveyor.

A **state** is the system bit together with `N` environment cells
(`Bool × List Bool`). Tick `t` exchanges the system bit with cell `t % N`
(`step`); `forwardFrom x0 D N` runs phases `0, …, D-1`.

Fiducial (product) initials are the blank-cell states (`fiducials`);
`Prop_D` (`propList`) is their image under `forwardFrom · D N`. The
depth-`D` **observer stock** (`stock`) is the system bit with cells
`0 … D-1`; `Syn_D` (`synList`) is every `N`-cell state sharing such a
stock; `Conf_D = Syn_D \ Prop_D` (`confList`).

For `1 ≤ D ≤ N`, `propagated_state` gives
`forwardFrom (s, replicate N false) D N = (false, s :: replicate (N-1) false)`,
and the cardinalities follow:

* `|Prop_D| = 2` (`propList_length`, `propList_distinct`)
* `|Syn_D| = 2^{N-D+1}` (`synList_length`, `synList_distinct`)
* `|Conf_D| = 2^{N-D+1} - 2` (`confList_length`, `confList_distinct`)
* `Syn_N = Prop_N`, `Conf_N = []` (`syn_eq_prop_at_max`, `conf_empty_at_max`)

Membership characterisations: `mem_synList_iff`, `mem_confList_iff`,
`mem_propList_iff` (depth-`D` archive pins the imprint bit). Enumerations
are `Distinct`, so `length` equals set cardinality. Statements use
`1 ≤ D ≤ N`.
-/

namespace Obs.Selection

open Geom.Ledger

/-! ## Arithmetic helpers (bare prelude, axiom-free) -/

theorem le_dest : ∀ {a b : Nat}, a ≤ b → ∃ k, b = a + k := by
  intro a b h
  induction h with
  | refl => exact ⟨0, rfl⟩
  | step _ ih =>
    match ih with
    | ⟨k, hk⟩ => exact ⟨k + 1, congrArg Nat.succ hk⟩

theorem add_sub_cancel_left : ∀ (a k : Nat), a + k - a = k := by
  intro a
  induction a with
  | zero => intro k; show 0 + k - 0 = k; rw [Nat.zero_add]; rfl
  | succ p ih =>
    intro k
    show (p + 1) + k - (p + 1) = k
    rw [Nat.succ_add, Nat.succ_sub_succ]
    exact ih k

theorem add_sub_cancel_right : ∀ (n m : Nat), n + m - m = n := by
  intro n m
  induction m with
  | zero => rfl
  | succ k ih =>
    show (n + k) + 1 - (k + 1) = n
    rw [Nat.succ_sub_succ]
    exact ih

theorem add_sub_of_le {a b : Nat} (h : a ≤ b) : a + (b - a) = b := by
  match le_dest h with
  | ⟨k, hk⟩ =>
    rw [hk, add_sub_cancel_left]

/-- `a % b = a` for `a < b`, proved from the definitional unfolding of
`Nat.mod` (core's `Nat.mod_eq_of_lt` carries `propext`). -/
theorem mod_eq_of_lt {a b : Nat} (h : a < b) : a % b = a := by
  cases a with
  | zero => rfl
  | succ n =>
    have hnot : ¬ (b ≤ n + 1) := fun hb => Nat.not_succ_le_self (n + 1) (Nat.le_trans h hb)
    show (if b ≤ n + 1 then Nat.modCore (n + 1) b else n + 1) = n + 1
    exact if_neg hnot

theorem add_self_two (a : Nat) : a + a + 2 = (a + 1) + (a + 1) := by
  have h : (a + 1) + a = (a + a) + 1 := Nat.succ_add a a
  show a + a + 2 = ((a + 1) + a) + 1
  rw [h]

/-- Cell bookkeeping: one imprint cell, `D-1` blank archive cells and `N-D`
free cells make `N` cells in all.  Needs `1 ≤ D ≤ N` (truncated subtraction). -/
theorem gap_split {N D : Nat} (hD : 1 ≤ D) (hDN : D ≤ N) :
    (D - 1) + (N - D) + 1 = N := by
  match D, hD, hDN with
  | k + 1, _, hDN =>
    have hk : k + 1 + (N - (k + 1)) = N := add_sub_of_le hDN
    have harith : ∀ m : Nat, k + m + 1 = k + 1 + m := by
      intro m
      rw [Nat.add_assoc, Nat.add_comm m 1, ← Nat.add_assoc]
    show k + (N - (k + 1)) + 1 = N
    rw [harith (N - (k + 1))]
    exact hk

/-- The same bookkeeping in the form used for the blank archive block. -/
theorem gap_split_pred {N D : Nat} (hD : 1 ≤ D) (hDN : D ≤ N) :
    (D - 1) + (N - D) = N - 1 := by
  have h := gap_split hD hDN
  have h2 : N - 1 = ((D - 1) + (N - D) + 1) - 1 := by rw [h]
  rw [h2, add_sub_cancel_right]

/-! ## List helpers (bare prelude, axiom-free) -/

theorem length_append {α : Type} : ∀ (as bs : List α),
    (as ++ bs).length = as.length + bs.length := by
  intro as
  induction as with
  | nil => intro bs; show bs.length = 0 + bs.length; rw [Nat.zero_add]
  | cons a as ih =>
    intro bs
    show (as ++ bs).length + 1 = (as.length + 1) + bs.length
    rw [ih bs, Nat.succ_add]

theorem length_replicate {α : Type} : ∀ (n : Nat) (a : α),
    (List.replicate n a).length = n := by
  intro n a
  induction n with
  | zero => rfl
  | succ k ih => show (List.replicate k a).length + 1 = k + 1; rw [ih]

theorem append_nil {α : Type} : ∀ (l : List α), l ++ [] = l := by
  intro l
  induction l with
  | nil => rfl
  | cons a as ih => show a :: (as ++ []) = a :: as; rw [ih]

theorem mem_append_left {α : Type} {a : α} : ∀ (l l' : List α), a ∈ l → a ∈ l ++ l' := by
  intro l
  induction l with
  | nil => intro _ h; cases h
  | cons x xs ih =>
    intro l' h
    cases h with
    | head => exact mem_head _ _
    | tail _ hm => exact mem_tail x (ih l' hm)

theorem mem_append_right {α : Type} {a : α} : ∀ (l l' : List α), a ∈ l' → a ∈ l ++ l' := by
  intro l
  induction l with
  | nil => intro _ h; exact h
  | cons x xs ih => intro l' h; exact mem_tail x (ih l' h)

theorem mem_or_of_mem_append {α : Type} {a : α} :
    ∀ (l l' : List α), a ∈ l ++ l' → a ∈ l ∨ a ∈ l' := by
  intro l
  induction l with
  | nil => intro _ h; exact Or.inr h
  | cons x xs ih =>
    intro l' h
    cases h with
    | head => exact Or.inl (mem_head _ _)
    | tail _ hm =>
      cases ih l' hm with
      | inl h1 => exact Or.inl (mem_tail x h1)
      | inr h1 => exact Or.inr h1

theorem mem_map_of_mem {α β : Type} (f : α → β) :
    ∀ (l : List α) (a : α), a ∈ l → f a ∈ l.map f := by
  intro l
  induction l with
  | nil => intro _ h; cases h
  | cons x xs ih =>
    intro a h
    cases h with
    | head => exact mem_head _ _
    | tail _ hm => exact mem_tail (f x) (ih a hm)

theorem distinct_append {α : Type} :
    ∀ (l l' : List α), Distinct l → Distinct l' →
      (∀ x, x ∈ l → ∀ y, y ∈ l' → x ≠ y) → Distinct (l ++ l') := by
  intro l
  induction l with
  | nil => intro _ _ hl' _; exact hl'
  | cons x xs ih =>
    intro l' hl hl' hd
    refine ⟨?_, ?_⟩
    · intro y hy
      cases mem_or_of_mem_append xs l' hy with
      | inl h => exact hl.1 y h
      | inr h => exact hd x (mem_head x xs) y h
    · exact ih l' hl.2 hl' (fun z hz => hd z (mem_tail x hz))

theorem distinct_map {α β : Type} (f : α → β) (hf : ∀ a b, f a = f b → a = b) :
    ∀ l : List α, Distinct l → Distinct (l.map f) := by
  intro l
  induction l with
  | nil => intro _; trivial
  | cons x xs ih =>
    intro hd
    refine ⟨?_, ?_⟩
    · intro y hy
      match exists_of_mem_map hy with
      | ⟨z, hz, hzy⟩ =>
        rw [← hzy]
        exact fun hfe => hd.1 z hz (hf x z hfe)
    · exact ih hd.2

theorem replicate_blank_cons {N : Nat} (hN : 1 ≤ N) :
    List.replicate N false = false :: List.replicate (N - 1) false := by
  match N, hN with
  | _ + 1, _ => rfl

theorem replicate_append_blank : ∀ (a b : Nat),
    List.replicate a false ++ List.replicate b false = List.replicate (a + b) false := by
  intro a
  induction a with
  | zero =>
    intro b
    show List.replicate b false = List.replicate (0 + b) false
    rw [Nat.zero_add]
  | succ k ih =>
    intro b
    show false :: (List.replicate k false ++ List.replicate b false)
        = List.replicate (k + 1 + b) false
    rw [ih b, Nat.succ_add]
    rfl

theorem replicate_cancel : ∀ (m : Nat) (t t' : List Bool),
    List.replicate m false ++ t = List.replicate m false ++ t' → t = t' := by
  intro m
  induction m with
  | zero => intro t t' h; exact h
  | succ k ih =>
    intro t t' h
    have h' : false :: (List.replicate k false ++ t)
            = false :: (List.replicate k false ++ t') := h
    exact ih t t' (congrArg List.tail h')

theorem take_replicate_le : ∀ (j m : Nat), j ≤ m →
    List.take j (List.replicate m false) = List.replicate j false := by
  intro j
  induction j with
  | zero => intro _ _; rfl
  | succ i ih =>
    intro m hm
    match m, hm with
    | p + 1, hm =>
      show false :: List.take i (List.replicate p false) = false :: List.replicate i false
      rw [ih p (Nat.le_of_succ_le_succ hm)]

theorem take_replicate_append : ∀ (m : Nat) (t : List Bool),
    List.take m (List.replicate m false ++ t) = List.replicate m false := by
  intro m
  induction m with
  | zero => intro _; rfl
  | succ k ih =>
    intro t
    show false :: List.take k (List.replicate k false ++ t) = false :: List.replicate k false
    rw [ih t]

/-! ## Boolean-list enumerations -/

/-- All Boolean lists of length `n`, blank list first. -/
def allBits : Nat → List (List Bool)
  | 0 => [[]]
  | n + 1 =>
    (allBits n).map (fun bs => false :: bs) ++ (allBits n).map (fun bs => true :: bs)

/-- `allBits n` with the blank list dropped: the `2^n - 1` non-blank lists. -/
def freeTails : Nat → List (List Bool)
  | 0 => []
  | n + 1 =>
    (freeTails n).map (fun bs => false :: bs) ++ (allBits n).map (fun bs => true :: bs)

theorem allBits_eq_cons : ∀ n, allBits n = List.replicate n false :: freeTails n := by
  intro n
  induction n with
  | zero => rfl
  | succ m ih =>
    show (allBits m).map (fun bs => false :: bs) ++ (allBits m).map (fun bs => true :: bs)
        = List.replicate (m + 1) false
          :: ((freeTails m).map (fun bs => false :: bs)
              ++ (allBits m).map (fun bs => true :: bs))
    rw [ih]
    rfl

theorem allBits_length : ∀ n, (allBits n).length = 2 ^ n := by
  intro n
  induction n with
  | zero => rfl
  | succ m ih =>
    show ((allBits m).map (fun bs => false :: bs)
          ++ (allBits m).map (fun bs => true :: bs)).length = 2 ^ (m + 1)
    rw [length_append, length_map_eq, length_map_eq, ih, Nat.pow_succ, Nat.mul_two]

/-- `|freeTails n| + 1 = 2^n` (subtraction-free form). -/
theorem freeTails_length_succ (n : Nat) : (freeTails n).length + 1 = 2 ^ n := by
  have h := allBits_length n
  rw [allBits_eq_cons] at h
  exact h

theorem freeTails_length (n : Nat) : (freeTails n).length = 2 ^ n - 1 := by
  have h := freeTails_length_succ n
  rw [← h, add_sub_cancel_right]

theorem allBits_distinct : ∀ n, Distinct (allBits n) := by
  intro n
  induction n with
  | zero => exact ⟨(fun _ h => nomatch h), trivial⟩
  | succ m ih =>
    show Distinct ((allBits m).map (fun bs => false :: bs)
                    ++ (allBits m).map (fun bs => true :: bs))
    refine distinct_append _ _ ?_ ?_ ?_
    · refine distinct_map (fun bs => false :: bs) ?_ _ ih
      intro a b h
      exact congrArg List.tail h
    · refine distinct_map (fun bs => true :: bs) ?_ _ ih
      intro a b h
      exact congrArg List.tail h
    · intro x hx y hy
      match exists_of_mem_map hx, exists_of_mem_map hy with
      | ⟨a, _, ha⟩, ⟨b, _, hb⟩ =>
        rw [← ha, ← hb]
        intro hc
        injection hc with h1 _
        exact Bool.noConfusion h1

theorem freeTails_distinct (n : Nat) : Distinct (freeTails n) := by
  have h := allBits_distinct n
  rw [allBits_eq_cons] at h
  exact h.2

theorem blank_not_mem_freeTails (n : Nat) :
    ∀ y, y ∈ freeTails n → List.replicate n false ≠ y := by
  intro y hy
  have h := allBits_distinct n
  rw [allBits_eq_cons] at h
  exact h.1 y hy

theorem mem_allBits : ∀ (n : Nat) (bs : List Bool), bs ∈ allBits n ↔ bs.length = n := by
  intro n
  induction n with
  | zero =>
    intro bs
    constructor
    · intro h
      cases h with
      | head => rfl
      | tail _ hm => cases hm
    · intro h
      cases bs with
      | nil => exact mem_head _ _
      | cons _ _ => exact absurd h (fun hh => Nat.noConfusion hh)
  | succ m ih =>
    intro bs
    constructor
    · intro h
      cases mem_or_of_mem_append _ _ h with
      | inl h1 =>
        match exists_of_mem_map h1 with
        | ⟨a, ha, hab⟩ =>
          rw [← hab]
          show a.length + 1 = m + 1
          rw [(ih a).mp ha]
      | inr h1 =>
        match exists_of_mem_map h1 with
        | ⟨a, ha, hab⟩ =>
          rw [← hab]
          show a.length + 1 = m + 1
          rw [(ih a).mp ha]
    · intro h
      cases bs with
      | nil => exact absurd h (fun hh => Nat.noConfusion hh)
      | cons c cs =>
        have hcs : cs.length = m := Nat.succ.inj h
        have hmem : cs ∈ allBits m := (ih cs).mpr hcs
        cases c with
        | false => exact mem_append_left _ _ (mem_map_of_mem _ _ cs hmem)
        | true => exact mem_append_right _ _ (mem_map_of_mem _ _ cs hmem)

theorem mem_freeTails_iff (n : Nat) (t : List Bool) :
    t ∈ freeTails n ↔ (t ∈ allBits n ∧ t ≠ List.replicate n false) := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · rw [allBits_eq_cons]
      exact mem_tail _ h
    · intro he
      exact blank_not_mem_freeTails n t h he.symm
  · intro h
    have h1 := h.1
    rw [allBits_eq_cons] at h1
    cases h1 with
    | head => exact absurd rfl h.2
    | tail _ hm => exact hm

/-! ## The swap conveyor -/

/-- A conveyor state: the system bit together with the environment cells. -/
abbrev State := Bool × List Bool

/-- Read cell `i`.  Out-of-range reads return `false`; the conveyor never makes
one, since the phase is reduced mod `N` and the cell list has length `N`. -/
def getCell : Nat → List Bool → Bool
  | _, [] => false
  | 0, c :: _ => c
  | n + 1, _ :: cs => getCell n cs

/-- Write `b` into cell `i`.  Out-of-range writes are no-ops. -/
def setCell : Nat → Bool → List Bool → List Bool
  | _, _, [] => []
  | 0, b, _ :: cs => b :: cs
  | n + 1, b, c :: cs => c :: setCell n b cs

theorem getCell_nil (i : Nat) : getCell i [] = false := by
  cases i <;> rfl

theorem setCell_nil (i : Nat) (b : Bool) : setCell i b [] = [] := by
  cases i <;> rfl

theorem getCell_replicate_false : ∀ (i m : Nat),
    getCell i (List.replicate m false) = false := by
  intro i m
  induction m generalizing i with
  | zero => exact getCell_nil i
  | succ p ih =>
    cases i with
    | zero => rfl
    | succ j => exact ih j

theorem setCell_replicate_false : ∀ (i m : Nat),
    setCell i false (List.replicate m false) = List.replicate m false := by
  intro i m
  induction m generalizing i with
  | zero => exact setCell_nil i false
  | succ p ih =>
    cases i with
    | zero => rfl
    | succ j =>
      show false :: setCell j false (List.replicate p false)
          = false :: List.replicate p false
      rw [ih j]

/-- One conveyor tick: SWAP the system bit with cell `phase % N`. -/
def step (x : State) (phase N : Nat) : State :=
  (getCell (phase % N) x.2, setCell (phase % N) x.1 x.2)

/-- `D` ticks from `x0`, at phases `0, 1, …, D-1` in order. -/
def forwardFrom (x0 : State) : Nat → Nat → State
  | 0, _ => x0
  | D + 1, N => step (forwardFrom x0 D N) D N

theorem forwardFrom_zero (x0 : State) (N : Nat) : forwardFrom x0 0 N = x0 := rfl

theorem forwardFrom_succ (x0 : State) (D N : Nat) :
    forwardFrom x0 (D + 1) N = step (forwardFrom x0 D N) D N := rfl

/-- The fiducial (product) initial states: system bit free, every cell blank. -/
def fiducials (N : Nat) : List State :=
  [(false, List.replicate N false), (true, List.replicate N false)]

/-- Observer stock at depth `D`: the system bit plus cells `0 … D-1`. -/
def stock (D : Nat) (x : State) : Bool × List Bool := (x.1, x.2.take D)

/-! ## The dynamical lemma -/

theorem propagated_aux (N : Nat) (s : Bool) :
    ∀ k, k + 1 ≤ N →
      forwardFrom (s, List.replicate N false) (k + 1) N
        = (false, s :: List.replicate (N - 1) false) := by
  intro k
  induction k with
  | zero =>
    intro h1
    have hN : 1 ≤ N := h1
    show step (s, List.replicate N false) 0 N = _
    rw [replicate_blank_cons hN]
    show (getCell (0 % N) (false :: List.replicate (N - 1) false),
          setCell (0 % N) s (false :: List.replicate (N - 1) false)) = _
    rw [Nat.zero_mod]
    rfl
  | succ m ih =>
    intro h
    have hm : m + 1 ≤ N := Nat.le_of_succ_le h
    have hlt : m + 1 < N := h
    show step (forwardFrom (s, List.replicate N false) (m + 1) N) (m + 1) N = _
    rw [ih hm]
    show (getCell ((m + 1) % N) (s :: List.replicate (N - 1) false),
          setCell ((m + 1) % N) false (s :: List.replicate (N - 1) false)) = _
    rw [mod_eq_of_lt hlt]
    show (getCell m (List.replicate (N - 1) false),
          s :: setCell m false (List.replicate (N - 1) false)) = _
    rw [getCell_replicate_false, setCell_replicate_false]

/-- **The dynamics.**  From a blank-tape fiducial, `D` ticks (`1 ≤ D ≤ N`) park
the system bit in cell `0` and leave everything else blank: the first tick
swaps `s` into cell `0`, and every later tick swaps blank with blank. -/
theorem propagated_state (N D : Nat) (hD : 1 ≤ D) (hDN : D ≤ N) (s : Bool) :
    forwardFrom (s, List.replicate N false) D N
      = (false, s :: List.replicate (N - 1) false) := by
  match D, hD, hDN with
  | _ + 1, _, hDN => exact propagated_aux N s _ hDN

/-! ## The three sets -/

/-- The state the conveyor writes from fiducial `(b, blank)`. -/
def imprint (N : Nat) (b : Bool) : State := (false, b :: List.replicate (N - 1) false)

/-- `Prop_D`: the image of the fiducials under `D` conveyor ticks. -/
def propList (N D : Nat) : List State :=
  (fiducials N).map (fun x0 => forwardFrom x0 D N)

/-- A depth-`D` syntactic state: imprint bit `b`, then `D-1` blank archive
cells, then a free tail. -/
def synState (D : Nat) (b : Bool) (t : List Bool) : State :=
  (false, b :: (List.replicate (D - 1) false ++ t))

/-- `Syn_D`: every state sharing a depth-`D` observer stock with a propagated
state — imprint bit free, free tail of length `N - D`. -/
def synList (N D : Nat) : List State :=
  (allBits (N - D)).map (synState D false) ++ (allBits (N - D)).map (synState D true)

/-- `Conf_D = Syn_D \ Prop_D`: the same, with the blank free tail removed. -/
def confList (N D : Nat) : List State :=
  (freeTails (N - D)).map (synState D false) ++ (freeTails (N - D)).map (synState D true)

/-- A state is *syntactic* at depth `D` when it has `N` cells and its depth-`D`
observer stock coincides with that of some propagated state. -/
def IsSyn (N D : Nat) (x : State) : Prop :=
  x.2.length = N ∧ ∃ y, y ∈ propList N D ∧ stock D x = stock D y

/-! ### Basic structure -/

theorem synState_inj {D : Nat} {b b' : Bool} {t t' : List Bool}
    (h : synState D b t = synState D b' t') : b = b' ∧ t = t' := by
  have h2 : b :: (List.replicate (D - 1) false ++ t)
          = b' :: (List.replicate (D - 1) false ++ t') := congrArg Prod.snd h
  injection h2 with hb hrest
  exact ⟨hb, replicate_cancel _ t t' hrest⟩

theorem synState_inj_tail {D : Nat} {b : Bool} {t t' : List Bool}
    (h : synState D b t = synState D b t') : t = t' := (synState_inj h).2

/-- Membership in a two-branch enumeration over a tail list. -/
theorem mem_branch_iff {D : Nat} {l : List (List Bool)} {x : State} :
    x ∈ l.map (synState D false) ++ l.map (synState D true)
      ↔ ∃ b t, t ∈ l ∧ x = synState D b t := by
  constructor
  · intro h
    cases mem_or_of_mem_append _ _ h with
    | inl h1 =>
      match exists_of_mem_map h1 with
      | ⟨t, ht, hEq⟩ => exact ⟨false, t, ht, hEq.symm⟩
    | inr h1 =>
      match exists_of_mem_map h1 with
      | ⟨t, ht, hEq⟩ => exact ⟨true, t, ht, hEq.symm⟩
  · intro h
    match h with
    | ⟨b, t, ht, hx⟩ =>
      cases b with
      | false =>
        rw [hx]
        exact mem_append_left _ _ (mem_map_of_mem _ _ t ht)
      | true =>
        rw [hx]
        exact mem_append_right _ _ (mem_map_of_mem _ _ t ht)

theorem branch_distinct {D : Nat} {l : List (List Bool)} (hl : Distinct l) :
    Distinct (l.map (synState D false) ++ l.map (synState D true)) := by
  refine distinct_append _ _ ?_ ?_ ?_
  · exact distinct_map _ (fun _ _ h => synState_inj_tail h) _ hl
  · exact distinct_map _ (fun _ _ h => synState_inj_tail h) _ hl
  · intro x hx y hy
    match exists_of_mem_map hx, exists_of_mem_map hy with
    | ⟨a, _, ha⟩, ⟨b, _, hb⟩ =>
      rw [← ha, ← hb]
      intro hc
      exact Bool.noConfusion (synState_inj hc).1

/-- The propagated states are exactly the two imprints. -/
theorem propList_eq (N D : Nat) (hD : 1 ≤ D) (hDN : D ≤ N) :
    propList N D = [imprint N false, imprint N true] := by
  show [forwardFrom (false, List.replicate N false) D N,
        forwardFrom (true, List.replicate N false) D N]
      = [(false, false :: List.replicate (N - 1) false),
         (false, true :: List.replicate (N - 1) false)]
  rw [propagated_state N D hD hDN false, propagated_state N D hD hDN true]

/-- An imprint is the syntactic state with the blank free tail. -/
theorem imprint_eq_synState {N D : Nat} (hD : 1 ≤ D) (hDN : D ≤ N) (b : Bool) :
    imprint N b = synState D b (List.replicate (N - D) false) := by
  show (false, b :: List.replicate (N - 1) false)
      = (false, b :: (List.replicate (D - 1) false ++ List.replicate (N - D) false))
  rw [replicate_append_blank, gap_split_pred hD hDN]

/-- **Archive determines imprint.**  `Prop_D` is exactly the two states indexed
by the imprint bit, each with the blank free tail. -/
theorem mem_propList_iff (N D : Nat) (hD : 1 ≤ D) (hDN : D ≤ N) (x : State) :
    x ∈ propList N D ↔ ∃ b, x = synState D b (List.replicate (N - D) false) := by
  rw [propList_eq N D hD hDN]
  constructor
  · intro h
    cases h with
    | head => exact ⟨false, imprint_eq_synState hD hDN false⟩
    | tail _ hm =>
      cases hm with
      | head => exact ⟨true, imprint_eq_synState hD hDN true⟩
      | tail _ hm2 => cases hm2
  · intro h
    match h with
    | ⟨b, hb⟩ =>
      cases b with
      | false =>
        rw [hb, ← imprint_eq_synState hD hDN false]
        exact mem_head _ _
      | true =>
        rw [hb, ← imprint_eq_synState hD hDN true]
        exact mem_tail _ (mem_head _ _)

/-! ### Stocks -/

theorem stock_synState {D : Nat} (hD : 1 ≤ D) (b : Bool) (t : List Bool) :
    stock D (synState D b t) = (false, b :: List.replicate (D - 1) false) := by
  match D, hD with
  | k + 1, _ =>
    show (false, b :: (List.replicate k false ++ t).take k)
        = (false, b :: List.replicate k false)
    rw [take_replicate_append]

theorem stock_imprint {N D : Nat} (hD : 1 ≤ D) (hDN : D ≤ N) (b : Bool) :
    stock D (imprint N b) = (false, b :: List.replicate (D - 1) false) := by
  match D, hD, hDN with
  | k + 1, _, hDN =>
    show (false, b :: (List.replicate (N - 1) false).take k)
        = (false, b :: List.replicate k false)
    rw [take_replicate_le k (N - 1) (Nat.sub_le_sub_right hDN 1)]

/-! ## Cardinalities -/

theorem propList_length (N D : Nat) : (propList N D).length = 2 := rfl

theorem synList_length (N D : Nat) : (synList N D).length = 2 ^ (N - D + 1) := by
  show ((allBits (N - D)).map (synState D false)
        ++ (allBits (N - D)).map (synState D true)).length = 2 ^ (N - D + 1)
  rw [length_append, length_map_eq, length_map_eq, allBits_length, Nat.pow_succ, Nat.mul_two]

theorem confList_length_add (N D : Nat) :
    (confList N D).length + 2 = 2 ^ (N - D + 1) := by
  show ((freeTails (N - D)).map (synState D false)
        ++ (freeTails (N - D)).map (synState D true)).length + 2 = 2 ^ (N - D + 1)
  rw [length_append, length_map_eq, length_map_eq, add_self_two, Nat.pow_succ,
      freeTails_length_succ, Nat.mul_two]

theorem confList_length (N D : Nat) : (confList N D).length = 2 ^ (N - D + 1) - 2 := by
  have h := confList_length_add N D
  rw [← h, add_sub_cancel_right]

theorem propList_distinct (N D : Nat) (hD : 1 ≤ D) (hDN : D ≤ N) :
    Distinct (propList N D) := by
  rw [propList_eq N D hD hDN]
  refine ⟨?_, ⟨(fun _ h => nomatch h), trivial⟩⟩
  intro y hy
  cases hy with
  | head =>
    intro h
    have h2 : false :: List.replicate (N - 1) false
            = true :: List.replicate (N - 1) false := congrArg Prod.snd h
    injection h2 with hb _
    exact Bool.noConfusion hb
  | tail _ hm => cases hm

theorem synList_distinct (N D : Nat) : Distinct (synList N D) :=
  branch_distinct (allBits_distinct (N - D))

theorem confList_distinct (N D : Nat) : Distinct (confList N D) :=
  branch_distinct (freeTails_distinct (N - D))

/-! ## Semantics of the enumerations -/

/-- `synList` enumerates exactly the syntactic states. -/
theorem mem_synList_iff (N D : Nat) (hD : 1 ≤ D) (hDN : D ≤ N) (x : State) :
    x ∈ synList N D ↔ IsSyn N D x := by
  constructor
  · intro h
    match mem_branch_iff.mp h with
    | ⟨b, t, ht, hx⟩ =>
      have hlen : t.length = N - D := (mem_allBits (N - D) t).mp ht
      refine ⟨?_, ⟨imprint N b, ?_, ?_⟩⟩
      · rw [hx]
        show (List.replicate (D - 1) false ++ t).length + 1 = N
        rw [length_append, length_replicate, hlen]
        exact gap_split hD hDN
      · exact (mem_propList_iff N D hD hDN _).mpr ⟨b, imprint_eq_synState hD hDN b⟩
      · rw [hx, stock_synState hD, stock_imprint hD hDN]
  · intro h
    match h with
    | ⟨hlen, ⟨y, hy, hst⟩⟩ =>
      match (mem_propList_iff N D hD hDN y).mp hy with
      | ⟨b, hyb⟩ =>
        have hsy : stock D y = (false, b :: List.replicate (D - 1) false) := by
          rw [hyb, stock_synState hD]
        have hst' : stock D x = (false, b :: List.replicate (D - 1) false) := by
          rw [hst, hsy]
        have h1 : x.1 = false := congrArg Prod.fst hst'
        have h2 : x.2.take D = b :: List.replicate (D - 1) false := congrArg Prod.snd hst'
        have hdlen : (x.2.drop D).length = N - D := by
          rw [List.length_drop, hlen]
        have hsplit : x.2 = b :: (List.replicate (D - 1) false ++ x.2.drop D) := by
          have hd := List.take_append_drop D x.2
          rw [h2] at hd
          exact hd.symm
        exact mem_branch_iff.mpr
          ⟨b, x.2.drop D, (mem_allBits (N - D) _).mpr hdlen, pair_ext h1 hsplit⟩

/-- Every propagated state is syntactic (take the all-blank free tail). -/
theorem prop_sublist_syn (N D : Nat) (hD : 1 ≤ D) (hDN : D ≤ N) :
    ∀ x, x ∈ propList N D → x ∈ synList N D := by
  intro x hx
  match (mem_propList_iff N D hD hDN x).mp hx with
  | ⟨b, hb⟩ =>
    refine mem_branch_iff.mpr ⟨b, List.replicate (N - D) false, ?_, hb⟩
    exact (mem_allBits (N - D) _).mpr (length_replicate (N - D) false)

/-- `confList` is exactly `synList` minus `propList`. -/
theorem mem_confList_iff (N D : Nat) (hD : 1 ≤ D) (hDN : D ≤ N) (x : State) :
    x ∈ confList N D ↔ (x ∈ synList N D ∧ x ∉ propList N D) := by
  constructor
  · intro h
    match mem_branch_iff.mp h with
    | ⟨b, t, ht, hx⟩ =>
      have ht' := (mem_freeTails_iff (N - D) t).mp ht
      refine ⟨mem_branch_iff.mpr ⟨b, t, ht'.1, hx⟩, ?_⟩
      intro hp
      match (mem_propList_iff N D hD hDN x).mp hp with
      | ⟨b', hb'⟩ =>
        rw [hx] at hb'
        exact ht'.2 (synState_inj hb').2
  · intro h
    match mem_branch_iff.mp h.1 with
    | ⟨b, t, ht, hx⟩ =>
      refine mem_branch_iff.mpr ⟨b, t, ?_, hx⟩
      refine (mem_freeTails_iff (N - D) t).mpr ⟨ht, ?_⟩
      intro hblank
      apply h.2
      refine (mem_propList_iff N D hD hDN x).mpr ⟨b, ?_⟩
      rw [hx, hblank]

/-! ## Maximum depth -/

/-- At maximum depth the free tail is empty: syntactic = propagated. -/
theorem syn_eq_prop_at_max (N : Nat) (hN : 1 ≤ N) : synList N N = propList N N := by
  rw [propList_eq N N hN (Nat.le_refl N)]
  show (allBits (N - N)).map (synState N false)
        ++ (allBits (N - N)).map (synState N true)
      = [imprint N false, imprint N true]
  rw [Nat.sub_self]
  show [(false, false :: (List.replicate (N - 1) false ++ [])),
        (false, true :: (List.replicate (N - 1) false ++ []))]
      = [(false, false :: List.replicate (N - 1) false),
         (false, true :: List.replicate (N - 1) false)]
  rw [append_nil]

/-- Confabulations vanish at maximum depth. -/
theorem conf_empty_at_max (N : Nat) : confList N N = [] := by
  show (freeTails (N - N)).map (synState N false)
        ++ (freeTails (N - N)).map (synState N true) = []
  rw [Nat.sub_self]
  rfl

theorem confList_length_at_max (N : Nat) : (confList N N).length = 0 :=
  congrArg List.length (conf_empty_at_max N)

/-! ## Closed-form cardinalities (bridged to the enumerations) -/

/-- Closed-form cardinality of the propagated set `Prop_D`. -/
def propCard : Nat := 2

/-- Closed-form cardinality of the syntactic set `Syn_D`. -/
def synCard (N D : Nat) : Nat := 2 ^ (N - D + 1)

/-- Closed-form cardinality of confabulations `Conf_D = Syn_D \\ Prop_D`. -/
def confCard (N D : Nat) : Nat := synCard N D - propCard

theorem propCard_eq_length (N D : Nat) : propCard = (propList N D).length :=
  (propList_length N D).symm

theorem synCard_eq_length (N D : Nat) : synCard N D = (synList N D).length :=
  (synList_length N D).symm

theorem confCard_eq_length (N D : Nat) : confCard N D = (confList N D).length :=
  (confList_length N D).symm

/-- `|Prop| · 2^{N-D} = |Syn|` (closed-form arithmetic). -/
theorem prop_times_free_eq_syn (N D : Nat) (_h : D ≤ N) :
    propCard * 2 ^ (N - D) = synCard N D := by
  show 2 * 2 ^ (N - D) = 2 ^ (N - D + 1)
  rw [Nat.pow_succ, Nat.mul_comm]

/-- Closed-form counterpart of `syn_eq_prop_at_max`. -/
theorem synCard_eq_propCard_at_max (N : Nat) : synCard N N = propCard := by
  show 2 ^ (N - N + 1) = 2
  rw [Nat.sub_self]

/-- Closed-form counterpart of `conf_empty_at_max`. -/
theorem confCard_zero_at_max (N : Nat) : confCard N N = 0 := by
  show synCard N N - propCard = 0
  rw [synCard_eq_propCard_at_max]
  exact Nat.sub_self _

/-- **Division-free ratio identity** about the real enumerations:
`|Syn_D| = |Prop_D| · 2^{N-D}`.  Stated on the regime `1 ≤ D ≤ N`, the only
one where `propList`/`synList` are the selection sets (`mem_synList_iff`); the
counting identity itself needs no side condition. -/
theorem selection_ratio_nat (N D : Nat) (_hD : 1 ≤ D) (_hDN : D ≤ N) :
    (synList N D).length = (propList N D).length * 2 ^ (N - D) := by
  rw [synList_length, propList_length]
  show 2 ^ (N - D + 1) = 2 * 2 ^ (N - D)
  rw [Nat.pow_succ, Nat.mul_comm]

/-- **Selection closed forms.**  Cardinalities of the constructed propagated,
syntactic and confabulation enumerations; their distinctness (so `length` is
cardinality); that `synList` enumerates exactly the syntactic states and
`confList` exactly `synList \ propList`; that every propagated state is
syntactic; the division-free ratio; and the vanishing of confabulations at
maximum depth. -/
theorem selection_closed_forms (N D : Nat) (hD : 1 ≤ D) (hDN : D ≤ N) :
    (propList N D).length = 2
    ∧ (synList N D).length = 2 ^ (N - D + 1)
    ∧ (confList N D).length = (synList N D).length - (propList N D).length
    ∧ Distinct (propList N D)
    ∧ Distinct (synList N D)
    ∧ Distinct (confList N D)
    ∧ (∀ x, x ∈ synList N D ↔ IsSyn N D x)
    ∧ (∀ x, x ∈ confList N D ↔ (x ∈ synList N D ∧ x ∉ propList N D))
    ∧ (∀ x, x ∈ propList N D → x ∈ synList N D)
    ∧ (synList N D).length = (propList N D).length * 2 ^ (N - D)
    ∧ (confList N N).length = 0 := by
  refine ⟨propList_length N D, synList_length N D, ?_, propList_distinct N D hD hDN,
    synList_distinct N D, confList_distinct N D, mem_synList_iff N D hD hDN,
    mem_confList_iff N D hD hDN, prop_sublist_syn N D hD hDN,
    selection_ratio_nat N D hD hDN, confList_length_at_max N⟩
  rw [synList_length, propList_length, confList_length]

end Obs.Selection

#print axioms Obs.Selection.le_dest
#print axioms Obs.Selection.add_sub_cancel_left
#print axioms Obs.Selection.add_sub_cancel_right
#print axioms Obs.Selection.add_sub_of_le
#print axioms Obs.Selection.mod_eq_of_lt
#print axioms Obs.Selection.add_self_two
#print axioms Obs.Selection.gap_split
#print axioms Obs.Selection.gap_split_pred
#print axioms Obs.Selection.length_append
#print axioms Obs.Selection.length_replicate
#print axioms Obs.Selection.append_nil
#print axioms Obs.Selection.mem_append_left
#print axioms Obs.Selection.mem_append_right
#print axioms Obs.Selection.mem_or_of_mem_append
#print axioms Obs.Selection.mem_map_of_mem
#print axioms Obs.Selection.distinct_append
#print axioms Obs.Selection.distinct_map
#print axioms Obs.Selection.replicate_blank_cons
#print axioms Obs.Selection.replicate_append_blank
#print axioms Obs.Selection.replicate_cancel
#print axioms Obs.Selection.take_replicate_le
#print axioms Obs.Selection.take_replicate_append
#print axioms Obs.Selection.allBits_eq_cons
#print axioms Obs.Selection.allBits_length
#print axioms Obs.Selection.freeTails_length_succ
#print axioms Obs.Selection.freeTails_length
#print axioms Obs.Selection.allBits_distinct
#print axioms Obs.Selection.freeTails_distinct
#print axioms Obs.Selection.blank_not_mem_freeTails
#print axioms Obs.Selection.mem_allBits
#print axioms Obs.Selection.mem_freeTails_iff
#print axioms Obs.Selection.getCell_nil
#print axioms Obs.Selection.setCell_nil
#print axioms Obs.Selection.getCell_replicate_false
#print axioms Obs.Selection.setCell_replicate_false
#print axioms Obs.Selection.forwardFrom_zero
#print axioms Obs.Selection.forwardFrom_succ
#print axioms Obs.Selection.propagated_aux
#print axioms Obs.Selection.propagated_state
#print axioms Obs.Selection.synState_inj
#print axioms Obs.Selection.synState_inj_tail
#print axioms Obs.Selection.mem_branch_iff
#print axioms Obs.Selection.branch_distinct
#print axioms Obs.Selection.propList_eq
#print axioms Obs.Selection.imprint_eq_synState
#print axioms Obs.Selection.mem_propList_iff
#print axioms Obs.Selection.stock_synState
#print axioms Obs.Selection.stock_imprint
#print axioms Obs.Selection.propList_length
#print axioms Obs.Selection.synList_length
#print axioms Obs.Selection.confList_length_add
#print axioms Obs.Selection.confList_length
#print axioms Obs.Selection.propList_distinct
#print axioms Obs.Selection.synList_distinct
#print axioms Obs.Selection.confList_distinct
#print axioms Obs.Selection.mem_synList_iff
#print axioms Obs.Selection.prop_sublist_syn
#print axioms Obs.Selection.mem_confList_iff
#print axioms Obs.Selection.syn_eq_prop_at_max
#print axioms Obs.Selection.conf_empty_at_max
#print axioms Obs.Selection.confList_length_at_max
#print axioms Obs.Selection.propCard_eq_length
#print axioms Obs.Selection.synCard_eq_length
#print axioms Obs.Selection.confCard_eq_length
#print axioms Obs.Selection.prop_times_free_eq_syn
#print axioms Obs.Selection.synCard_eq_propCard_at_max
#print axioms Obs.Selection.confCard_zero_at_max
#print axioms Obs.Selection.selection_ratio_nat
#print axioms Obs.Selection.selection_closed_forms
