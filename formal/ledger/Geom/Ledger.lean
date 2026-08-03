import Geom.Registration

/-!
# Geom.Ledger

An injective dilation of a `K`-fold system merge writes `K` pairwise-distinct
environment records, so the environment alphabet is at least `K`.
-/

namespace Geom.Ledger

open Geom.Registration

variable {X E S E' : Type}

/-! ## List helpers -/

theorem mem_head (a : α) (l : List α) : a ∈ a :: l := List.Mem.head l
theorem mem_tail (b : α) {a : α} {l : List α} (h : a ∈ l) : a ∈ b :: l :=
  List.Mem.tail b h

def Distinct : List α → Prop
  | [] => True
  | x :: xs => (∀ y, y ∈ xs → x ≠ y) ∧ Distinct xs

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

theorem length_map_eq (f : α → β) :
    ∀ l : List α, (l.map f).length = l.length := by
  intro l
  induction l with
  | nil => rfl
  | cons x xs ih =>
    show (xs.map f).length + 1 = xs.length + 1
    rw [ih]

theorem pair_ext {α β : Type} {p q : α × β}
    (h1 : p.1 = q.1) (h2 : p.2 = q.2) : p = q := by
  match p, q with
  | (a, b), (c, d) =>
    cases h1
    cases h2
    rfl

/-!
# Geom.Ledger

An injective dilation of a `K`-fold system merge writes `K` pairwise-distinct
environment records, so the environment alphabet is at least `K`.
-/

/-- Pairwise: merged states force distinct environment records. -/
theorem env_records_distinct (G : X × E → S × E')
    (hinj : ∀ a b : X × E, G a = G b → a = b) (e0 : E)
    {x y : X} (hxy : x ≠ y)
    (hsys : (G (x, e0)).1 = (G (y, e0)).1) :
    (G (x, e0)).2 ≠ (G (y, e0)).2 := by
  intro henv
  apply hxy
  have h := hinj (x, e0) (y, e0) (pair_ext hsys henv)
  exact congrArg Prod.fst h

/-- K-fold: distinct states merged at the system write distinct env records. -/
theorem env_records_distinct_list (G : X × E → S × E')
    (hinj : ∀ a b : X × E, G a = G b → a = b) (e0 : E) (s : S) :
    ∀ (xs : List X), Distinct xs →
      (∀ x, x ∈ xs → (G (x, e0)).1 = s) →
      Distinct (xs.map (fun x => (G (x, e0)).2)) := by
  intro xs
  induction xs with
  | nil => intro _ _; trivial
  | cons x rest ih =>
    intro hd hsys
    constructor
    · intro y hy
      match exists_of_mem_map hy with
      | ⟨z, hz, hzy⟩ =>
        rw [← hzy]
        exact env_records_distinct G hinj e0 (hd.1 z hz)
          (Eq.trans (hsys x (mem_head x rest))
            (Eq.symm (hsys z (mem_tail x hz))))
    · exact ih hd.2 (fun z hz => hsys z (mem_tail x hz))

/-- **Ledger bound.** Environment alphabet length ≥ merge in-degree `K`. -/
theorem alphabet_ge_indegree [DecidableEq E']
    (G : X × E → S × E')
    (hinj : ∀ a b : X × E, G a = G b → a = b) (e0 : E) (s : S)
    (xs : List X) (hd : Distinct xs)
    (hsys : ∀ x, x ∈ xs → (G (x, e0)).1 = s)
    (Es : List E') (halph : ∀ x, x ∈ xs → (G (x, e0)).2 ∈ Es) :
    xs.length ≤ Es.length := by
  have hdm := env_records_distinct_list G hinj e0 s xs hd hsys
  have hlm : ∀ y, y ∈ xs.map (fun x => (G (x, e0)).2) → y ∈ Es := fun y hy =>
    match exists_of_mem_map hy with
    | ⟨z, hz, hzy⟩ => hzy ▸ halph z hz
  have h := length_le_of_distinct_mem hdm hlm
  rw [length_map_eq] at h
  exact h

/-- **Ledger bound on the alphabet itself.** `alphabet_ge_indegree` bounds the
length of *some* list containing the records. If the list enumerates the whole
outgoing environment carrier `E'` -- i.e. it really is the alphabet -- then the
merge in-degree is a lower bound on the alphabet size: `|E'| ≥ K`. -/
theorem alphabet_ge_indegree_exhaustive [DecidableEq E']
    (G : X × E → S × E')
    (hinj : ∀ a b : X × E, G a = G b → a = b) (e0 : E) (s : S)
    (xs : List X) (hd : Distinct xs)
    (hsys : ∀ x, x ∈ xs → (G (x, e0)).1 = s)
    (Es : List E') (hall : ∀ e : E', e ∈ Es) :
    xs.length ≤ Es.length :=
  alphabet_ge_indegree G hinj e0 s xs hd hsys Es
    (fun x _ => hall (G (x, e0)).2)

/-- Specialization: registration's `merge_registers` is the K=2 ledger. -/
theorem merge_registers_is_ledger_pair {S E : Type}
    {U : S × E → S × E} (hU : Registration.Inj U)
    {a b : S × E} (hab : a ≠ b) (hm : (U a).1 = (U b).1) :
    (U a).2 ≠ (U b).2 :=
  fun he => hab (hU a b (Registration.pair_ext hm he))

end Geom.Ledger

#print axioms Geom.Ledger.env_records_distinct
#print axioms Geom.Ledger.env_records_distinct_list
#print axioms Geom.Ledger.alphabet_ge_indegree
#print axioms Geom.Ledger.alphabet_ge_indegree_exhaustive
#print axioms Geom.Ledger.merge_registers_is_ledger_pair
