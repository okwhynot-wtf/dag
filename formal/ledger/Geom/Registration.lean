/-!
# Geom.Registration

Under an injective joint step, every effective system merge writes a
distinguishing environment record.
-/

namespace Geom.Registration

variable {S E : Type}

/-- Pair extensionality. -/
theorem pair_ext {a b : S × E} (h1 : a.1 = b.1) (h2 : a.2 = b.2) :
    a = b := by
  cases a with
  | mk x y =>
    cases b with
    | mk z w =>
      cases h1
      cases h2
      rfl

/-- The joint step is injective. -/
def Inj (U : S × E → S × E) : Prop := ∀ a b, U a = U b → a = b

/-- Effective merge: two joint states reach one system target. -/
def Merges (U : S × E → S × E) : Prop :=
  ∃ a b : S × E, a ≠ b ∧ (U a).1 = (U b).1

/-- Registration: some merge is resolved in the outgoing environment slot. -/
def Registers (U : S × E → S × E) : Prop :=
  ∃ a b : S × E, a ≠ b ∧ (U a).1 = (U b).1 ∧ (U a).2 ≠ (U b).2

/-- **Any merge registers.** Injectivity forces a distinguishing record. -/
theorem merge_registers {U : S × E → S × E} (hU : Inj U) :
    Merges U → Registers U :=
  fun ⟨a, b, hab, hm⟩ =>
    ⟨a, b, hab, hm, fun he => hab (hU a b (pair_ext hm he))⟩

/-- No writing, no merging: mute outgoing slots imply injective effective map. -/
theorem no_write_no_merge {U : S × E → S × E} (hU : Inj U)
    (hw : ∀ a b : S × E, (U a).1 = (U b).1 → (U a).2 = (U b).2) :
    ∀ a b : S × E, (U a).1 = (U b).1 → a = b :=
  fun a b hm => hU a b (pair_ext hm (hw a b hm))

/-- Merged pair at a fixed incoming unit: outgoing records differ. -/
theorem merge_pair_registers {U : S × E → S × E} (hU : Inj U)
    {s₁ s₂ : S} {e : E} (hne : s₁ ≠ s₂)
    (hm : (U (s₁, e)).1 = (U (s₂, e)).1) :
    (U (s₁, e)).2 ≠ (U (s₂, e)).2 :=
  fun he => hne (congrArg Prod.fst (hU _ _ (pair_ext hm he)))

/-! ## Independence witnesses

Oscillator: injective, never merges (perfect memory, no archive needed).
Swap: injective, merges and registers. Registration is independent of bare
injectivity — both poles exist. -/

def oscStep : Bool × Unit → Bool × Unit := fun p => (!p.1, ())

def swapStep : Bool × Bool → Bool × Bool := fun p => (p.2, p.1)

theorem osc_inj : Inj oscStep := by
  intro a b h
  have h1 : (!a.1) = (!b.1) := congrArg Prod.fst h
  have h2 : a.1 = b.1 := by
    cases ha : a.1 <;> cases hb : b.1
    · rfl
    · rw [ha, hb] at h1; exact absurd h1 (by decide)
    · rw [ha, hb] at h1; exact absurd h1 (by decide)
    · rfl
  cases a with
  | mk x u =>
    cases b with
    | mk y v =>
      cases h2
      rfl

theorem osc_never_registers :
    Inj oscStep ∧ ¬ Merges oscStep ∧ ¬ Registers oscStep := by
  refine ⟨osc_inj, ?_, ?_⟩
  · intro ⟨a, b, hab, hm⟩
    exact hab (osc_inj a b (pair_ext hm rfl))
  · intro ⟨a, b, _, _, hr⟩
    exact hr rfl

theorem swap_inj : Inj swapStep := by
  intro a b h
  have h1 : a.2 = b.2 := congrArg Prod.fst h
  have h2 : a.1 = b.1 := congrArg Prod.snd h
  exact pair_ext h2 h1

theorem swap_registers : Inj swapStep ∧ Merges swapStep ∧ Registers swapStep := by
  refine ⟨swap_inj, ?_, ?_⟩
  · exact ⟨(false, true), (true, true), by decide, rfl⟩
  · exact ⟨(false, true), (true, true), by decide, rfl, by decide⟩

theorem registration_independent :
    (Inj oscStep ∧ ¬ Merges oscStep ∧ ¬ Registers oscStep)
    ∧ (Inj swapStep ∧ Merges swapStep ∧ Registers swapStep) :=
  ⟨osc_never_registers, swap_registers⟩

/-! ## Finitude forces merges (pigeonhole) -/

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

def findEq [DecidableEq S] (tok : Nat → S) (v : S) : List Nat → Option Nat
  | [] => none
  | j :: js => if tok j = v then some j else findEq tok v js

theorem findEq_some [DecidableEq S] (tok : Nat → S) (v : S) :
    ∀ (l : List Nat) (j : Nat),
      findEq tok v l = some j → j ∈ l ∧ tok j = v := by
  intro l
  induction l with
  | nil =>
    intro j h
    exact nomatch (show (none : Option Nat) = some j from h)
  | cons k ks ih =>
    intro j h
    have h' : (if tok k = v then some k else findEq tok v ks) = some j := h
    by_cases hk : tok k = v
    · rw [if_pos hk] at h'
      cases h'
      exact ⟨mem_head k ks, hk⟩
    · rw [if_neg hk] at h'
      match ih j h' with
      | ⟨hm, he⟩ => exact ⟨mem_tail k hm, he⟩

theorem findEq_none [DecidableEq S] (tok : Nat → S) (v : S) :
    ∀ l : List Nat, findEq tok v l = none →
      ∀ j, j ∈ l → tok j ≠ v := by
  intro l
  induction l with
  | nil => intro _ j hj; cases hj
  | cons k ks ih =>
    intro h j hj
    have h' : (if tok k = v then some k else findEq tok v ks) = none := h
    by_cases hk : tok k = v
    · rw [if_pos hk] at h'
      exact nomatch h'
    · rw [if_neg hk] at h'
      cases hj with
      | head => exact hk
      | tail _ hm => exact ih h' j hm

/-- Constructive pigeonhole: colliding pair found by bounded search. -/
theorem pigeonhole_list {S : Type} [DecidableEq S] (tok : Nat → S) :
    ∀ (l : List Nat) (Ss : List S),
      Distinct l → (∀ i, i ∈ l → tok i ∈ Ss) → Ss.length < l.length →
      ∃ i j : Nat, i ∈ l ∧ j ∈ l ∧ i ≠ j ∧ tok i = tok j := by
  intro l
  induction l with
  | nil =>
    intro Ss _ _ hlt
    exact absurd hlt (Nat.not_lt_zero _)
  | cons i rest ih =>
    intro Ss hd hmem hlt
    match hfind : findEq tok (tok i) rest with
    | some j =>
      match findEq_some tok (tok i) rest j hfind with
      | ⟨hjmem, hje⟩ =>
        exact ⟨i, j, mem_head i rest, mem_tail i hjmem,
          hd.1 j hjmem, hje.symm⟩
    | none =>
      have hnone := findEq_none tok (tok i) rest hfind
      have hmem' : ∀ k, k ∈ rest → tok k ∈ remove (tok i) Ss :=
        fun k hk => mem_remove (hmem k (mem_tail i hk)) (hnone k hk)
      have hlen : (remove (tok i) Ss).length < rest.length := by
        have h1 : (remove (tok i) Ss).length + 1 = Ss.length :=
          length_remove_of_mem (hmem i (mem_head i rest))
        have h2 : Ss.length ≤ rest.length := Nat.le_of_lt_succ hlt
        rw [← h1] at h2
        exact Nat.lt_of_succ_le h2
      match ih (remove (tok i) Ss) hd.2 hmem' hlen with
      | ⟨i', j', hi', hj', hne, he⟩ =>
        exact ⟨i', j', mem_tail i hi', mem_tail i hj', hne, he⟩

def upto : Nat → List Nat
  | 0 => []
  | n + 1 => n :: upto n

theorem upto_lt : ∀ n m : Nat, m ∈ upto n → m < n := by
  intro n
  induction n with
  | zero => intro m hm; cases hm
  | succ k ih =>
    intro m hm
    cases hm with
    | head => exact Nat.lt_succ_self k
    | tail _ hm' => exact Nat.lt_succ_of_lt (ih m hm')

theorem upto_distinct : ∀ n : Nat, Distinct (upto n) := by
  intro n
  induction n with
  | zero => trivial
  | succ k ih =>
    exact ⟨fun y hy he => Nat.lt_irrefl y (he ▸ upto_lt k y hy), ih⟩

theorem upto_length : ∀ n : Nat, (upto n).length = n := by
  intro n
  induction n with
  | zero => rfl
  | succ k ih =>
    show (upto k).length + 1 = k + 1
    rw [ih]

/-- Finite carrier, unboundedly many labeled visits ⇒ token collision. -/
theorem finite_carrier_collision {S : Type} [DecidableEq S]
    (Ss : List S) (hS : ∀ s : S, s ∈ Ss) (tok : Nat → S) :
    ∃ i j : Nat, i ≠ j ∧ tok i = tok j := by
  match pigeonhole_list tok (upto (Ss.length + 1)) Ss
      (upto_distinct _) (fun i _ => hS (tok i))
      (by rw [upto_length]; exact Nat.lt_succ_self _) with
  | ⟨i, j, _, _, hne, he⟩ => exact ⟨i, j, hne, he⟩

end Geom.Registration

#print axioms Geom.Registration.pair_ext
#print axioms Geom.Registration.merge_registers
#print axioms Geom.Registration.no_write_no_merge
#print axioms Geom.Registration.merge_pair_registers
#print axioms Geom.Registration.osc_never_registers
#print axioms Geom.Registration.swap_registers
#print axioms Geom.Registration.registration_independent
#print axioms Geom.Registration.pigeonhole_list
#print axioms Geom.Registration.finite_carrier_collision
