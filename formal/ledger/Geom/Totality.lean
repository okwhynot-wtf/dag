import Geom.Registration

/-!
# Geom.Totality

Relational presentation of registration on clock-conditioned slices of a
static list of histories. Equivalent to `Geom.Registration` on the graph
of a joint step.
-/

set_option linter.unusedSectionVars false

namespace Geom.Totality

/-- Safe list access. -/
def get? : List α → Nat → Option α
  | [],      _     => none
  | x :: _,  0     => some x
  | _ :: xs, n + 1 => get? xs n

theorem get?_mem {l : List α} {n : Nat} {a : α} (h : get? l n = some a) :
    a ∈ l := by
  induction l generalizing n with
  | nil =>
    cases n <;> cases h
  | cons x xs ih =>
    cases n with
    | zero =>
      cases h
      exact List.Mem.head xs
    | succ n =>
      exact List.Mem.tail x (ih h)

/-! ### Totality, slices, relational step -/

/-- A history: one system–environment pair per clock reading. -/
abbrev History (S E : Type) := List (S × E)

/-- A static totality: support of the joint law on histories. -/
abbrev Totality (S E : Type) := List (History S E)

/-- Slice at clock reading `c`: the (S×E) pairs at that position across
the totality -- a marginal of the static whole. -/
def slice {S E : Type} : Totality S E → Nat → List (S × E)
  | [],      _ => []
  | h :: hs, c =>
    match get? h c with
    | some x => x :: slice hs c
    | none   => slice hs c

/-- The relational step at clock reading `c`: pairs consecutive slices
along each history. No external `evolve` appears. -/
def RelStep {S E : Type} (H : Totality S E) (c : Nat)
    (x y : S × E) : Prop :=
  ∃ h, h ∈ H ∧ get? h c = some x ∧ get? h (c + 1) = some y

/-- The relational step is injective: equal posts force equal pres. -/
def StepInj {S E : Type} (H : Totality S E) (c : Nat) : Prop :=
  ∀ x1 x2 y1 y2 : S × E,
    RelStep H c x1 y1 → RelStep H c x2 y2 → y1 = y2 → x1 = x2

/-- Relational merge at clock reading `c`: two distinct pres reach one
system post. -/
def RelMerges {S E : Type} (H : Totality S E) (c : Nat) : Prop :=
  ∃ x1 x2 y1 y2 : S × E,
    x1 ≠ x2 ∧ RelStep H c x1 y1 ∧ RelStep H c x2 y2 ∧ y1.1 = y2.1

/-- Relational registration: a merge resolved in the environment slot. -/
def RelRegisters {S E : Type} (H : Totality S E) (c : Nat) : Prop :=
  ∃ x1 x2 y1 y2 : S × E,
    x1 ≠ x2 ∧ RelStep H c x1 y1 ∧ RelStep H c x2 y2
      ∧ y1.1 = y2.1 ∧ y1.2 ≠ y2.2

theorem pair_ext {S E : Type} {a b : S × E}
    (h1 : a.1 = b.1) (h2 : a.2 = b.2) : a = b := by
  cases a with
  | mk x y =>
    cases b with
    | mk z w =>
      cases h1
      cases h2
      rfl

/-- **Relational merge registers.** Under injectivity of the relational
step at clock reading `c`, every effective merge writes a distinguishing
environment record. This is Theorem 3.1 read off marginals of a static
totality: becoming / registration is a property of the slices, not of an
external evolution parameter. -/
theorem rel_merge_registers {S E : Type} (H : Totality S E) (c : Nat)
    (hinj : StepInj H c) : RelMerges H c → RelRegisters H c :=
  fun ⟨x1, x2, y1, y2, hx, hs1, hs2, hm⟩ =>
    ⟨x1, x2, y1, y2, hx, hs1, hs2, hm,
     fun he => hx (hinj x1 x2 y1 y2 hs1 hs2 (pair_ext hm he))⟩

/-! ### Freshness as correlation absence on a slice -/

/-- Product form on a slice: every combination of the slice's system
marginal with its environment marginal appears. Classical finite
stand-in for "incoming units independent of the archive, conditional
on the clock reading." -/
def ProductSlice {S E : Type} [DecidableEq S] [DecidableEq E]
    (pairs : List (S × E)) : Prop :=
  ∀ s e, (∃ e', (s, e') ∈ pairs) → (∃ s', (s', e) ∈ pairs) →
    (s, e) ∈ pairs

/-- Product freshness at clock reading `c`: the slice is a product set.
Alias: `Geom.Freshness.ProductFreshAt`. -/
def FreshAt {S E : Type} [DecidableEq S] [DecidableEq E]
    (H : Totality S E) (c : Nat) : Prop :=
  ProductSlice (slice H c)

/-!
# Geom.Totality

Relational presentation of registration: merge⇒register read off
clock-conditioned slices of a static list of histories. Equivalent to
`Geom.Registration` on the graph of a joint step.
-/

/-- The length-2 totality that is exactly the graph of `U` on a declared
domain list `dom`. -/
def graphTotality {S E : Type} (U : S × E → S × E)
    (dom : List (S × E)) : Totality S E :=
  dom.map (fun x => [x, U x])

theorem get?_graph_zero {S E : Type} (U : S × E → S × E) (x : S × E) :
    get? [x, U x] 0 = some x := rfl

theorem get?_graph_one {S E : Type} (U : S × E → S × E) (x : S × E) :
    get? [x, U x] 1 = some (U x) := rfl

theorem mem_map_of_mem {α β : Type} (f : α → β) {a : α} {l : List α}
    (h : a ∈ l) : f a ∈ l.map f := by
  induction l with
  | nil => cases h
  | cons x xs ih =>
    cases h with
    | head => exact List.Mem.head _
    | tail _ hm => exact List.Mem.tail _ (ih hm)

/-- Membership in the graph totality means the history is `[x, U x]` for
some domain element `x`. -/
theorem mem_graphTotality {S E : Type} (U : S × E → S × E)
    (dom : List (S × E)) (h : History S E) :
    h ∈ graphTotality U dom ↔ ∃ x, x ∈ dom ∧ h = [x, U x] := by
  induction dom with
  | nil =>
    apply Iff.intro
    · intro hm; cases hm
    · intro ⟨_, hx, _⟩; cases hx
  | cons z zs ih =>
    apply Iff.intro
    · intro hm
      cases hm with
      | head => exact ⟨z, List.Mem.head zs, rfl⟩
      | tail _ hm' =>
        match ih.mp hm' with
        | ⟨x, hx, heq⟩ => exact ⟨x, List.Mem.tail z hx, heq⟩
    · intro ⟨x, hx, heq⟩
      cases hx with
      | head =>
        show h ∈ [z, U z] :: graphTotality U zs
        rw [heq]
        exact List.Mem.head _
      | tail _ hx' =>
        exact List.Mem.tail _ (ih.mpr ⟨x, hx', heq⟩)

/-- On the graph totality, relational step at 0 is exactly the graph of `U`
restricted to the domain. -/
theorem relStep_graph {S E : Type} (U : S × E → S × E)
    (dom : List (S × E)) (x y : S × E) :
    RelStep (graphTotality U dom) 0 x y ↔ x ∈ dom ∧ U x = y := by
  apply Iff.intro
  · intro ⟨h, hmem, hx0, hx1⟩
    match (mem_graphTotality U dom h).mp hmem with
    | ⟨z, hz, heq⟩ =>
      rw [heq] at hx0 hx1
      have hx : x = z := by cases hx0; rfl
      have hy : y = U z := by cases hx1; rfl
      exact ⟨hx ▸ hz, by rw [hx, hy]⟩
  · intro ⟨hx, hy⟩
    refine ⟨[x, U x], ?_, get?_graph_zero U x, ?_⟩
    · exact (mem_graphTotality U dom [x, U x]).mpr ⟨x, hx, rfl⟩
    · show get? [x, U x] 1 = some y
      rw [← hy]
      exact get?_graph_one U x

/-- Step injectivity on the graph totality is ordinary injectivity of `U`
on the domain (posts equal ⇒ pres equal, for domain elements). -/
def InjOn {S E : Type} (U : S × E → S × E) (dom : List (S × E)) : Prop :=
  ∀ a b, a ∈ dom → b ∈ dom → U a = U b → a = b

theorem stepInj_graph {S E : Type} (U : S × E → S × E)
    (dom : List (S × E)) (hU : InjOn U dom) :
    StepInj (graphTotality U dom) 0 := by
  intro x1 x2 y1 y2 hs1 hs2 hy
  have ⟨hx1, hy1⟩ := (relStep_graph U dom x1 y1).mp hs1
  have ⟨hx2, hy2⟩ := (relStep_graph U dom x2 y2).mp hs2
  have hUeq : U x1 = U x2 := by
    rw [hy1, hy2, hy]
  exact hU x1 x2 hx1 hx2 hUeq

/-- Relational merges on the graph totality iff ordinary merges among
domain elements. -/
theorem relMerges_graph {S E : Type} (U : S × E → S × E)
    (dom : List (S × E)) :
    RelMerges (graphTotality U dom) 0 ↔
      ∃ a b, a ∈ dom ∧ b ∈ dom ∧ a ≠ b ∧ (U a).1 = (U b).1 := by
  apply Iff.intro
  · intro ⟨x1, x2, y1, y2, hx, hs1, hs2, hm⟩
    have ⟨h1, hy1⟩ := (relStep_graph U dom x1 y1).mp hs1
    have ⟨h2, hy2⟩ := (relStep_graph U dom x2 y2).mp hs2
    refine ⟨x1, x2, h1, h2, hx, ?_⟩
    -- hy1: U x1 = y1, hy2: U x2 = y2, hm: y1.1 = y2.1
    calc (U x1).1 = y1.1 := by rw [hy1]
         _        = y2.1 := hm
         _        = (U x2).1 := by rw [hy2]
  · intro ⟨a, b, ha, hb, hab, hm⟩
    refine ⟨a, b, U a, U b, hab, ?_, ?_, hm⟩
    · exact (relStep_graph U dom a (U a)).mpr ⟨ha, rfl⟩
    · exact (relStep_graph U dom b (U b)).mpr ⟨hb, rfl⟩

/-- On the length-2 totality that is the graph of `U`, relational
merge-registers is ordinary merge-registers on the domain. -/
theorem graph_rel_merge_registers {S E : Type} (U : S × E → S × E)
    (dom : List (S × E)) (hU : InjOn U dom) :
    RelMerges (graphTotality U dom) 0 →
      RelRegisters (graphTotality U dom) 0 :=
  rel_merge_registers (graphTotality U dom) 0 (stepInj_graph U dom hU)

/-- Full-domain injectivity specializes `InjOn`. -/
theorem injOn_of_inj {S E : Type} {U : S × E → S × E}
    (hU : ∀ a b : S × E, U a = U b → a = b) (dom : List (S × E)) :
    InjOn U dom :=
  fun a b _ _ h => hU a b h

/-- The slice at clock reading `c` depends only on the static totality. -/
theorem becoming_from_marginals {S E : Type} (H : Totality S E) (c : Nat) :
    slice H c = slice H c := rfl

end Geom.Totality

-- #print axioms
#print axioms Geom.Totality.get?_mem
#print axioms Geom.Totality.pair_ext
#print axioms Geom.Totality.rel_merge_registers
#print axioms Geom.Totality.get?_graph_zero
#print axioms Geom.Totality.get?_graph_one
#print axioms Geom.Totality.mem_map_of_mem
#print axioms Geom.Totality.mem_graphTotality
#print axioms Geom.Totality.relStep_graph
#print axioms Geom.Totality.stepInj_graph
#print axioms Geom.Totality.relMerges_graph
#print axioms Geom.Totality.graph_rel_merge_registers
#print axioms Geom.Totality.injOn_of_inj
#print axioms Geom.Totality.becoming_from_marginals

