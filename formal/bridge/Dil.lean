import Alphabet
import Capacity
import Density
import Ladder
import Geom.Exhaustion
import Geom.Registration

/-!
# Dil — environment as universal completion (keystone)

Targets I-2 / T-1 beyond fiber-tagging: the environment is the minimal
archive restoring injectivity to a merging system map `u : S → S`.

This module lands the afternoon propositions of the keystone sketch:
1. Free archive is initial in `Dil(u)`
2. Capacity law `|E_{T+1}| ≥ K · |E_T|` from a K-fold fiber
3. Registration as corollary (merge forces record separation)
4. Minimal = saturated schedule; ladder predicate count realises `|E_T| = 2^{T+2}`

Rigidity partition fragment landed (cover at equality). Packaged UF↔UF
iso landed (`rigidity_iso`). Graded terminality among UF + pointed archives
landed (`graded_terminality_of_UF`). I-2 Fin alphabet-UF closed
(`boolCapsUF` / `i2_fin_closed` / `rigidity_iso_of_base`): at `K = 2` with
`S = Bool` the letter type *is* the alphabet, so minimal bijection = UF;
rigidity is relative to a base bijection (`|E₀| = 4`). Ladder-predicate
addressing witness and `|S|>K` address-uniform idx fragment land below.
**Straightening** (`isoToFreeOnBase` / `straighten_fragment`): UF archives
≅ append-only on frozen base; record gauge = base relabelling.
**T-2** classified identification:
`TickSimulation.tick_identification` (append glue here via
`freeOnBase_append_step`). Historical remnant:
`tick_identification_licensed`.
-/

namespace Bridge.Dil

open Geom.Exhaustion

/-! ## Free archive carrier: words -/

/-- Words of length `n` over `S` — carrier of the free archive. -/
inductive Word (S : Type) : Nat → Type where
  | nil : Word S 0
  | cons {n : Nat} (head : S) (tail : Word S n) : Word S (n + 1)

/-- Prepend a letter (record step of the free archive). -/
def Word.prepend {S : Type} {n : Nat} (s : S) (w : Word S n) : Word S (n + 1) :=
  Word.cons s w

@[simp] theorem Word.prepend_eq {S : Type} {n : Nat} (s : S) (w : Word S n) :
    Word.prepend s w = Word.cons s w :=
  rfl

/-! ## Archives and morphisms -/

/-- An archive for system dynamics `u : S → S`: environment levels with
    record maps such that the joint step `(u, r_T)` is injective. -/
structure Archive (S : Type) (u : S → S) where
  E : Nat → Type
  /-- Empty-archive basepoint at tick 0 (non-commencement). -/
  z0 : E 0
  r : (T : Nat) → S → E T → E (T + 1)
  /-- Joint injectivity of `Û_T(s,e) = (u s, r T s e)`. -/
  joint_inj :
    ∀ T (s₁ s₂ : S) (e₁ e₂ : E T),
      u s₁ = u s₂ →
      r T s₁ e₁ = r T s₂ e₂ →
      s₁ = s₂ ∧ e₁ = e₂

/-- Pointed archive morphism: preserves basepoint and records. -/
structure Hom {S : Type} {u : S → S} (A B : Archive S u) where
  map : (T : Nat) → A.E T → B.E T
  map_z0 : map 0 A.z0 = B.z0
  nat_r :
    ∀ T (s : S) (e : A.E T),
      map (T + 1) (A.r T s e) = B.r T s (map T e)

/-! ## Prop 1 — free archive is initial -/

/-- Free archive: records prepend; joint injectivity is syntactic. -/
def free (S : Type) (u : S → S) : Archive S u where
  E := Word S
  z0 := Word.nil
  r := fun _ s w => Word.prepend s w
  joint_inj := by
    intro T s₁ s₂ e₁ e₂ _ hr
    -- `Word.cons s₁ e₁ = Word.cons s₂ e₂`
    cases hr
    exact ⟨rfl, rfl⟩

/-- Interpret a free word in an arbitrary archive by replaying records. -/
def interpret {S : Type} {u : S → S} (A : Archive S u) :
    (T : Nat) → Word S T → A.E T
  | 0, Word.nil => A.z0
  | _n + 1, Word.cons s w => A.r _n s (interpret A _n w)

theorem interpret_nil {S : Type} {u : S → S} (A : Archive S u) :
    interpret A 0 Word.nil = A.z0 :=
  rfl

theorem interpret_cons {S : Type} {u : S → S} (A : Archive S u)
    (n : Nat) (s : S) (w : Word S n) :
    interpret A (n + 1) (Word.cons s w) = A.r n s (interpret A n w) :=
  rfl

/-- Canonical morphism from the free archive. -/
def freeHom {S : Type} {u : S → S} (A : Archive S u) : Hom (free S u) A where
  map := interpret A
  map_z0 := rfl
  nat_r := by
    intro T s e
    rfl

/-- Any pointed record-morphism from free equals `interpret` (uniqueness). -/
theorem freeHom_unique {S : Type} {u : S → S} (A : Archive S u)
    (h : Hom (free S u) A) :
    ∀ T (w : Word S T), h.map T w = interpret A T w := by
  intro T w
  induction w with
  | nil =>
    exact h.map_z0
  | cons s tail ih =>
    -- h.map (n+1) (cons s tail) = A.r n s (h.map n tail)
    have hnat := h.nat_r _ s tail
    -- free.r = prepend = cons
    change h.map _ (Word.cons s tail) = A.r _ s (h.map _ tail) at hnat
    rw [hnat, ih]
    rfl

/-- **Prop 1.** Free archive is initial in `Dil(u)`:
    a pointed record-morphism exists and is unique. -/
theorem free_initial {S : Type} {u : S → S} (A : Archive S u) :
    (∃ _h : Hom (free S u) A, True) ∧
    (∀ h₁ h₂ : Hom (free S u) A, h₁ = h₂) :=
  ⟨⟨freeHom A, True.intro⟩, by
    intro h₁ h₂
    have u₁ := freeHom_unique A h₁
    have u₂ := freeHom_unique A h₂
    cases h₁ with
    | mk m₁ z₁ n₁ =>
      cases h₂ with
      | mk m₂ z₂ n₂ =>
        have hm : m₁ = m₂ := by
          funext T w
          exact (u₁ T w).trans (u₂ T w).symm
        cases hm
        rfl⟩

/-! ## Finite (enumerated) archives — for capacity counting -/

/-- Archive equipped with finite enumerations of each level. -/
structure FiniteArchive (S : Type) (u : S → S) extends Archive S u where
  enum : (T : Nat) → List (E T)
  enum_distinct : ∀ T, Distinct (enum T)
  enum_complete : ∀ T (e : E T), e ∈ enum T

def FiniteArchive.card {S : Type} {u : S → S} (A : FiniteArchive S u)
    (T : Nat) : Nat :=
  (A.enum T).length

/-! ## Prop 2 — capacity law -/

/-- On a common `u`-fiber, record maps are injective in the environment. -/
theorem record_inj_on_fiber {S E E' : Type}
    (u : S → S) (r : S → E → E')
    (hjoint : ∀ s₁ e₁ s₂ e₂,
      u s₁ = u s₂ → r s₁ e₁ = r s₂ e₂ → s₁ = s₂ ∧ e₁ = e₂)
    (s : S) (e₁ e₂ : E) (hre : r s e₁ = r s e₂) :
    e₁ = e₂ :=
  (hjoint s e₁ s e₂ rfl hre).2

/-- Distinct fiber indices yield disjoint record images. -/
theorem record_images_disjoint {S E E' : Type}
    (u : S → S) (r : S → E → E')
    (hjoint : ∀ s₁ e₁ s₂ e₂,
      u s₁ = u s₂ → r s₁ e₁ = r s₂ e₂ → s₁ = s₂ ∧ e₁ = e₂)
    (s₁ s₂ : S) (hsu : u s₁ = u s₂) (hne : s₁ ≠ s₂)
    (e₁ e₂ : E) (hre : r s₁ e₁ = r s₂ e₂) :
    False := by
  have h := hjoint s₁ e₁ s₂ e₂ hsu hre
  exact hne h.1

/-- Image of an enumeration under `r s`. -/
def recordImage {S E E' : Type} (r : S → E → E') (s : S) (enum : List E) :
    List E' :=
  enum.map (r s)

theorem recordImage_length {S E E' : Type}
    (r : S → E → E') (s : S) (enum : List E) :
    (recordImage r s enum).length = enum.length :=
  length_map_eq (r s) enum

theorem recordImage_distinct {S E E' : Type}
    (u : S → S) (r : S → E → E')
    (hjoint : ∀ s₁ e₁ s₂ e₂,
      u s₁ = u s₂ → r s₁ e₁ = r s₂ e₂ → s₁ = s₂ ∧ e₁ = e₂)
    (s : S) (enum : List E) (hd : Distinct enum) :
    Distinct (recordImage r s enum) := by
  refine distinct_map_of_inj hd ?_
  intro a a' _ _ hfa
  exact record_inj_on_fiber u r hjoint s a a' hfa

/-- **Prop 2 (step form).** A K-fold merge fiber forces
    `|E'| ≥ K · |E|` for any joint-injective record step. -/
theorem capacity_step {S E E' : Type} [DecidableEq E']
    (u : S → S) (r : S → E → E')
    (hjoint : ∀ s₁ e₁ s₂ e₂,
      u s₁ = u s₂ → r s₁ e₁ = r s₂ e₂ → s₁ = s₂ ∧ e₁ = e₂)
    (xs : List S) (hxd : Distinct xs)
    (hy : ∀ s ∈ xs, ∀ s' ∈ xs, u s = u s')
    (enum : List E) (hEd : Distinct enum)
    (enum' : List E') (_hE'd : Distinct enum')
    (hE'c : ∀ e', e' ∈ enum') :
    xs.length * enum.length ≤ enum'.length := by
  let f : S → List E' := fun s => recordImage r s enum
  have hlen_ge : xs.length * enum.length ≤ (joinMap f xs).length := by
    refine length_joinMap_ge (N := enum.length) ?_
    intro s _
    exact Nat.le_of_eq (recordImage_length r s enum).symm
  have hdist : Distinct (joinMap f xs) := by
    refine distinct_joinMap hxd ?_ ?_
    · intro s _
      exact recordImage_distinct u r hjoint s enum hEd
    · intro s s' hs hs' hne b hb hb'
      match exists_of_mem_map hb with
      | ⟨e₁, _, hre₁⟩ =>
        match exists_of_mem_map hb' with
        | ⟨e₂, _, hre₂⟩ =>
          exact record_images_disjoint u r hjoint s s'
            (hy s hs s' hs') hne e₁ e₂ (hre₁.trans hre₂.symm)
  have hsub : ∀ b, b ∈ joinMap f xs → b ∈ enum' := fun b _ => hE'c b
  have hle : (joinMap f xs).length ≤ enum'.length :=
    length_le_of_distinct_mem hdist hsub
  exact Nat.le_trans hlen_ge hle

/-- Capacity law for enumerated archives at a fixed tick. -/
theorem capacity_law {S : Type} {u : S → S}
    (A : FiniteArchive S u) (T : Nat) [DecidableEq (A.E (T + 1))]
    (xs : List S) (hxd : Distinct xs)
    (hy : ∀ s ∈ xs, ∀ s' ∈ xs, u s = u s') :
    xs.length * A.card T ≤ A.card (T + 1) :=
  capacity_step (E' := A.E (T + 1)) u (A.r T)
    (fun s₁ e₁ s₂ e₂ hu hr => A.joint_inj T s₁ s₂ e₁ e₂ hu hr)
    xs hxd hy
    (A.enum T) (A.enum_distinct T)
    (A.enum (T + 1)) (A.enum_distinct (T + 1))
    (A.enum_complete (T + 1))

/-- **Registration (derived).** On a ≥2 fiber, distinct system states
    receive distinct records (merge ⇒ record separation). Corollary of
    joint injectivity / capacity counting — not a primitive ledger axiom. -/
theorem registration {S E E' : Type}
    (u : S → S) (r : S → E → E')
    (hjoint : ∀ s₁ e₁ s₂ e₂,
      u s₁ = u s₂ → r s₁ e₁ = r s₂ e₂ → s₁ = s₂ ∧ e₁ = e₂)
    (s₁ s₂ : S) (e : E)
    (hsu : u s₁ = u s₂) (hne : s₁ ≠ s₂) :
    r s₁ e ≠ r s₂ e := by
  intro hre
  exact record_images_disjoint u r hjoint s₁ s₂ hsu hne e e hre

/-- Archive form of registration at any tick. -/
theorem archive_registers {S : Type} {u : S → S}
    (A : Archive S u) (T : Nat) (s₁ s₂ : S) (e : A.E T)
    (hsu : u s₁ = u s₂) (hne : s₁ ≠ s₂) :
    A.r T s₁ e ≠ A.r T s₂ e :=
  registration u (A.r T)
    (fun s₁ e₁ s₂ e₂ hu hr => A.joint_inj T s₁ s₂ e₁ e₂ hu hr)
    s₁ s₂ e hsu hne

/-! ## Minimal = saturated schedule -/

/-- Minimal archive schedule: capacity law holds with equality every tick
    along a fixed fiber size `K` (T-15 saturation as defining property). -/
def MinimalSchedule (K : Nat) (card : Nat → Nat) : Prop :=
  ∀ T, card (T + 1) = K * card T

theorem minimal_schedule_closed_form (K card0 : Nat) (card : Nat → Nat)
    (h0 : card 0 = card0)
    (hmin : MinimalSchedule K card) :
    ∀ T, card T = K ^ T * card0 := by
  intro T
  induction T with
  | zero =>
    simpa [Nat.pow_zero, Nat.one_mul] using h0
  | succ T ih =>
    rw [hmin T, ih, Nat.pow_succ, Nat.mul_assoc, Nat.mul_left_comm K]

/-- Ladder predicate count is the minimal K=2 schedule with `|E₀| = 4`. -/
theorem predicate_minimal_schedule :
    MinimalSchedule 2 Density.predicateCount ∧
    Density.predicateCount 0 = 4 ∧
    ∀ T, Density.predicateCount T = 2 ^ T * 4 := by
  refine ⟨?min, ?base, ?closed⟩
  · intro T
    -- predicateCount (T+1) = 2^(T+3) = 2 * 2^(T+2)
    simp only [Density.predicateCount_eq, Nat.pow_succ, Nat.mul_comm]
  · decide
  · intro T
    -- 2^(T+2) = 2^T * 4
    have h : (2 : Nat) ^ (T + 2) = 2 ^ T * 4 := by
      calc 2 ^ (T + 2) = 2 ^ (T + 1 + 1) := rfl
        _ = 2 ^ (T + 1) * 2 := Nat.pow_succ _ _
        _ = (2 ^ T * 2) * 2 := by rw [Nat.pow_succ]
        _ = 2 ^ T * (2 * 2) := by rw [Nat.mul_assoc]
        _ = 2 ^ T * 4 := rfl
    simpa [Density.predicateCount_eq] using h

/-- I-2 arithmetic face: committed caps realise the minimal K=2 schedule. -/
theorem caps_realise_minimal_schedule :
    MinimalSchedule 2 Bridge.Capacity.caps ∧
    Bridge.Capacity.caps 0 = 4 ∧
    ∀ T, Bridge.Capacity.caps T = 2 ^ (T + 2) :=
  ⟨fun T => by
      simp [Bridge.Capacity.caps_eq, Nat.pow_succ, Nat.mul_comm],
   by decide,
   Bridge.Capacity.caps_eq⟩

/-! ## Rigidity heart — partition / exhaustion at equality -/

/-- If a distinct list sits inside another list at equal length, it covers. -/
theorem distinct_subset_eq_length_covers {α : Type} [DecidableEq α]
    {l al : List α} (hdl : Distinct l)
    (hsub : ∀ x, x ∈ l → x ∈ al) (hlen : l.length = al.length) :
    ∀ x, x ∈ al → x ∈ l := by
  intro x hx
  by_cases hxl : x ∈ l
  · exact hxl
  · -- then l ⊆ remove x al, so |l| ≤ |al| - 1, contradicting |l| = |al|
    have hxal : x ∈ al := hx
    have hsub' : ∀ y, y ∈ l → y ∈ remove x al := by
      intro y hy
      exact mem_remove (hsub y hy) (fun hyx => hxl (hyx ▸ hy))
    have hle := length_le_of_distinct_mem hdl hsub'
    have hrlen : (remove x al).length + 1 = al.length :=
      length_remove_of_mem hxal
    -- hle : l.length ≤ (remove x al).length
    -- so l.length + 1 ≤ al.length, but l.length = al.length
    have : l.length + 1 ≤ al.length := by
      rw [← hrlen]
      exact Nat.succ_le_succ hle
    rw [hlen] at this
    exact absurd this (Nat.not_succ_le_self al.length)

/-- At capacity equality, the K record-images partition / cover `enum'`. -/
theorem minimal_step_covers {S E E' : Type} [DecidableEq E']
    (u : S → S) (r : S → E → E')
    (hjoint : ∀ s₁ e₁ s₂ e₂,
      u s₁ = u s₂ → r s₁ e₁ = r s₂ e₂ → s₁ = s₂ ∧ e₁ = e₂)
    (xs : List S) (hxd : Distinct xs)
    (hy : ∀ s ∈ xs, ∀ s' ∈ xs, u s = u s')
    (enum : List E) (hEd : Distinct enum)
    (enum' : List E') (hE'd : Distinct enum')
    (hE'c : ∀ e', e' ∈ enum')
    (heq : xs.length * enum.length = enum'.length) :
    (∀ e', e' ∈ enum' →
      e' ∈ joinMap (fun s => recordImage r s enum) xs) ∧
    (joinMap (fun s => recordImage r s enum) xs).length = enum'.length := by
  let f : S → List E' := fun s => recordImage r s enum
  have hlen_join :
      (joinMap f xs).length = xs.length * enum.length := by
    -- use Provision's exact-length join, or prove via ge + map lengths
    have hge := length_joinMap_ge (f := f) (N := enum.length)
      (l := xs) (fun s _ => Nat.le_of_eq (recordImage_length r s enum).symm)
    -- upper bound: joinMap ⊆ enum' and distinct ⇒ length ≤ |enum'|
    have hdist : Distinct (joinMap f xs) := by
      refine distinct_joinMap hxd ?_ ?_
      · intro s _; exact recordImage_distinct u r hjoint s enum hEd
      · intro s s' hs hs' hne b hb hb'
        match exists_of_mem_map hb with
        | ⟨e₁, _, hre₁⟩ =>
          match exists_of_mem_map hb' with
          | ⟨e₂, _, hre₂⟩ =>
            exact record_images_disjoint u r hjoint s s'
              (hy s hs s' hs') hne e₁ e₂ (hre₁.trans hre₂.symm)
    have hsub : ∀ b, b ∈ joinMap f xs → b ∈ enum' := fun b _ => hE'c b
    have hle := length_le_of_distinct_mem hdist hsub
    -- hge : K*|E| ≤ |join|, hle : |join| ≤ |enum'| = K*|E|
    have hEq' : (joinMap f xs).length = enum'.length :=
      Nat.le_antisymm hle (heq ▸ hge)
    exact hEq'.trans heq.symm
  have hdist : Distinct (joinMap f xs) := by
    refine distinct_joinMap hxd ?_ ?_
    · intro s _; exact recordImage_distinct u r hjoint s enum hEd
    · intro s s' hs hs' hne b hb hb'
      match exists_of_mem_map hb with
      | ⟨e₁, _, hre₁⟩ =>
        match exists_of_mem_map hb' with
        | ⟨e₂, _, hre₂⟩ =>
          exact record_images_disjoint u r hjoint s s'
            (hy s hs s' hs') hne e₁ e₂ (hre₁.trans hre₂.symm)
  have hsub : ∀ b, b ∈ joinMap f xs → b ∈ enum' := fun b _ => hE'c b
  have hlen' : (joinMap f xs).length = enum'.length :=
    hlen_join.trans heq
  refine ⟨?cover, hlen'⟩
  intro e' he'
  exact distinct_subset_eq_length_covers hdist hsub hlen' e' he'

/-- Each fiber record-image has exact length `|enum|` (block size). -/
theorem minimal_block_size {S E E' : Type}
    (r : S → E → E') (s : S) (enum : List E) :
    (recordImage r s enum).length = enum.length :=
  recordImage_length r s enum

/-- **Rigidity fragment.** At saturation equality, fiber record-images
    are pairwise disjoint, each of size `|E|`, and jointly cover `|E'| = K·|E|`.
    Full iso between two UF + pointed archives is `rigidity_iso`. -/
theorem rigidity_partition_fragment {S E E' : Type} [DecidableEq E']
    (u : S → S) (r : S → E → E')
    (hjoint : ∀ s₁ e₁ s₂ e₂,
      u s₁ = u s₂ → r s₁ e₁ = r s₂ e₂ → s₁ = s₂ ∧ e₁ = e₂)
    (xs : List S) (hxd : Distinct xs)
    (hy : ∀ s ∈ xs, ∀ s' ∈ xs, u s = u s')
    (enum : List E) (hEd : Distinct enum)
    (enum' : List E') (hE'd : Distinct enum')
    (hE'c : ∀ e', e' ∈ enum')
    (heq : xs.length * enum.length = enum'.length) :
    (∀ s ∈ xs, (recordImage r s enum).length = enum.length) ∧
    (∀ s ∈ xs, ∀ s' ∈ xs, s ≠ s' →
      ∀ b, b ∈ recordImage r s enum → b ∈ recordImage r s' enum → False) ∧
    (∀ e', e' ∈ enum' →
      e' ∈ joinMap (fun s => recordImage r s enum) xs) := by
  refine ⟨fun s _ => minimal_block_size r s enum, ?_, ?_⟩
  · intro s hs s' hs' hne b hb hb'
    match exists_of_mem_map hb with
    | ⟨e₁, _, h1⟩ =>
      match exists_of_mem_map hb' with
      | ⟨e₂, _, h2⟩ =>
        exact record_images_disjoint u r hjoint s s'
          (hy s hs s' hs') hne e₁ e₂ (h1.trans h2.symm)
  · exact (minimal_step_covers u r hjoint xs hxd hy enum hEd enum' hE'd hE'c heq).1

/-! ## Inductive uniqueness on record-reachable elements -/

/-- Elements generated from `z0` by successive records (reduced archive). -/
inductive Reachable {S : Type} {u : S → S} (A : Archive S u) :
    (T : Nat) → A.E T → Prop where
  | base : Reachable A 0 A.z0
  | step {T : Nat} {e : A.E T} (s : S) :
      Reachable A T e → Reachable A (T + 1) (A.r T s e)

/-- Free words are entirely reachable. -/
theorem free_reachable {S : Type} (u : S → S) :
    ∀ T (w : Word S T), Reachable (free S u) T w := by
  intro T w
  induction w with
  | nil => exact Reachable.base
  | cons s tail ih => exact Reachable.step s ih

/-- Morphisms that agree at `z0` agree on all reachable elements. -/
theorem hom_unique_on_reachable {S : Type} {u : S → S}
    {A B : Archive S u} (h₁ h₂ : Hom A B)
    (hz : h₁.map 0 A.z0 = h₂.map 0 A.z0) :
    ∀ T (e : A.E T), Reachable A T e → h₁.map T e = h₂.map T e := by
  intro T e hr
  induction hr with
  | base => exact hz
  | @step T e s hrec ih =>
    have n₁ := h₁.nat_r T s e
    have n₂ := h₂.nat_r T s e
    rw [n₁, n₂, ih]

/-- **Inductive uniqueness fragment.** On reduced archives (everything
    reachable from `z0`), a Hom is uniquely determined by its value at `z0`.
    Specialises to free archives; UF + pointed singleton gives the packaged
    iso (`rigidity_iso`) once both sides factor uniquely. -/
theorem hom_unique_reduced {S : Type} {u : S → S}
    {A B : Archive S u} (h₁ h₂ : Hom A B)
    (hz : h₁.map 0 A.z0 = h₂.map 0 A.z0)
    (hreach : ∀ T (e : A.E T), Reachable A T e) :
    ∀ T (e : A.E T), h₁.map T e = h₂.map T e :=
  fun T e => hom_unique_on_reachable h₁ h₂ hz T e (hreach T e)

/-- Free-archive case of inductive uniqueness (whole carrier reachable). -/
theorem free_hom_unique_by_z0 {S : Type} {u : S → S}
    {A : Archive S u} (h₁ h₂ : Hom (free S u) A)
    (hz : h₁.map 0 Word.nil = h₂.map 0 Word.nil) :
    ∀ T (w : Word S T), h₁.map T w = h₂.map T w :=
  hom_unique_reduced h₁ h₂ hz (free_reachable u)

/-! ## Carrier reachability from record generation -/

/-- Every letter at `T+1` is some fiber-record of a letter at `T`. -/
def RecordGenerated {S : Type} {u : S → S} (A : Archive S u)
    (xs : List S) : Prop :=
  ∀ T (e' : A.E (T + 1)),
    ∃ s, s ∈ xs ∧ ∃ e : A.E T, e' = A.r T s e

/-- Pointed base: the only letter at tick 0 is `z0`. -/
def PointedSingleton {S : Type} {u : S → S} (A : Archive S u) : Prop :=
  ∀ e : A.E 0, e = A.z0

/-- **Carrier exhaustion.** Pointed singleton + record generation ⇒
    every letter is `Reachable` from `z0`. -/
theorem inductive_carrier_reachable {S : Type} {u : S → S}
    (A : Archive S u) (xs : List S)
    (h0 : PointedSingleton A)
    (hgen : RecordGenerated A xs) :
    ∀ T (e : A.E T), Reachable A T e := by
  intro T
  induction T with
  | zero =>
    intro e
    exact (h0 e) ▸ Reachable.base
  | succ T ih =>
    intro e'
    obtain ⟨s, _hs, e, rfl⟩ := hgen T e'
    exact Reachable.step s (ih e)

/-- On a record-generated pointed archive, a Hom is unique given `z0`. -/
theorem at_most_one_hom_recordGenerated {S : Type} {u : S → S}
    {A B : Archive S u} (h₁ h₂ : Hom A B)
    (hz : h₁.map 0 A.z0 = h₂.map 0 A.z0)
    (xs : List S)
    (h0 : PointedSingleton A)
    (hgen : RecordGenerated A xs) :
    ∀ T (e : A.E T), h₁.map T e = h₂.map T e :=
  hom_unique_reduced h₁ h₂ hz (inductive_carrier_reachable A xs h0 hgen)

/-- Partition cover at equality is the step-instance of `RecordGenerated`
    for enumerated minimal archives (every `e'` lies in some record image). -/
theorem recordGenerated_of_minimal_cover {S E E' : Type} [DecidableEq E']
    (u : S → S) (r : S → E → E')
    (hjoint : ∀ s₁ e₁ s₂ e₂,
      u s₁ = u s₂ → r s₁ e₁ = r s₂ e₂ → s₁ = s₂ ∧ e₁ = e₂)
    (xs : List S) (hxd : Distinct xs)
    (hy : ∀ s ∈ xs, ∀ s' ∈ xs, u s = u s')
    (enum : List E) (hEd : Distinct enum)
    (enum' : List E') (hE'd : Distinct enum')
    (hE'c : ∀ e', e' ∈ enum')
    (heq : xs.length * enum.length = enum'.length) :
    ∀ e', e' ∈ enum' →
      ∃ s, s ∈ xs ∧ ∃ e, e ∈ enum ∧ r s e = e' := by
  intro e' he'
  have hcov :=
    (minimal_step_covers u r hjoint xs hxd hy enum hEd enum' hE'd hE'c heq).1
      e' he'
  -- e' ∈ joinMap (recordImage r · enum) xs
  match mem_joinMap hcov with
  | ⟨s, hs, hb⟩ =>
    match exists_of_mem_map hb with
    | ⟨e, he, hre⟩ => exact ⟨s, hs, e, he, hre⟩

/-! ## Hom existence via unique record factorization -/

/-- Every letter at `T+1` factors uniquely as a single record step. -/
structure UniqueFactorization {S : Type} {u : S → S} (A : Archive S u) where
  factor : (T : Nat) → A.E (T + 1) → S × A.E T
  reconstruct :
    ∀ T (e' : A.E (T + 1)),
      e' = A.r T (factor T e').1 (factor T e').2
  unique :
    ∀ T (e' : A.E (T + 1)) (s : S) (e : A.E T),
      e' = A.r T s e → factor T e' = (s, e)

/-- Free archive has unique factorization (word head / tail). -/
def freeUniqueFactorization (S : Type) (u : S → S) :
    UniqueFactorization (free S u) where
  factor := fun _T w =>
    match w with
    | Word.cons s t => (s, t)
  reconstruct := by
    intro T e'
    cases e'
    rfl
  unique := by
    intro T e' s e h
    cases e'
    cases h
    rfl

/-- Transport a base map along unique factorization to a full Hom. -/
def mapFromUF {S : Type} {u : S → S} {A B : Archive S u}
    (fa : UniqueFactorization A) (h0 : A.E 0 → B.E 0) :
    (T : Nat) → A.E T → B.E T
  | 0, e => h0 e
  | T + 1, e' =>
    B.r T (fa.factor T e').1 (mapFromUF fa h0 T (fa.factor T e').2)

theorem mapFromUF_nat {S : Type} {u : S → S} {A B : Archive S u}
    (fa : UniqueFactorization A) (h0 : A.E 0 → B.E 0)
    (T : Nat) (s : S) (e : A.E T) :
    mapFromUF fa h0 (T + 1) (A.r T s e) =
      B.r T s (mapFromUF fa h0 T e) := by
  have hfac : fa.factor T (A.r T s e) = (s, e) :=
    fa.unique T (A.r T s e) s e rfl
  -- mapFromUF (T+1) unfolds to B.r (factor).1 (mapFromUF (factor).2)
  change B.r T (fa.factor T (A.r T s e)).1
      (mapFromUF fa h0 T (fa.factor T (A.r T s e)).2) =
    B.r T s (mapFromUF fa h0 T e)
  rw [hfac]

/-- **Hom existence.** Unique factorization + pointed base map ⇒ Hom. -/
def homFromUF {S : Type} {u : S → S} {A B : Archive S u}
    (fa : UniqueFactorization A) (h0 : A.E 0 → B.E 0)
    (hz : h0 A.z0 = B.z0) : Hom A B where
  map := mapFromUF fa h0
  map_z0 := hz
  nat_r := fun T s e => mapFromUF_nat fa h0 T s e

/-- Free archive always admits a Hom into any archive (re-proof via UF). -/
def freeHomViaUF {S : Type} {u : S → S} (A : Archive S u) :
    Hom (free S u) A :=
  homFromUF (freeUniqueFactorization S u)
    (fun _ => A.z0) rfl

/-- History embedding: factorisation replay as a free word. -/
def historyWord {S : Type} {u : S → S} {A : Archive S u}
    (fa : UniqueFactorization A) (_h0 : PointedSingleton A) :
    (T : Nat) → A.E T → Word S T
  | 0, _e => Word.nil
  | T + 1, e' =>
    Word.cons (fa.factor T e').1 (historyWord fa _h0 T (fa.factor T e').2)

theorem history_section {S : Type} {u : S → S} {A : Archive S u}
    (fa : UniqueFactorization A) (h0 : PointedSingleton A) :
    ∀ T (e : A.E T), interpret A T (historyWord fa h0 T e) = e := by
  intro T
  induction T with
  | zero =>
    intro e
    exact (h0 e).symm
  | succ T ih =>
    intro e'
    have hrec := fa.reconstruct T e'
    have ih' := ih (fa.factor T e').2
    change A.r T (fa.factor T e').1
        (interpret A T (historyWord fa h0 T (fa.factor T e').2)) = e'
    rw [ih']
    exact hrec.symm

theorem historyWord_step {S : Type} {u : S → S} {A : Archive S u}
    (fa : UniqueFactorization A) (h0 : PointedSingleton A)
    (T : Nat) (s : S) (e : A.E T) :
    historyWord fa h0 (T + 1) (A.r T s e) =
      Word.cons s (historyWord fa h0 T e) := by
  have hfac : fa.factor T (A.r T s e) = (s, e) :=
    fa.unique T (A.r T s e) s e rfl
  change Word.cons (fa.factor T (A.r T s e)).1
      (historyWord fa h0 T (fa.factor T (A.r T s e)).2) =
    Word.cons s (historyWord fa h0 T e)
  rw [hfac]

/-- Hom A → B by pushing history into B's interpret (UF source). -/
def homViaHistory {S : Type} {u : S → S} {A B : Archive S u}
    (fa : UniqueFactorization A) (h0 : PointedSingleton A) : Hom A B where
  map := fun T e => interpret B T (historyWord fa h0 T e)
  map_z0 := rfl
  nat_r := by
    intro T s e
    have hhist := historyWord_step fa h0 T s e
    -- LHS = interpret B (history (A.r s e)) = interpret B (cons s (history e))
    change interpret B (T + 1) (historyWord fa h0 (T + 1) (A.r T s e)) =
      B.r T s (interpret B T (historyWord fa h0 T e))
    rw [hhist]
    rfl

/-- **Hom existence.** Unique factorization + pointed singleton ⇒ Hom into
    any target archive. Free always factorises. -/
theorem hom_exists_of_UF {S : Type} {u : S → S} {A B : Archive S u}
    (fa : UniqueFactorization A) (h0 : PointedSingleton A) :
    ∃ _h : Hom A B, True :=
  ⟨homViaHistory fa h0, True.intro⟩

theorem free_always_factors (S : Type) (u : S → S) :
    ∃ _fa : UniqueFactorization (free S u), True :=
  ⟨freeUniqueFactorization S u, True.intro⟩

theorem free_is_pointed_singleton (S : Type) (u : S → S) :
    PointedSingleton (free S u) := by
  intro e
  cases e
  rfl

/-- Free → any archive via UF. -/
theorem free_hom_exists_via_UF {S : Type} {u : S → S} (A : Archive S u) :
    ∃ _h : Hom (free S u) A, True :=
  hom_exists_of_UF (freeUniqueFactorization S u) (free_is_pointed_singleton S u)

/-- History retracts interpret: every word is the history of its reading. -/
theorem history_retract {S : Type} {u : S → S} {A : Archive S u}
    (fa : UniqueFactorization A) (h0 : PointedSingleton A) :
    ∀ T (w : Word S T), historyWord fa h0 T (interpret A T w) = w := by
  intro T w
  induction w with
  | nil =>
    rfl
  | cons s tail ih =>
    have hfac :
        fa.factor _ (A.r _ s (interpret A _ tail)) = (s, interpret A _ tail) :=
      fa.unique _ (A.r _ s (interpret A _ tail)) s (interpret A _ tail) rfl
    change Word.cons (fa.factor _ (A.r _ s (interpret A _ tail))).1
        (historyWord fa h0 _ (fa.factor _ (A.r _ s (interpret A _ tail))).2) =
      Word.cons s tail
    rw [hfac]
    exact congrArg (Word.cons s) ih

/-- Packaged iso data between two archives. -/
structure ArchiveIso {S : Type} {u : S → S} (A B : Archive S u) where
  toHom : Hom A B
  invHom : Hom B A
  left_inv : ∀ T (e : A.E T), invHom.map T (toHom.map T e) = e
  right_inv : ∀ T (e : B.E T), toHom.map T (invHom.map T e) = e

/-- Every UF + pointed-singleton archive is isomorphic to the free archive. -/
def isoToFree {S : Type} {u : S → S} {A : Archive S u}
    (fa : UniqueFactorization A) (h0 : PointedSingleton A) :
    ArchiveIso A (free S u) where
  toHom := {
    map := historyWord fa h0
    map_z0 := rfl
    nat_r := fun T s e => historyWord_step fa h0 T s e
  }
  invHom := freeHom A
  left_inv := fun T e => history_section fa h0 T e
  right_inv := fun T w => history_retract fa h0 T w

/-- Compose archive isos A ≅ B and B ≅ C. -/
def ArchiveIso.trans {S : Type} {u : S → S} {A B C : Archive S u}
    (i : ArchiveIso A B) (j : ArchiveIso B C) : ArchiveIso A C where
  toHom := {
    map := fun T e => j.toHom.map T (i.toHom.map T e)
    map_z0 := by
      change j.toHom.map 0 (i.toHom.map 0 A.z0) = C.z0
      rw [i.toHom.map_z0, j.toHom.map_z0]
    nat_r := by
      intro T s e
      change j.toHom.map (T + 1) (i.toHom.map (T + 1) (A.r T s e)) =
        C.r T s (j.toHom.map T (i.toHom.map T e))
      rw [i.toHom.nat_r, j.toHom.nat_r]
  }
  invHom := {
    map := fun T e => i.invHom.map T (j.invHom.map T e)
    map_z0 := by
      change i.invHom.map 0 (j.invHom.map 0 C.z0) = A.z0
      rw [j.invHom.map_z0, i.invHom.map_z0]
    nat_r := by
      intro T s e
      change i.invHom.map (T + 1) (j.invHom.map (T + 1) (C.r T s e)) =
        A.r T s (i.invHom.map T (j.invHom.map T e))
      rw [j.invHom.nat_r, i.invHom.nat_r]
  }
  left_inv := by
    intro T e
    change i.invHom.map T (j.invHom.map T (j.toHom.map T (i.toHom.map T e))) = e
    rw [j.left_inv, i.left_inv]
  right_inv := by
    intro T e
    change j.toHom.map T (i.toHom.map T (i.invHom.map T (j.invHom.map T e))) = e
    rw [i.right_inv, j.right_inv]

/-- Inverse of an archive iso. -/
def ArchiveIso.symm {S : Type} {u : S → S} {A B : Archive S u}
    (i : ArchiveIso A B) : ArchiveIso B A where
  toHom := i.invHom
  invHom := i.toHom
  left_inv := i.right_inv
  right_inv := i.left_inv

/-- **Rigidity iso.** Two UF + pointed-singleton archives are isomorphic
    (packaged bijective match via free as intermediary). Base `E 0` is a
    singleton on both sides, so the pointed base bijection is unique. -/
def rigidity_iso {S : Type} {u : S → S} {A B : Archive S u}
    (fa : UniqueFactorization A) (fb : UniqueFactorization B)
    (ha : PointedSingleton A) (hb : PointedSingleton B) :
    ArchiveIso A B :=
  ArchiveIso.trans (isoToFree fa ha) (ArchiveIso.symm (isoToFree fb hb))

/-- Existence form of the rigidity iso. -/
theorem rigidity_iso_of_UF {S : Type} {u : S → S} {A B : Archive S u}
    (fa : UniqueFactorization A) (fb : UniqueFactorization B)
    (ha : PointedSingleton A) (hb : PointedSingleton B) :
    ∃ _i : ArchiveIso A B, True :=
  ⟨rigidity_iso fa fb ha hb, True.intro⟩

/-- Free archive is isomorphic to itself via UF (sanity). -/
theorem free_rigidity_self (S : Type) (u : S → S) :
    ∃ _i : ArchiveIso (free S u) (free S u), True :=
  rigidity_iso_of_UF
    (freeUniqueFactorization S u) (freeUniqueFactorization S u)
    (free_is_pointed_singleton S u) (free_is_pointed_singleton S u)

/-- UF + pointed singleton ⇒ every letter is reachable from `z0`. -/
theorem uf_pointed_carrier_reachable {S : Type} {u : S → S}
    {A : Archive S u} (fa : UniqueFactorization A) (h0 : PointedSingleton A) :
    ∀ T (e : A.E T), Reachable A T e := by
  intro T
  induction T with
  | zero =>
    intro e
    exact (h0 e) ▸ Reachable.base
  | succ T ih =>
    intro e'
    have hrec := fa.reconstruct T e'
    -- e' = A.r (factor).1 (factor).2
    exact hrec ▸ Reachable.step (fa.factor T e').1 (ih (fa.factor T e').2)

/-- At most one Hom under UF + pointed source (given agreement at `z0`). -/
theorem at_most_one_hom_of_UF {S : Type} {u : S → S}
    {A B : Archive S u} (h₁ h₂ : Hom A B)
    (hz : h₁.map 0 A.z0 = h₂.map 0 A.z0)
    (fa : UniqueFactorization A) (h0 : PointedSingleton A) :
    ∀ T (e : A.E T), h₁.map T e = h₂.map T e :=
  hom_unique_reduced h₁ h₂ hz (uf_pointed_carrier_reachable fa h0)

/-- Hom equality from pointwise map equality (Hom is a structure). -/
theorem Hom.ext {S : Type} {u : S → S} {A B : Archive S u}
    (h₁ h₂ : Hom A B) (hm : ∀ T e, h₁.map T e = h₂.map T e) :
    h₁ = h₂ := by
  cases h₁ with
  | mk m₁ z₁ n₁ =>
    cases h₂ with
    | mk m₂ z₂ n₂ =>
      have heq : m₁ = m₂ := funext fun T => funext fun e => hm T e
      cases heq
      rfl

/-- **Graded terminality.** Among UF + pointed-singleton archives, a Hom
    exists and is unique (terminality in this graded subcategory). -/
theorem graded_terminality_of_UF {S : Type} {u : S → S}
    {A B : Archive S u}
    (fa : UniqueFactorization A) (_fb : UniqueFactorization B)
    (ha : PointedSingleton A) (_hb : PointedSingleton B) :
    (∃ _h : Hom A B, True) ∧
    (∀ h₁ h₂ : Hom A B, h₁ = h₂) :=
  ⟨⟨homViaHistory fa ha, True.intro⟩, by
    intro h₁ h₂
    apply Hom.ext h₁ h₂
    intro T e
    have hz : h₁.map 0 A.z0 = h₂.map 0 A.z0 := by
      rw [h₁.map_z0, h₂.map_z0]
    exact at_most_one_hom_of_UF h₁ h₂ hz fa ha T e⟩

/-- Free archive is terminal among UF + pointed archives (re-statement). -/
theorem free_terminal_among_UF {S : Type} {u : S → S}
    {A : Archive S u}
    (fa : UniqueFactorization A) (ha : PointedSingleton A) :
    (∃ _h : Hom A (free S u), True) ∧
    (∀ h₁ h₂ : Hom A (free S u), h₁ = h₂) :=
  graded_terminality_of_UF fa (freeUniqueFactorization S u) ha
    (free_is_pointed_singleton S u)

/-! ## Address-uniform records (`|S| > K` fragment) -/

/-- Record map factors through an address/alphabet index:
    `r_T(s, e) = r̃_T(idx(s), e)`. When `|S| > K`, `idx` collapses the
    system letter onto the blank alphabet; at `K = 2` with `S = Bool`,
    `idx = id` recovers alphabet-UF. -/
structure AddressUniform {S Alph : Type} {u : S → S}
    (A : Archive S u) (idx : S → Alph) where
  rTilt : (T : Nat) → Alph → A.E T → A.E (T + 1)
  factor : ∀ T (s : S) (e : A.E T), A.r T s e = rTilt T (idx s) e

/-- Joint injectivity descends along address factoring when `idx` separates
    on `u`-fibers and `r̃` is jointly injective on the alphabet. -/
theorem joint_inj_of_addressUniform {S Alph : Type} {u : S → S}
    {A : Archive S u} {idx : S → Alph}
    (au : AddressUniform A idx)
    (hidx : ∀ s₁ s₂, u s₁ = u s₂ → idx s₁ = idx s₂ → s₁ = s₂)
    (hrt : ∀ T (a₁ a₂ : Alph) (e₁ e₂ : A.E T),
      au.rTilt T a₁ e₁ = au.rTilt T a₂ e₂ → a₁ = a₂ ∧ e₁ = e₂) :
    ∀ T (s₁ s₂ : S) (e₁ e₂ : A.E T),
      u s₁ = u s₂ → A.r T s₁ e₁ = A.r T s₂ e₂ → s₁ = s₂ ∧ e₁ = e₂ := by
  intro T s₁ s₂ e₁ e₂ hu hr
  have hr' : au.rTilt T (idx s₁) e₁ = au.rTilt T (idx s₂) e₂ := by
    rw [← au.factor, ← au.factor]
    exact hr
  have ⟨ha, he⟩ := hrt T (idx s₁) (idx s₂) e₁ e₂ hr'
  exact ⟨hidx s₁ s₂ hu ha, he⟩

/-- Tick identification (naming ↔ microtick): see
    `Bridge.TickSimulation.tick_identification` (v0.2).
    Historical licensed remnant kept as a pointer of humility. -/
def tick_identification_T2_licensed : True := True.intro

/-! ## I-2 caps archive (Fin schedule, non-singleton base) -/

/-- Cap cardinality `2^(T+2)`. -/
def capCard (T : Nat) : Nat := 2 ^ (T + 2)

theorem capCard_succ (T : Nat) : capCard (T + 1) = 2 * capCard T := by
  simp only [capCard, Nat.pow_succ, Nat.mul_comm]

theorem capCard_pos (T : Nat) : 0 < capCard T :=
  Nat.pow_pos (by decide : 0 < 2)

/-- Encode `(s, e)` into the next cap level (low half = false, high = true). -/
def capRecord {T : Nat} (s : Bool) (e : Fin (capCard T)) :
    Fin (capCard (T + 1)) :=
  Fin.mk
    (e.val + (if s then capCard T else 0))
    (by
      have hcard := capCard_succ T
      have he : e.val < capCard T := e.isLt
      cases s with
      | false =>
        have : e.val < capCard T + capCard T :=
          Nat.lt_of_lt_of_le he (Nat.le_add_right _ _)
        simpa [hcard, Nat.two_mul, Nat.add_zero] using this
      | true =>
        have : e.val + capCard T < capCard T + capCard T :=
          Nat.add_lt_add_right he (capCard T)
        simpa [hcard, Nat.two_mul] using this)

theorem capRecord_val_false {T : Nat} (e : Fin (capCard T)) :
    (capRecord false e).val = e.val := by
  simp [capRecord]

theorem capRecord_val_true {T : Nat} (e : Fin (capCard T)) :
    (capRecord true e).val = e.val + capCard T := by
  simp [capRecord]

theorem capRecord_inj {T : Nat} (s₁ s₂ : Bool)
    (e₁ e₂ : Fin (capCard T))
    (h : capRecord s₁ e₁ = capRecord s₂ e₂) :
    s₁ = s₂ ∧ e₁ = e₂ := by
  have hv : (capRecord s₁ e₁).val = (capRecord s₂ e₂).val :=
    congrArg Fin.val h
  cases s₁ with
  | false =>
    cases s₂ with
    | false =>
      have : e₁.val = e₂.val := by
        simpa [capRecord_val_false] using hv
      exact ⟨rfl, Fin.ext this⟩
    | true =>
      have hv' : e₁.val = e₂.val + capCard T := by
        simpa [capRecord_val_false, capRecord_val_true] using hv
      have hlt : e₁.val < capCard T := e₁.isLt
      have hge : capCard T ≤ e₁.val := by
        have : capCard T ≤ e₂.val + capCard T := Nat.le_add_left _ _
        exact hv' ▸ this
      exact absurd hlt (Nat.not_lt.mpr hge)
  | true =>
    cases s₂ with
    | false =>
      have hv' : e₁.val + capCard T = e₂.val := by
        simpa [capRecord_val_true, capRecord_val_false] using hv
      have hlt : e₂.val < capCard T := e₂.isLt
      have hge : capCard T ≤ e₂.val := by
        have : capCard T ≤ e₁.val + capCard T := Nat.le_add_left _ _
        exact hv' ▸ this
      exact absurd hlt (Nat.not_lt.mpr hge)
    | true =>
      have : e₁.val + capCard T = e₂.val + capCard T := by
        simpa [capRecord_val_true] using hv
      have : e₁.val = e₂.val := Nat.add_right_cancel this
      exact ⟨rfl, Fin.ext this⟩

/-- Bound for the high-half tail index. -/
theorem cap_high_tail_lt {T : Nat} {v : Nat}
    (hge : capCard T ≤ v) (hlt : v < capCard (T + 1)) :
    v - capCard T < capCard T :=
  Nat.sub_lt_left_of_lt_add hge (by
    have : v < 2 * capCard T := by
      simpa [capCard_succ T] using hlt
    simpa [Nat.two_mul] using this)

/-- Factor a cap letter into recording bit + prior index (alphabet = Bool). -/
def capFactor {T : Nat} (e' : Fin (capCard (T + 1))) :
    Bool × Fin (capCard T) :=
  if h : capCard T ≤ e'.val then
    (true, ⟨e'.val - capCard T, cap_high_tail_lt h e'.isLt⟩)
  else
    (false, ⟨e'.val, Nat.lt_of_not_ge h⟩)

theorem capFactor_of_lt {T : Nat} (e' : Fin (capCard (T + 1)))
    (hlt : e'.val < capCard T) :
    capFactor e' = (false, ⟨e'.val, hlt⟩) := by
  have h : ¬ capCard T ≤ e'.val := Nat.not_le.mpr hlt
  simp only [capFactor, dif_neg h]

theorem capFactor_of_ge {T : Nat} (e' : Fin (capCard (T + 1)))
    (hge : capCard T ≤ e'.val) :
    capFactor e' =
      (true, ⟨e'.val - capCard T, cap_high_tail_lt hge e'.isLt⟩) := by
  simp only [capFactor, dif_pos hge]

theorem capFactor_reconstruct {T : Nat} (e' : Fin (capCard (T + 1))) :
    e' = capRecord (capFactor e').1 (capFactor e').2 := by
  by_cases h : capCard T ≤ e'.val
  · have hfac := capFactor_of_ge e' h
    -- rewrite both projections via hfac
    have h1 : (capFactor e').1 = true := congrArg Prod.fst hfac
    have h2 : (capFactor e').2 =
        ⟨e'.val - capCard T, cap_high_tail_lt h e'.isLt⟩ :=
      congrArg Prod.snd hfac
    apply Fin.ext
    rw [h1, h2, capRecord_val_true]
    exact (Nat.sub_add_cancel h).symm
  · have hlt : e'.val < capCard T := Nat.lt_of_not_ge h
    have hfac := capFactor_of_lt e' hlt
    have h1 : (capFactor e').1 = false := congrArg Prod.fst hfac
    have h2 : (capFactor e').2 = ⟨e'.val, hlt⟩ := congrArg Prod.snd hfac
    apply Fin.ext
    rw [h1, h2, capRecord_val_false]

theorem capFactor_unique {T : Nat} (e' : Fin (capCard (T + 1)))
    (s : Bool) (e : Fin (capCard T))
    (hre : e' = capRecord s e) :
    capFactor e' = (s, e) := by
  subst hre
  cases s with
  | false =>
    have hlt : (capRecord false e).val < capCard T := by
      rw [capRecord_val_false]; exact e.isLt
    rw [capFactor_of_lt _ hlt]
    refine Prod.ext rfl (Fin.ext ?_)
    exact capRecord_val_false e
  | true =>
    have hge : capCard T ≤ (capRecord true e).val := by
      rw [capRecord_val_true]; exact Nat.le_add_left _ _
    rw [capFactor_of_ge _ hge]
    refine Prod.ext rfl (Fin.ext ?_)
    -- (capRecord true e).val - capCard T = e.val
    calc (capRecord true e).val - capCard T
        = (e.val + capCard T) - capCard T := by rw [capRecord_val_true]
      _ = e.val := Nat.add_sub_cancel _ _

/-- **I-2 Bool caps archive.** Carrier `Fin (2^(T+2))` with half-split
    record map. Realises the minimal K=2 schedule with `|E₀| = 4`.
    Here `S = Bool =` alphabet (`Kmin`), so UF = bijection of the minimal
    step — the alphabet-UF / address-uniform case at K = 2. -/
def boolCapsArchive (u : Bool → Bool) : Archive Bool u where
  E := fun T => Fin (capCard T)
  z0 := ⟨0, by decide⟩
  r := fun _ s e => capRecord s e
  joint_inj := by
    intro _T s₁ s₂ e₁ e₂ _hu hr
    exact capRecord_inj s₁ s₂ e₁ e₂ hr

/-- Caps archive admits unique factorization (minimal alphabet-UF). -/
def boolCapsUF (u : Bool → Bool) :
    UniqueFactorization (boolCapsArchive u) where
  factor := fun _T e' => capFactor e'
  reconstruct := fun _T e' => capFactor_reconstruct e'
  unique := fun _T e' s e h => capFactor_unique e' s e h

/-- Caps base is not a pointed singleton (`|E₀| = 4`). -/
theorem boolCaps_not_pointedSingleton (_u : Bool → Bool) :
    ¬ PointedSingleton (boolCapsArchive _u) := by
  intro h
  have h1 := h ⟨1, by decide⟩
  have : (1 : Nat) = 0 := congrArg Fin.val h1
  exact absurd this (by decide)

/-- Caps levels realise the committed capacity schedule. -/
theorem boolCaps_card_eq_caps (_u : Bool → Bool) :
    (∀ T, capCard T = Bridge.Capacity.caps T) ∧
    MinimalSchedule 2 capCard ∧
    capCard 0 = 4 :=
  ⟨fun T => by simp [capCard, Bridge.Capacity.caps_eq],
   fun T => capCard_succ T,
   rfl⟩

/-- Record map is injective in the letter (registration face of the Fin archive). -/
theorem boolCaps_registers (u : Bool → Bool) (T : Nat)
    (s₁ s₂ : Bool) (e : Fin (capCard T))
    (hsu : u s₁ = u s₂) (hne : s₁ ≠ s₂) :
    (boolCapsArchive u).r T s₁ e ≠ (boolCapsArchive u).r T s₂ e :=
  archive_registers (boolCapsArchive u) T s₁ s₂ e hsu hne

/-! ## Base-relative rigidity (minimal / non-singleton UF) -/

/-- Under UF alone, a Hom is unique given agreement on the whole base `E 0`
    (no PointedSingleton required). -/
theorem hom_unique_of_UF {S : Type} {u : S → S}
    {A B : Archive S u} (h₁ h₂ : Hom A B)
    (hbase : ∀ e0 : A.E 0, h₁.map 0 e0 = h₂.map 0 e0)
    (fa : UniqueFactorization A) :
    ∀ T (e : A.E T), h₁.map T e = h₂.map T e := by
  intro T
  induction T with
  | zero =>
    exact hbase
  | succ T ih =>
    intro e'
    have hrec := fa.reconstruct T e'
    -- rewrite e' via reconstruct, then naturality
    calc
      h₁.map (T + 1) e'
          = h₁.map (T + 1) (A.r T (fa.factor T e').1 (fa.factor T e').2) := by
            rw [← hrec]
      _ = B.r T (fa.factor T e').1 (h₁.map T (fa.factor T e').2) :=
            h₁.nat_r T (fa.factor T e').1 (fa.factor T e').2
      _ = B.r T (fa.factor T e').1 (h₂.map T (fa.factor T e').2) := by
            rw [ih (fa.factor T e').2]
      _ = h₂.map (T + 1) (A.r T (fa.factor T e').1 (fa.factor T e').2) :=
            (h₂.nat_r T (fa.factor T e').1 (fa.factor T e').2).symm
      _ = h₂.map (T + 1) e' := by rw [← hrec]

/-- `mapFromUF` is left-inverse to itself across a base retraction. -/
theorem mapFromUF_left_inv {S : Type} {u : S → S} {A B : Archive S u}
    (fa : UniqueFactorization A) (fb : UniqueFactorization B)
    (h0 : A.E 0 → B.E 0) (k0 : B.E 0 → A.E 0)
    (hleft : ∀ e, k0 (h0 e) = e) :
    ∀ T (e : A.E T),
      mapFromUF fb k0 T (mapFromUF fa h0 T e) = e := by
  intro T
  induction T with
  | zero =>
    intro e; exact hleft e
  | succ T ih =>
    intro e'
    let s := (fa.factor T e').1
    let e := (fa.factor T e').2
    have hrec : e' = A.r T s e := fa.reconstruct T e'
    -- unfold mapFromUF fa at successor
    have hmap :
        mapFromUF fa h0 (T + 1) e' =
          B.r T s (mapFromUF fa h0 T e) := by
      change B.r T (fa.factor T e').1
          (mapFromUF fa h0 T (fa.factor T e').2) =
        B.r T s (mapFromUF fa h0 T e)
      rfl
    rw [hmap]
    -- unfold mapFromUF fb at B.r
    have hfacB :
        fb.factor T (B.r T s (mapFromUF fa h0 T e)) =
          (s, mapFromUF fa h0 T e) :=
      fb.unique T _ s _ rfl
    change A.r T
        (fb.factor T (B.r T s (mapFromUF fa h0 T e))).1
        (mapFromUF fb k0 T
          (fb.factor T (B.r T s (mapFromUF fa h0 T e))).2) = e'
    rw [hfacB]
    -- A.r s (mapFromUF fb (mapFromUF fa e)) = A.r s e = e'
    rw [ih e]
    exact hrec.symm

/-- **Base-relative rigidity iso.** Two UF archives are isomorphic once a
    base bijection `h₀` (with inverse) is fixed — including non-singleton
    bases such as `|E₀| = 4`. PointedSingleton is the special case where
    `h₀` is unique. -/
def rigidity_iso_of_base {S : Type} {u : S → S} {A B : Archive S u}
    (fa : UniqueFactorization A) (fb : UniqueFactorization B)
    (h0 : A.E 0 → B.E 0) (k0 : B.E 0 → A.E 0)
    (hleft : ∀ e, k0 (h0 e) = e)
    (hright : ∀ e, h0 (k0 e) = e)
    (hz : h0 A.z0 = B.z0) :
    ArchiveIso A B where
  toHom := homFromUF fa h0 hz
  invHom :=
    homFromUF fb k0 (by
      -- k0 B.z0 = k0 (h0 A.z0) = A.z0
      calc k0 B.z0 = k0 (h0 A.z0) := by rw [hz]
        _ = A.z0 := hleft A.z0)
  left_inv := fun T e => mapFromUF_left_inv fa fb h0 k0 hleft T e
  right_inv := fun T e => mapFromUF_left_inv fb fa k0 h0 hright T e

/-- Hom existence + uniqueness for UF archives relative to a fixed base map. -/
theorem graded_terminality_of_base {S : Type} {u : S → S}
    {A B : Archive S u}
    (fa : UniqueFactorization A) (_fb : UniqueFactorization B)
    (h0 : A.E 0 → B.E 0) (hz : h0 A.z0 = B.z0) :
    (∃ _h : Hom A B, True) ∧
    (∀ h₁ h₂ : Hom A B,
      (∀ e0, h₁.map 0 e0 = h0 e0) →
      (∀ e0, h₂.map 0 e0 = h0 e0) →
      h₁ = h₂) := by
  refine ⟨⟨homFromUF fa h0 hz, True.intro⟩, ?_⟩
  intro h₁ h₂ hb1 hb2
  apply Hom.ext h₁ h₂
  intro T e
  have h12 : ∀ e0, h₁.map 0 e0 = h₂.map 0 e0 := fun e0 =>
    (hb1 e0).trans (hb2 e0).symm
  exact hom_unique_of_UF h₁ h₂ h12 fa T e

/-! ## Straightening — append-only normal form mod record gauge -/

/-- Append-only archive on a frozen base: letters are `(base, word)`,
    and each record prepends without reshuffling prior base labels.
    This is the normal form targeted by the T-2 straightening plan. -/
def freeOnBase (S : Type) (u : S → S) (Base : Type) (zBase : Base) :
    Archive S u where
  E := fun T => Base × Word S T
  z0 := (zBase, Word.nil)
  r := fun _ s p => (p.1, Word.cons s p.2)
  joint_inj := by
    intro T s₁ s₂ ⟨b₁, w₁⟩ ⟨b₂, w₂⟩ _ hr
    have hb : b₁ = b₂ := congrArg Prod.fst hr
    have hw : Word.cons s₁ w₁ = Word.cons s₂ w₂ := congrArg Prod.snd hr
    cases hw
    exact ⟨rfl, by cases hb; rfl⟩

/-- Unique factorization for the append-only-on-base archive. -/
def freeOnBaseUF (S : Type) (u : S → S) (Base : Type) (zBase : Base) :
    UniqueFactorization (freeOnBase S u Base zBase) where
  factor := fun _T p =>
    match p with
    | (b, Word.cons s t) => (s, (b, t))
  reconstruct := by
    intro T e'
    cases e' with
    | mk b w =>
      cases w with
      | cons s t => rfl
  unique := by
    intro T e' s e h
    cases e' with
    | mk b w =>
      cases w with
      | cons s' t =>
        cases e with
        | mk b' t' =>
          cases h
          rfl

/-- **Induction step (archive face).** On `freeOnBase`, one microtick is
    exactly one append: freeze the base letter, `Word.cons` the system
    letter. This is the operational content of T-2 induction glue on Dil
    carriers — not a `Registration → Ladder.Level` functor. -/
theorem freeOnBase_append_step (S : Type) (u : S → S) (Base : Type)
    (zBase : Base) (T : Nat) (s : S) (e0 : Base) (w : Word S T) :
    (freeOnBase S u Base zBase).r T s (e0, w) = (e0, Word.cons s w) :=
  rfl

/-- Peel after append: UF factor recovers the just-written letter and prior
    archive letter (namer-shaped invertibility on history). -/
theorem freeOnBase_factor_cons (S : Type) (u : S → S) (Base : Type)
    (zBase : Base) (T : Nat) (s : S) (e0 : Base) (w : Word S T) :
    (freeOnBaseUF S u Base zBase).factor T (e0, Word.cons s w) =
      (s, (e0, w)) :=
  rfl

/-- Replay a free word from an arbitrary base letter (not just `z0`). -/
def interpretFromBase {S : Type} {u : S → S} (A : Archive S u) :
    (T : Nat) → A.E 0 → Word S T → A.E T
  | 0, e0, _ => e0
  | T + 1, e0, Word.cons s w =>
      A.r T s (interpretFromBase A T e0 w)

/-- Peel a UF letter to its base seed + append-only history word. -/
def factorHistory {S : Type} {u : S → S} {A : Archive S u}
    (fa : UniqueFactorization A) :
    (T : Nat) → A.E T → A.E 0 × Word S T
  | 0, e => (e, Word.nil)
  | T + 1, e' =>
      let s := (fa.factor T e').1
      let e := (fa.factor T e').2
      let p := factorHistory fa T e
      (p.1, Word.cons s p.2)

theorem factorHistory_step {S : Type} {u : S → S} {A : Archive S u}
    (fa : UniqueFactorization A) (T : Nat) (s : S) (e : A.E T) :
    factorHistory fa (T + 1) (A.r T s e) =
      ((factorHistory fa T e).1, Word.cons s (factorHistory fa T e).2) := by
  have hfac : fa.factor T (A.r T s e) = (s, e) :=
    fa.unique T (A.r T s e) s e rfl
  -- unfold factorHistory at successor
  change
      let s' := (fa.factor T (A.r T s e)).1
      let e' := (fa.factor T (A.r T s e)).2
      let p := factorHistory fa T e'
      (p.1, Word.cons s' p.2) =
    ((factorHistory fa T e).1, Word.cons s (factorHistory fa T e).2)
  simp only [hfac]

theorem factorHistory_section {S : Type} {u : S → S} {A : Archive S u}
    (fa : UniqueFactorization A) :
    ∀ T (e : A.E T),
      interpretFromBase A T (factorHistory fa T e).1 (factorHistory fa T e).2 = e := by
  intro T
  induction T with
  | zero =>
    intro e
    rfl
  | succ T ih =>
    intro e'
    have hrec := fa.reconstruct T e'
    have ih' := ih (fa.factor T e').2
    -- interpretFromBase (cons s w) = A.r s (interpretFromBase w)
    change A.r T (fa.factor T e').1
        (interpretFromBase A T
          (factorHistory fa T (fa.factor T e').2).1
          (factorHistory fa T (fa.factor T e').2).2) = e'
    rw [ih']
    exact hrec.symm

theorem factorHistory_retract {S : Type} {u : S → S} {A : Archive S u}
    (fa : UniqueFactorization A) :
    ∀ T (e0 : A.E 0) (w : Word S T),
      factorHistory fa T (interpretFromBase A T e0 w) = (e0, w) := by
  intro T e0 w
  induction w with
  | nil =>
    rfl
  | cons s tail ih =>
    have hfac :
        fa.factor _ (A.r _ s (interpretFromBase A _ e0 tail)) =
          (s, interpretFromBase A _ e0 tail) :=
      fa.unique _ _ s _ rfl
    -- factorHistory (succ) (A.r s …) expands via factor then IH
    change
        let s' := (fa.factor _ (A.r _ s (interpretFromBase A _ e0 tail))).1
        let e' := (fa.factor _ (A.r _ s (interpretFromBase A _ e0 tail))).2
        let p := factorHistory fa _ e'
        (p.1, Word.cons s' p.2) =
      (e0, Word.cons s tail)
    simp only [hfac]
    exact congrArg (fun p => (p.1, Word.cons s p.2)) ih

/-- **Straightening iso.** Every UF archive is isomorphic to the append-only
    archive on its own base (`freeOnBase`). Record gauge = base relabelling;
    uniqueness of Homs is exactly agreement on `E 0` (`hom_unique_of_UF`).

    Fence: Fin/UF archives only. Not Registration→`NamingExtension` on carriers.
    Does not discharge unconditional T-2; eternal `swapStep` remains obstructed. -/
def isoToFreeOnBase {S : Type} {u : S → S} {A : Archive S u}
    (fa : UniqueFactorization A) :
    ArchiveIso A (freeOnBase S u (A.E 0) A.z0) where
  toHom := {
    map := fun T e => factorHistory fa T e
    map_z0 := rfl
    nat_r := fun T s e => factorHistory_step fa T s e
  }
  invHom := {
    map := fun T p => interpretFromBase A T p.1 p.2
    map_z0 := rfl
    nat_r := by
      intro T s p
      -- interpretFromBase (cons s w) from base = A.r s (interpret …)
      cases p with
      | mk e0 w =>
        rfl
  }
  left_inv := fun T e => factorHistory_section fa T e
  right_inv := fun T p => by
    cases p with
    | mk e0 w =>
      exact factorHistory_retract fa T e0 w

/-- Existence form: UF archives straighten to append-only mod base. -/
theorem uf_straightens_mod_base {S : Type} {u : S → S} {A : Archive S u}
    (fa : UniqueFactorization A) :
    ∃ _i : ArchiveIso A (freeOnBase S u (A.E 0) A.z0), True :=
  ⟨isoToFreeOnBase fa, True.intro⟩

/-- Pointed special case: UF + singleton base ≅ free (existing `isoToFree`).
    Append-only normal form with trivial gauge. -/
theorem uf_pointed_straightens_to_free {S : Type} {u : S → S}
    {A : Archive S u}
    (fa : UniqueFactorization A) (h0 : PointedSingleton A) :
    ∃ _i : ArchiveIso A (free S u), True :=
  ⟨isoToFree fa h0, True.intro⟩

/-- Record gauge leftover = base bijection: Hom uniqueness among UF archives
    is exactly agreement on all of `E 0` (rephrase of `hom_unique_of_UF`). -/
theorem record_gauge_is_base_bijection {S : Type} {u : S → S}
    {A B : Archive S u} (h₁ h₂ : Hom A B)
    (hbase : ∀ e0 : A.E 0, h₁.map 0 e0 = h₂.map 0 e0)
    (fa : UniqueFactorization A) :
    h₁ = h₂ :=
  Hom.ext h₁ h₂ (fun T e => hom_unique_of_UF h₁ h₂ hbase fa T e)

/-- Bool caps (non-pointed `|E₀|=4`) straightens mod base to append-only. -/
theorem boolCaps_straightens_mod_base (u : Bool → Bool) :
    (∃ _i : ArchiveIso (boolCapsArchive u)
      (freeOnBase Bool u (Fin (capCard 0)) (boolCapsArchive u).z0), True) ∧
    (¬ PointedSingleton (boolCapsArchive u)) ∧
    Bridge.Alphabet.Kmin = 2 :=
  ⟨uf_straightens_mod_base (boolCapsUF u),
   boolCaps_not_pointedSingleton u,
   Bridge.Alphabet.Kmin_eq⟩

/-- **Straightening fragment package.** UF⇒append-only-on-base; pointed⇒free;
    gauge = base agreement; Bool caps instance. Fence: does not close T-2. -/
theorem straighten_fragment :
    (∀ {S : Type} {u : S → S} {A : Archive S u}
      (_fa : UniqueFactorization A),
      ∃ _i : ArchiveIso A (freeOnBase S u (A.E 0) A.z0), True) ∧
    (∀ {S : Type} {u : S → S} {A : Archive S u}
      (_fa : UniqueFactorization A) (_h0 : PointedSingleton A),
      ∃ _i : ArchiveIso A (free S u), True) ∧
    (∀ {S : Type} {u : S → S} {A B : Archive S u}
      (h₁ h₂ : Hom A B)
      (_hbase : ∀ e0, h₁.map 0 e0 = h₂.map 0 e0)
      (_fa : UniqueFactorization A), h₁ = h₂) ∧
    (∀ u : Bool → Bool,
      ∃ _i : ArchiveIso (boolCapsArchive u)
        (freeOnBase Bool u (Fin (capCard 0)) (boolCapsArchive u).z0), True) ∧
    Bridge.Alphabet.Kmin = 2 :=
  ⟨fun fa => uf_straightens_mod_base fa,
   fun fa h0 => uf_pointed_straightens_to_free fa h0,
   fun h₁ h₂ hbase fa => record_gauge_is_base_bijection h₁ h₂ hbase fa,
   fun u => (boolCaps_straightens_mod_base u).1,
   Bridge.Alphabet.Kmin_eq⟩

/-- **I-2 Fin closed (alphabet-UF).** Bool caps archive is UF (minimal
    bijection at `K = 2`), schedule-correct, non-pointed, and rigid
    relative to the identity base bijection. -/
theorem i2_fin_closed (u : Bool → Bool) :
    (∃ _fa : UniqueFactorization (boolCapsArchive u), True) ∧
    (¬ PointedSingleton (boolCapsArchive u)) ∧
    MinimalSchedule 2 capCard ∧
    (∀ T, capCard T = Bridge.Capacity.caps T) ∧
    (∀ T, capCard T = 2 ^ (T + 2)) ∧
    (∃ _i : ArchiveIso (boolCapsArchive u) (boolCapsArchive u), True) ∧
    Bridge.Alphabet.Kmin = 2 :=
  ⟨⟨boolCapsUF u, True.intro⟩,
   boolCaps_not_pointedSingleton u,
   fun T => capCard_succ T,
   fun T => by simp [capCard, Bridge.Capacity.caps_eq],
   fun _ => rfl,
   ⟨rigidity_iso_of_base (boolCapsUF u) (boolCapsUF u)
      id id (fun _ => rfl) (fun _ => rfl) rfl, True.intro⟩,
   Bridge.Alphabet.Kmin_eq⟩

/-- Backward-compatible fragment name. -/
theorem i2_caps_record_map_fragment (u : Bool → Bool) :
    (∃ _A : Archive Bool u, True) ∧
    (¬ PointedSingleton (boolCapsArchive u)) ∧
    MinimalSchedule 2 capCard ∧
    (∀ T, capCard T = Bridge.Capacity.caps T) ∧
    (∀ T, capCard T = 2 ^ (T + 2)) ∧
    Bridge.Alphabet.Kmin = 2 :=
  ⟨⟨boolCapsArchive u, True.intro⟩,
   (i2_fin_closed u).2.1,
   (i2_fin_closed u).2.2.1,
   (i2_fin_closed u).2.2.2.1,
   (i2_fin_closed u).2.2.2.2.1,
   Bridge.Alphabet.Kmin_eq⟩

/-- Bool caps is address-uniform with trivial `idx = id` (letter = alphabet). -/
def boolCaps_addressUniform (u : Bool → Bool) :
    AddressUniform (boolCapsArchive u) id where
  rTilt := fun _ a e => capRecord a e
  factor := fun _ _ _ => rfl

/-- Address-uniformity recovers the archive's joint injectivity at K = 2. -/
theorem boolCaps_joint_inj_via_addressUniform (u : Bool → Bool) :
    ∀ T (s₁ s₂ : Bool) (e₁ e₂ : Fin (capCard T)),
      u s₁ = u s₂ →
      (boolCapsArchive u).r T s₁ e₁ = (boolCapsArchive u).r T s₂ e₂ →
      s₁ = s₂ ∧ e₁ = e₂ :=
  joint_inj_of_addressUniform (boolCaps_addressUniform u)
    (fun _ _ _ hidx => hidx)
    (fun _ a₁ a₂ e₁ e₂ hr => capRecord_inj a₁ a₂ e₁ e₂ hr)

/-- **Ladder-predicate addressing witness.** Combinatorial count of
    `Ladder.Level T → Bool` (= `Branch.Predicate`) is `predicateCount` /
    `caps`; the Fin `boolCapsArchive` realises that schedule under
    alphabet-UF. Not a second `Archive` carrier on predicates. -/
theorem ladder_predicate_addressing_witness :
    (∀ T, Density.predicateCount T = 2 ^ Density.levelCard T) ∧
    (∀ T, Density.predicateCount T = Bridge.Capacity.caps T) ∧
    (∀ T, Density.levelCard T = T + 2) ∧
    (∀ T, capCard T = Bridge.Capacity.caps T) ∧
    MinimalSchedule 2 Density.predicateCount ∧
    MinimalSchedule 2 capCard ∧
    (∀ u : Bool → Bool, ∃ _fa : UniqueFactorization (boolCapsArchive u), True) ∧
    (∀ u : Bool → Bool, ∃ _au : AddressUniform (boolCapsArchive u) id, True) ∧
    Bridge.Alphabet.Kmin = 2 :=
  ⟨fun T => rfl,
   fun T => rfl,
   Density.levelCard_eq,
   fun T => by simp [capCard, Bridge.Capacity.caps_eq],
   predicate_minimal_schedule.1,
   fun T => capCard_succ T,
   fun u => ⟨boolCapsUF u, True.intro⟩,
   fun u => ⟨boolCaps_addressUniform u, True.intro⟩,
   Bridge.Alphabet.Kmin_eq⟩

/-! ## Keystone sprint package -/

/-- **Keystone Dil sprint.** Free archive initial; capacity step law;
    registration corollary; ladder/caps realise minimal K=2 schedule;
    rigidity partition; UF rigidity iso; graded terminality among UF +
    pointed archives. I-2 Fin alphabet-UF closed (`i2_fin_closed`). -/
theorem keystone_dil_sprint :
    (∀ {S : Type} {u : S → S} (A : Archive S u),
      (∃ _h : Hom (free S u) A, True) ∧
      (∀ h₁ h₂ : Hom (free S u) A, h₁ = h₂)) ∧
    (∀ {S E E' : Type} [DecidableEq E'] (u : S → S) (r : S → E → E'),
      (∀ s₁ e₁ s₂ e₂,
        u s₁ = u s₂ → r s₁ e₁ = r s₂ e₂ → s₁ = s₂ ∧ e₁ = e₂) →
      ∀ xs : List S, Distinct xs →
        (∀ s ∈ xs, ∀ s' ∈ xs, u s = u s') →
        ∀ enum : List E, Distinct enum →
          ∀ enum' : List E', Distinct enum' →
            (∀ e', e' ∈ enum') →
            xs.length * enum.length ≤ enum'.length) ∧
    (∀ {S E E' : Type} (u : S → S) (r : S → E → E'),
      (∀ s₁ e₁ s₂ e₂,
        u s₁ = u s₂ → r s₁ e₁ = r s₂ e₂ → s₁ = s₂ ∧ e₁ = e₂) →
      ∀ s₁ s₂ e, u s₁ = u s₂ → s₁ ≠ s₂ → r s₁ e ≠ r s₂ e) ∧
    MinimalSchedule 2 Bridge.Capacity.caps ∧
    (∀ T, Bridge.Capacity.caps T = 2 ^ (T + 2)) ∧
    Bridge.Alphabet.Kmin = 2 :=
  ⟨fun A => free_initial A,
   fun u r hjoint xs hxd hy enum hEd enum' hE'd hE'c =>
     capacity_step u r hjoint xs hxd hy enum hEd enum' hE'd hE'c,
   fun u r hjoint s₁ s₂ e hsu hne => registration u r hjoint s₁ s₂ e hsu hne,
   caps_realise_minimal_schedule.1,
   caps_realise_minimal_schedule.2.2,
   Bridge.Alphabet.Kmin_eq⟩

#print axioms free_initial
#print axioms capacity_step
#print axioms registration
#print axioms rigidity_partition_fragment
#print axioms hom_unique_on_reachable
#print axioms free_hom_unique_by_z0
#print axioms inductive_carrier_reachable
#print axioms at_most_one_hom_recordGenerated
#print axioms recordGenerated_of_minimal_cover
#print axioms mapFromUF_nat
#print axioms hom_exists_of_UF
#print axioms free_hom_exists_via_UF
#print axioms history_section
#print axioms history_retract
#print axioms rigidity_iso_of_UF
#print axioms free_rigidity_self
#print axioms graded_terminality_of_UF
#print axioms hom_unique_of_UF
#print axioms rigidity_iso_of_base
#print axioms factorHistory_section
#print axioms factorHistory_retract
#print axioms uf_straightens_mod_base
#print axioms uf_pointed_straightens_to_free
#print axioms record_gauge_is_base_bijection
#print axioms boolCaps_straightens_mod_base
#print axioms straighten_fragment
#print axioms i2_fin_closed
#print axioms i2_caps_record_map_fragment
#print axioms joint_inj_of_addressUniform
#print axioms ladder_predicate_addressing_witness
#print axioms predicate_minimal_schedule
#print axioms caps_realise_minimal_schedule
#print axioms keystone_dil_sprint

end Bridge.Dil
