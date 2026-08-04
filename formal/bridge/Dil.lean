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

Still open (typed markers): uniform-fiber rigidity isomorphism; graded
terminality; full predicate-space record map. Tick identification remains
T-2-licensed. See `docs/` keystone notes / RESIDUE.
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

/-- **Registration corollary.** On a ≥2 fiber, distinct system states
    receive distinct records (merge ⇒ record separation). -/
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

/-! ## Open markers (typed teeth) -/

/-- Uniform-fiber rigidity: any two minimal archives for uniformly K-to-1
    `u` are uniquely isomorphic once `E 0` is matched. Open — partition
    lemma not yet mechanised. -/
def rigidity_uniform_open : True := True.intro

/-- Graded terminality of the ladder minimal archive among reduced
    u-graded archives. Open — addressing obstruction flagged in sketch. -/
def graded_terminality_open : True := True.intro

/-- Tick identification (naming ↔ microtick) remains T-2-licensed. -/
def tick_identification_T2_licensed : True := True.intro

/-! ## Keystone sprint package -/

/-- **Keystone Dil sprint.** Free archive initial; capacity step law;
    registration corollary; ladder/caps realise minimal K=2 schedule.
    Rigidity / graded terminality / full I-2 record-map realisation remain open. -/
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
#print axioms predicate_minimal_schedule
#print axioms caps_realise_minimal_schedule
#print axioms keystone_dil_sprint

end Bridge.Dil
