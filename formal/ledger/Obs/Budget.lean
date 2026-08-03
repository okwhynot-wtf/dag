import Obs.StochasticUnlock

/-!
# Obs.Budget

Freshness budget: per-tick and run-level product bounds, saturation
conditions, Dirac embedding into the counting second law.
-/

set_option linter.unusedSectionVars false

namespace Obs.Budget

open Obs.StochasticUnlock

variable {X E S E' : Type}

/-! ### B1: the budget, per tick and per run -/

/-- **B1, per tick.** The realized in-degree of a merged fiber is at most
the size of the record alphabet consumed that tick: `K_t ≤ |E_t|`. This
is Thm 3.2 (`env_alphabet_ge_indegree`) with the rate reading -- stated
as a corollary, not reproved. -/
theorem budget_tick [DecidableEq E'] (G : X × E → S × E')
    (hinj : ∀ a b : X × E, G a = G b → a = b) (e0 : E) (s : S)
    (xs : List X) (hd : Distinct xs)
    (hsys : ∀ x, x ∈ xs → (G (x, e0)).1 = s)
    (Es : List E') (halph : ∀ x, x ∈ xs → (G (x, e0)).2 ∈ Es) :
    xs.length ≤ Es.length :=
  env_alphabet_ge_indegree G hinj e0 s xs hd hsys Es halph

/-- Product of `f 0 * f 1 * ⋯ * f (T-1)` (the run budget). -/
def prodBelow (f : Nat → Nat) : Nat → Nat
  | 0 => 1
  | T + 1 => prodBelow f T * f T

theorem prodBelow_mono {f g : Nat → Nat} :
    ∀ T : Nat, (∀ t, t < T → f t ≤ g t) →
      prodBelow f T ≤ prodBelow g T := by
  intro T
  induction T with
  | zero => intro _; exact Nat.le_refl 1
  | succ T ih =>
    intro h
    show prodBelow f T * f T ≤ prodBelow g T * g T
    exact Nat.le_trans
      (Nat.mul_le_mul_right (f T)
        (ih (fun t ht => h t (Nat.lt_succ_of_lt ht))))
      (Nat.mul_le_mul_left (prodBelow g T) (h T (Nat.lt_succ_self T)))

theorem prodBelow_congr {f g : Nat → Nat} :
    ∀ T : Nat, (∀ t, t < T → f t = g t) →
      prodBelow f T = prodBelow g T := by
  intro T
  induction T with
  | zero => intro _; rfl
  | succ T ih =>
    intro h
    show prodBelow f T * f T = prodBelow g T * g T
    rw [ih (fun t ht => h t (Nat.lt_succ_of_lt ht)),
        h T (Nat.lt_succ_self T)]

/-- **B1, the run (the freshness budget).** Over `T` ticks of injectively
dilated dynamics, the product of realized in-degrees is bounded by the
product of consumed record-alphabet sizes: `∏ K_t ≤ ∏ |E_t|`. Total
distinguishability loss is bounded by total fresh capacity consumed. -/
theorem budget_run [DecidableEq E'] (T : Nat)
    (G : Nat → X × E → S × E') (e0 : Nat → E) (s : Nat → S)
    (xs : Nat → List X) (Es : Nat → List E')
    (hinj : ∀ t, t < T → ∀ a b : X × E, G t a = G t b → a = b)
    (hd : ∀ t, t < T → Distinct (xs t))
    (hsys : ∀ t, t < T → ∀ x, x ∈ xs t → (G t (x, e0 t)).1 = s t)
    (halph : ∀ t, t < T → ∀ x, x ∈ xs t → (G t (x, e0 t)).2 ∈ Es t) :
    prodBelow (fun t => (xs t).length) T ≤
      prodBelow (fun t => (Es t).length) T :=
  prodBelow_mono T (fun t ht =>
    budget_tick (G t) (hinj t ht) (e0 t) (s t) (xs t) (hd t ht)
      (hsys t ht) (Es t) (halph t ht))

/-! ### B2: the equality case is saturation -/

/-- Membership introduction for `map`, axiom-free. -/
theorem mem_map_of_mem (f : α → β) {a : α} :
    ∀ {l : List α}, a ∈ l → f a ∈ l.map f := by
  intro l
  induction l with
  | nil => intro h; cases h
  | cons x xs ih =>
    intro h
    cases h with
    | head => exact mem_head (f a) (xs.map f)
    | tail _ h' => exact mem_tail (f x) (ih h')

/-- A pairwise-distinct list included in a no-longer list covers it: the
finite injection-surjection pivot, in list form. -/
theorem mem_of_distinct_incl_length_le [DecidableEq α] :
    ∀ (l m : List α), Distinct l → (∀ x, x ∈ l → x ∈ m) →
      m.length ≤ l.length → ∀ y, y ∈ m → y ∈ l := by
  intro l
  induction l with
  | nil =>
    intro m _ _ hlen y hy
    match m, hlen, hy with
    | [], _, hy => exact (nomatch hy)
    | z :: m', hlen, _ =>
      exact absurd hlen (Nat.not_le_of_gt (Nat.succ_pos m'.length))
  | cons x l' ih =>
    intro m hd hincl hlen y hy
    by_cases hyx : y = x
    · rw [hyx]; exact mem_head x l'
    · have hxm : x ∈ m := hincl x (mem_head x l')
      have hincl' : ∀ z, z ∈ l' → z ∈ remove x m := fun z hz =>
        mem_remove (hincl z (mem_tail x hz)) (fun hzx => hd.1 z hz hzx.symm)
      have hlen' : (remove x m).length ≤ l'.length := by
        have h1 := length_remove_of_mem hxm
        have h2 : m.length ≤ l'.length + 1 := hlen
        rw [← h1] at h2
        exact Nat.le_of_succ_le_succ h2
      exact mem_tail x (ih (remove x m) hd.2 hincl' hlen' y (mem_remove hy hyx))

/-- A tick is *saturated* when the records of its merged fiber exhaust
the record alphabet consumed that tick: the fiber → record map (injective
by Thm 3.2) is onto the declared alphabet. -/
def Saturated (G : X × E → S × E') (e0 : E) (xs : List X)
    (Es : List E') : Prop :=
  ∀ r, r ∈ Es → ∃ x, x ∈ xs ∧ (G (x, e0)).2 = r

/-- **B2 (equality iff saturation).** For an injectively dilated `K`-merge
with pairwise-distinct fiber and duplicate-free consumed alphabet:
`K_t = |E_t|` iff the tick is saturated. Distinguishability loss spends
the whole per-tick budget exactly when the records exhaust the fresh
alphabet. -/
theorem budget_tick_eq_iff [DecidableEq E'] (G : X × E → S × E')
    (hinj : ∀ a b : X × E, G a = G b → a = b) (e0 : E) (s : S)
    (xs : List X) (hd : Distinct xs)
    (hsys : ∀ x, x ∈ xs → (G (x, e0)).1 = s)
    (Es : List E') (hEs : Distinct Es)
    (halph : ∀ x, x ∈ xs → (G (x, e0)).2 ∈ Es) :
    xs.length = Es.length ↔ Saturated G e0 xs Es := by
  have hrd : Distinct (xs.map (fun x => (G (x, e0)).2)) :=
    env_records_distinct_list G hinj e0 s xs hd hsys
  have hrmem : ∀ y, y ∈ xs.map (fun x => (G (x, e0)).2) → y ∈ Es :=
    fun y hy =>
      match exists_of_mem_map hy with
      | ⟨z, hz, hzy⟩ => hzy ▸ halph z hz
  constructor
  · intro heq r hr
    have hlen : Es.length ≤ (xs.map (fun x => (G (x, e0)).2)).length := by
      rw [length_map_eq, heq]
      exact Nat.le_refl _
    have hcov := mem_of_distinct_incl_length_le _ Es hrd hrmem hlen r hr
    match exists_of_mem_map hcov with
    | ⟨x, hx, hxr⟩ => exact ⟨x, hx, hxr⟩
  · intro hsat
    have hle := budget_tick G hinj e0 s xs hd hsys Es halph
    have hEsub : ∀ r, r ∈ Es → r ∈ xs.map (fun x => (G (x, e0)).2) := by
      intro r hr
      match hsat r hr with
      | ⟨x, hx, hxr⟩ => exact hxr ▸ mem_map_of_mem (fun x => (G (x, e0)).2) hx
    have hge : Es.length ≤ xs.length := by
      have h := length_le_of_distinct_mem hEs hEsub
      rw [length_map_eq] at h
      exact h
    exact Nat.le_antisymm hle hge

/-- An everywhere-saturated run spends its whole budget:
`∏ K_t = ∏ |E_t|`. In the classical skeleton of the conveyor this is the
"loss = capacity" tick-identity. -/
theorem budget_run_eq_of_saturated [DecidableEq E'] (T : Nat)
    (G : Nat → X × E → S × E') (e0 : Nat → E) (s : Nat → S)
    (xs : Nat → List X) (Es : Nat → List E')
    (hinj : ∀ t, t < T → ∀ a b : X × E, G t a = G t b → a = b)
    (hd : ∀ t, t < T → Distinct (xs t))
    (hsys : ∀ t, t < T → ∀ x, x ∈ xs t → (G t (x, e0 t)).1 = s t)
    (hEs : ∀ t, t < T → Distinct (Es t))
    (halph : ∀ t, t < T → ∀ x, x ∈ xs t → (G t (x, e0 t)).2 ∈ Es t)
    (hsat : ∀ t, t < T → Saturated (G t) (e0 t) (xs t) (Es t)) :
    prodBelow (fun t => (xs t).length) T =
      prodBelow (fun t => (Es t).length) T :=
  prodBelow_congr T (fun t ht =>
    (budget_tick_eq_iff (G t) (hinj t ht) (e0 t) (s t) (xs t) (hd t ht)
      (hsys t ht) (Es t) (hEs t ht) (halph t ht)).mpr (hsat t ht))

/-!
# Obs.Budget

Freshness budget: per-tick and run-level product bounds, saturation
conditions, Dirac embedding into the counting second law.
-/

section Deterministic

variable {Q : Type} [Add Q] [Mul Q] [OfNat Q 0] [OfNat Q 1] [DecidableEq Q]
variable {RL : Type}

/-- Iterated composition of the deterministic tick. -/
def iter (φ : RL → RL) : Nat → RL → RL
  | 0, r => r
  | n + 1, r => φ (iter φ n r)

/-- The Dirac law at a readout value. -/
def dirac [DecidableEq RL] (v : RL) : RL → Q :=
  fun r => if r = v then 1 else 0

/-- The Dirac (deterministic) kernel of `φ`. -/
def diracKernel [DecidableEq RL] (φ : RL → RL) : RL → RL → Q :=
  fun r r' => if r' = φ r then 1 else 0

/-- The Dirac laws of a deterministic readout dynamics satisfy the
autonomous-step hypothesis of the counting second law: one garbling step
by the Dirac kernel advances the iterate. Semiring facts (`h1`, `h0`) and
multiplicity-one evaluation of the declared readout list (`hone`) are
explicit hypotheses; `hall` enumerates the readout by the list. -/
theorem dirac_autonomous [DecidableEq RL] (RLs : List RL) (φ : RL → RL)
    (h1 : ∀ a : Q, 1 * a = a) (h0 : ∀ a : Q, 0 * a = 0)
    (hone : ∀ v : RL, v ∈ RLs → ∀ f : RL → Q,
      lsum RLs (fun r => if r = v then f r else 0) = f v)
    (hall : ∀ r : RL, r ∈ RLs) :
    ∀ (c : RL) (n : Nat), ∀ r', r' ∈ RLs →
      dirac (Q := Q) (iter φ (n + 1) c) r' =
        garble RLs (dirac (iter φ n c)) (diracKernel φ) r' := by
  intro c n r' _
  show (if r' = φ (iter φ n c) then (1 : Q) else 0) =
    lsum RLs (fun r => (if r = iter φ n c then (1 : Q) else 0) *
      (if r' = φ r then (1 : Q) else 0))
  have hterm : ∀ r, r ∈ RLs →
      (if r = iter φ n c then (1 : Q) else 0) *
        (if r' = φ r then (1 : Q) else 0) =
      (if r = iter φ n c then
        (if r' = φ r then (1 : Q) else 0) else 0) := by
    intro r _
    by_cases h : r = iter φ n c
    · rw [if_pos h, if_pos h, h1]
    · rw [if_neg h, if_neg h, h0]
  rw [lsum_congr hterm,
      hone (iter φ n c) (hall _) (fun r => if r' = φ r then (1 : Q) else 0)]

/-- Deterministic counting arrow: iterate-equality classes are antitone in
the horizon (merging never splits). -/
theorem iter_classes_antitone {RL : Type} [DecidableEq RL]
    (φ : RL → RL) (Cs : List RL) (n : Nat) :
    countClasses (fun c c' => iter φ (n + 1) c = iter φ (n + 1) c') Cs ≤
      countClasses (fun c c' => iter φ n c = iter φ n c') Cs :=
  countClasses_le_of_imp (fun _ _ h => congrArg φ h) Cs

end Deterministic

end Obs.Budget

-- #print axioms
#print axioms Obs.Budget.budget_tick
#print axioms Obs.Budget.prodBelow_mono
#print axioms Obs.Budget.prodBelow_congr
#print axioms Obs.Budget.budget_run
#print axioms Obs.Budget.mem_map_of_mem
#print axioms Obs.Budget.mem_of_distinct_incl_length_le
#print axioms Obs.Budget.budget_tick_eq_iff
#print axioms Obs.Budget.budget_run_eq_of_saturated
#print axioms Obs.Budget.dirac_autonomous
#print axioms Obs.Budget.iter_classes_antitone

