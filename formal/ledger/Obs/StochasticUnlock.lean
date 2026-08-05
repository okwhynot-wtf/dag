/-!
# Obs.StochasticUnlock

Stochastic unlock: class-count second law, purity / Tsallis-2 forms,
Blackwell layer, alphabet bounds under dilation.
-/

set_option linter.unusedSectionVars false

namespace Obs.StochasticUnlock

variable {Q : Type} [Add Q] [Mul Q] [OfNat Q 0] [DecidableEq Q]
variable {R RL RU X C : Type}

/-- Constructor-level membership helpers, List membership helpers. -/
theorem mem_head (a : α) (l : List α) : a ∈ a :: l := List.Mem.head l
theorem mem_tail (b : α) {a : α} {l : List α} (h : a ∈ l) : a ∈ b :: l :=
  List.Mem.tail b h

/-- Sum of a `Q`-valued function over a list. -/
def lsum : List α → (α → Q) → Q
  | [],      _ => 0
  | x :: xs, f => f x + lsum xs f

/-- Pointwise equality of two laws on a declared list of readout values. -/
def EqOn (l : List R) (f g : R → Q) : Prop :=
  ∀ r, r ∈ l → f r = g r

instance (l : List R) (f g : R → Q) : Decidable (EqOn l f g) :=
  List.decidableBAll (fun r => f r = g r) l

theorem lsum_congr {l : List α} {f g : α → Q}
    (h : ∀ x, x ∈ l → f x = g x) : lsum l f = lsum l g := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    show f x + lsum xs f = g x + lsum xs g
    rw [h x (mem_head x xs),
        ih (fun y hy => h y (mem_tail x hy))]

/-- Negated bounded-forall over a list pushes to a bounded-exists, using
decidability of the pointwise predicate (no classical axioms). -/
theorem exists_mem_not_of_not_ball {l : List R} {f g : R → Q}
    (h : ¬ EqOn l f g) : ∃ r, r ∈ l ∧ f r ≠ g r := by
  induction l with
  | nil =>
    exact absurd (fun r hr => nomatch hr) h
  | cons x xs ih =>
    by_cases hx : f x = g x
    · have hxs : ¬ EqOn xs f g := by
        intro hall
        apply h
        intro r hr
        cases hr with
        | head => exact hx
        | tail _ hmem => exact hall r hmem
      match ih hxs with
      | ⟨r, hr, hne⟩ => exact ⟨r, mem_tail x hr, hne⟩
    · exact ⟨x, mem_head x xs, hx⟩

/-- A channel `h : RL → RU → Q` applied to a law on the locked readout: the
garbled law on the probe readout. Linearity is built into the formula. -/
def garble (RLs : List RL) (law : RL → Q) (h : RL → RU → Q) : RU → Q :=
  fun r' => lsum RLs (fun r => law r * h r r')

/-- Channels map laws that agree on the declared values to equal garbled
laws: the one-line linearity fact behind the access price. -/
theorem garble_congr (RLs : List RL) {l₁ l₂ : RL → Q}
    (he : EqOn RLs l₁ l₂) (h : RL → RU → Q) :
    ∀ r', garble RLs l₁ h r' = garble RLs l₂ h r' := by
  intro r'
  exact lsum_congr (fun r hr => by
    show l₁ r * h r r' = l₂ r * h r r'
    rw [he r hr])

/-! ## The access price (Theorem S4)

If the locked laws of the pair agree at the witnessing horizon and the probe
laws differ there, no channel garbles the locked law into the probe law on
the pair: the stochastic strengthening of the deterministic
`no_postprocessing_of_separating`, with any stochastic post-processing (not
merely any function) as the impossible object. -/

theorem access_price {RLs : List RL} {RUs : List RU}
    {lock₁ lock₂ : RL → Q} {probe₁ probe₂ : RU → Q}
    (hmerge : EqOn RLs lock₁ lock₂)
    (hsep : ∃ r', r' ∈ RUs ∧ probe₁ r' ≠ probe₂ r') :
    ¬ ∃ h : RL → RU → Q,
        (∀ r', r' ∈ RUs → probe₁ r' = garble RLs lock₁ h r') ∧
        (∀ r', r' ∈ RUs → probe₂ r' = garble RLs lock₂ h r') := by
  intro hex
  match hex, hsep with
  | ⟨h, h₁, h₂⟩, ⟨r', hr', hne⟩ =>
    apply hne
    rw [h₁ r' hr', h₂ r' hr']
    exact garble_congr RLs hmerge h r'

/-! ## The autonomy price, state level (Theorem S5)

A strong-lumpability violation pair -- two states with the same locked
readout whose rows push forward to different laws -- certifies that no
quotient kernel `g` on readout values reproduces every row's pushforward. -/

theorem autonomy_price (RLs : List RL)
    (rowLaw : X → RL → Q) (rdL : X → RL)
    {x y : X} (hclass : rdL x = rdL y)
    (hviol : ¬ EqOn RLs (rowLaw x) (rowLaw y)) :
    ¬ ∃ g : RL → RL → Q, ∀ z, EqOn RLs (rowLaw z) (g (rdL z)) := by
  intro hex
  match hex with
  | ⟨g, hg⟩ =>
    apply hviol
    intro r hr
    rw [hg x r hr, hclass, ← hg y r hr]

/-! ## The autonomy price, law level

If the locked laws agree at some horizon and differ at the next, no readout
kernel can drive the locked marginal as an autonomous first-order law: a
kernel is a channel, and channels preserve agreement. This is the form the
master theorem consumes, and it is exactly what a crossing step certifies. -/

theorem marginal_autonomy_price (RLs : List RL)
    {law₁ law₂ : Nat → RL → Q} {s : Nat}
    (hs : EqOn RLs (law₁ s) (law₂ s))
    (hbreak : ∃ r, r ∈ RLs ∧ law₁ (s+1) r ≠ law₂ (s+1) r) :
    ¬ ∃ g : RL → RL → Q,
        (∀ n, ∀ r, r ∈ RLs → law₁ (n+1) r = garble RLs (law₁ n) g r) ∧
        (∀ n, ∀ r, r ∈ RLs → law₂ (n+1) r = garble RLs (law₂ n) g r) := by
  intro hex
  match hex, hbreak with
  | ⟨g, h₁, h₂⟩, ⟨r, hr, hne⟩ =>
    apply hne
    rw [h₁ s r hr, h₂ s r hr]
    exact garble_congr RLs hs g r

/-! ## Soundness (Theorem S1)

Under an autonomous marginal law, a pair merged at imprint is merged at
every horizon (`merged_forever`). -/

theorem merged_forever (RLs : List RL)
    {law₁ law₂ : Nat → RL → Q} (g : RL → RL → Q)
    (hstep₁ : ∀ n, ∀ r, r ∈ RLs → law₁ (n+1) r = garble RLs (law₁ n) g r)
    (hstep₂ : ∀ n, ∀ r, r ∈ RLs → law₂ (n+1) r = garble RLs (law₂ n) g r)
    (h0 : EqOn RLs (law₁ 0) (law₂ 0)) :
    ∀ t, EqOn RLs (law₁ t) (law₂ t) := by
  intro t
  induction t with
  | zero => exact h0
  | succ n ih =>
    intro r hr
    rw [hstep₁ n r hr, hstep₂ n r hr]
    exact garble_congr RLs ih g r

/-! ## Crossing (Theorem S2) and trichotomy (Theorem S3)

Stated over an abstract time-indexed merge predicate with decidable stages,
in the stochastic instantiation
`mergedL t := EqOn RLs (lockedLaw₁ t) (lockedLaw₂ t)`, decidable by the
instance above. Decidability replaces classical choice throughout. -/

theorem crossing (mergedL : Nat → Prop) [DecidablePred mergedL]
    (h0 : mergedL 0) :
    ∀ t, ¬ mergedL t → ∃ s, s < t ∧ mergedL s ∧ ¬ mergedL (s+1) := by
  intro t
  induction t with
  | zero => intro h; exact absurd h0 h
  | succ n ih =>
    intro h
    by_cases hn : mergedL n
    · exact ⟨n, Nat.lt_succ_self n, hn, h⟩
    · match ih hn with
      | ⟨s, hs, hm, hnm⟩ =>
        exact ⟨s, Nat.lt_trans hs (Nat.lt_succ_self n), hm, hnm⟩

/-- Unlock trichotomy: every witness time `t` against a pair merged at
imprint lands in exactly one of U1 (`t = 0`), U2 (`t > 0`, locked cut
separates at `t`, with an extracted crossing step), or U3 (`t > 0`, locked
cut still merged at `t`). -/
theorem unlock_trichotomy (mergedL : Nat → Prop) [DecidablePred mergedL]
    (h0 : mergedL 0) (t : Nat) :
    (t = 0)
    ∨ (0 < t ∧ ¬ mergedL t ∧ ∃ s, s < t ∧ mergedL s ∧ ¬ mergedL (s+1))
    ∨ (0 < t ∧ mergedL t) := by
  match t with
  | 0 => exact Or.inl rfl
  | Nat.succ n =>
    by_cases hm : mergedL (n+1)
    · exact Or.inr (Or.inr ⟨Nat.succ_pos n, hm⟩)
    · exact Or.inr (Or.inl ⟨Nat.succ_pos n, hm, crossing mergedL h0 (n+1) hm⟩)

/-- The three labels are pairwise exclusive. -/
theorem labels_exclusive (mergedL : Nat → Prop) (t : Nat) :
    (t = 0 → ¬ (0 < t))
    ∧ ((0 < t ∧ ¬ mergedL t) → ¬ (0 < t ∧ mergedL t)) := by
  constructor
  · intro h0 hpos
    rw [h0] at hpos
    exact Nat.lt_irrefl 0 hpos
  · intro h1 h2
    exact h1.2 h2.2

/-! ## The master theorem (Theorem S6): access or autonomy

Every unlock witness pays. The locked merge predicate is instantiated
concretely as law agreement; the case split is on its decidable stage at the
witnessing horizon. If the locked laws still agree at `t`, the probe's
separation triggers the access price; if they disagree, the crossing step
triggers the law-level autonomy price. -/

theorem access_or_autonomy (RLs : List RL) (RUs : List RU)
    (lockedLaw₁ lockedLaw₂ : Nat → RL → Q)
    (probeLaw₁ probeLaw₂ : Nat → RU → Q)
    (h0 : EqOn RLs (lockedLaw₁ 0) (lockedLaw₂ 0))
    (t : Nat)
    (hwit : ∃ r', r' ∈ RUs ∧ probeLaw₁ t r' ≠ probeLaw₂ t r') :
    (¬ ∃ h : RL → RU → Q,
        (∀ r', r' ∈ RUs → probeLaw₁ t r' = garble RLs (lockedLaw₁ t) h r') ∧
        (∀ r', r' ∈ RUs → probeLaw₂ t r' = garble RLs (lockedLaw₂ t) h r'))
    ∨ (¬ ∃ g : RL → RL → Q,
        (∀ n, ∀ r, r ∈ RLs →
            lockedLaw₁ (n+1) r = garble RLs (lockedLaw₁ n) g r) ∧
        (∀ n, ∀ r, r ∈ RLs →
            lockedLaw₂ (n+1) r = garble RLs (lockedLaw₂ n) g r)) := by
  by_cases hm : EqOn RLs (lockedLaw₁ t) (lockedLaw₂ t)
  · exact Or.inl (access_price hm hwit)
  · match crossing (fun n => EqOn RLs (lockedLaw₁ n) (lockedLaw₂ n)) h0 t hm with
    | ⟨s, _, hms, hbreak⟩ =>
      exact Or.inr
        (marginal_autonomy_price RLs hms (exists_mem_not_of_not_ball hbreak))

/-! ## Blackwell layer

Experiments are content-indexed laws. A channel garbling the locked
experiment into the probe experiment on a content list transports law
agreement content-by-content; a probe separating any merged pair is not in
the garbling downset of the locked experiment on any ensemble containing
the pair. -/

/-- Garbling refines merging: a probe in the garbling downset of the locked
experiment separates nothing the locked experiment merges. Free probes are
post-processing. -/
theorem garbling_refines_merging (RLs : List RL) (RUs : List RU)
    (lawL : C → RL → Q) (lawU : C → RU → Q) (Cs : List C) (h : RL → RU → Q)
    (hg : ∀ c, c ∈ Cs → ∀ r', r' ∈ RUs → lawU c r' = garble RLs (lawL c) h r')
    {c₁ c₂ : C} (h₁ : c₁ ∈ Cs) (h₂ : c₂ ∈ Cs)
    (hm : EqOn RLs (lawL c₁) (lawL c₂)) :
    EqOn RUs (lawU c₁) (lawU c₂) := by
  intro r' hr'
  rw [hg c₁ h₁ r' hr', hg c₂ h₂ r' hr']
  exact garble_congr RLs hm h r'

/-- Ensemble access price: a probe that separates a merged pair is not a
garbling of the locked experiment on any content ensemble containing the
pair -- the whole-ensemble strengthening of `access_price`. -/
theorem ensemble_access_price (RLs : List RL) (RUs : List RU)
    (lawL : C → RL → Q) (lawU : C → RU → Q) (Cs : List C)
    {c₁ c₂ : C} (h₁ : c₁ ∈ Cs) (h₂ : c₂ ∈ Cs)
    (hm : EqOn RLs (lawL c₁) (lawL c₂))
    (hsep : ∃ r', r' ∈ RUs ∧ lawU c₁ r' ≠ lawU c₂ r') :
    ¬ ∃ h : RL → RU → Q,
        ∀ c, c ∈ Cs → ∀ r', r' ∈ RUs →
          lawU c r' = garble RLs (lawL c) h r' := by
  intro hex
  match hex, hsep with
  | ⟨h, hg⟩, ⟨r', hr', hne⟩ =>
    exact hne
      (garbling_refines_merging RLs RUs lawL lawU Cs h hg h₁ h₂ hm r' hr')

/-! ## Counting form of the alphabet bound

An injective dilation of a merge writes pairwise-distinct environment
records for the merged states: the environment alphabet is at least the
merge in-degree (counting form of the ln K capacity bound). -/

/-- Pair extensionality, prelude-safe. -/
theorem pair_ext {α β : Type} {p q : α × β}
    (h1 : p.1 = q.1) (h2 : p.2 = q.2) : p = q := by
  match p, q with
  | (a, b), (c, d) =>
    cases h1
    cases h2
    rfl

/-- Merged states force distinct environment records under any injective
dilation: the ln K bound in counting form. -/
theorem env_records_distinct {X E S E' : Type} (G : X × E → S × E')
    (hinj : ∀ a b : X × E, G a = G b → a = b) (e0 : E)
    {x y : X} (hxy : x ≠ y)
    (hsys : (G (x, e0)).1 = (G (y, e0)).1) :
    (G (x, e0)).2 ≠ (G (y, e0)).2 := by
  intro henv
  apply hxy
  have h := hinj (x, e0) (y, e0) (pair_ext hsys henv)
  exact congrArg Prod.fst h

/-! ## Second law (counting form)

Distinguishability class count as a Lyapunov function on content ensembles
(laws compared by `EqOn` at declared readout values):

* **Arrow** (`second_law_arrow`): under any autonomous stochastic law the
  class count never increases.
* **Strict arrow** (`second_law_strict`): at a merge (separated at `n`,
  merged at `n+1`) the count strictly drops.
* **No revival**: merged stays merged (`merged_forever`); an autonomous
  increase is impossible (`marginal_autonomy_price`).
* **Ledger** (`env_records_distinct_list`, `env_alphabet_ge_indegree`):
  an injective dilation of a K-fold merge writes K pairwise-distinct
  environment records, so the environment alphabet is at least K. -/

/-- Number of distinguishability classes represented in a list: an element
scores iff nothing later in the list is equivalent to it (count of last
representatives; equals the class count for equivalence relations). -/
def countClasses (eqv : α → α → Prop) [DecidableRel eqv] : List α → Nat
  | [] => 0
  | x :: xs => (if ∃ y ∈ xs, eqv x y then 0 else 1) + countClasses eqv xs

/-- Coarsening monotonicity: a relation with more identifications has no
more classes. -/
theorem countClasses_le_of_imp {eqv eqv' : α → α → Prop}
    [DecidableRel eqv] [DecidableRel eqv']
    (h : ∀ a b, eqv a b → eqv' a b) (l : List α) :
    countClasses eqv' l ≤ countClasses eqv l := by
  induction l with
  | nil => exact Nat.le_refl 0
  | cons x xs ih =>
    show (if ∃ y ∈ xs, eqv' x y then 0 else 1) + countClasses eqv' xs ≤
         (if ∃ y ∈ xs, eqv x y then 0 else 1) + countClasses eqv xs
    by_cases hx : ∃ y ∈ xs, eqv x y
    · have hx' : ∃ y ∈ xs, eqv' x y :=
        match hx with
        | ⟨y, hy, he⟩ => ⟨y, hy, h x y he⟩
      rw [if_pos hx, if_pos hx']
      exact Nat.add_le_add_left ih 0
    · rw [if_neg hx]
      by_cases hx' : ∃ y ∈ xs, eqv' x y
      · rw [if_pos hx', Nat.zero_add]
        exact Nat.le_trans ih (Nat.le_add_left _ 1)
      · rw [if_neg hx']
        exact Nat.add_le_add_left ih 1

/-- Helper for the strict law: a fresh identification between the head and
a tail element strictly reduces the class count. -/
theorem countClasses_lt_head_witness {eqv eqv' : α → α → Prop}
    [DecidableRel eqv] [DecidableRel eqv']
    (himp : ∀ a b, eqv a b → eqv' a b)
    (htrans : ∀ a b c, eqv a b → eqv b c → eqv a c)
    (hsymm' : ∀ a b, eqv' a b → eqv' b a)
    (htrans' : ∀ a b c, eqv' a b → eqv' b c → eqv' a c)
    {x b : α} {xs : List α} (hb : b ∈ xs)
    (hab' : eqv' x b) (hnab : ¬ eqv x b)
    (ih : (∃ a, a ∈ xs ∧ ∃ b, b ∈ xs ∧ eqv' a b ∧ ¬ eqv a b) →
          countClasses eqv' xs < countClasses eqv xs) :
    countClasses eqv' (x :: xs) < countClasses eqv (x :: xs) := by
  show (if ∃ y ∈ xs, eqv' x y then 0 else 1) + countClasses eqv' xs <
       (if ∃ y ∈ xs, eqv x y then 0 else 1) + countClasses eqv xs
  by_cases hy : ∃ y ∈ xs, eqv x y
  · match hy with
    | ⟨y, hyx, hexy⟩ =>
      have hyb' : eqv' y b := htrans' y x b (hsymm' x y (himp x y hexy)) hab'
      have hnyb : ¬ eqv y b := fun h => hnab (htrans x y b hexy h)
      have hlt := ih ⟨y, hyx, b, hb, hyb', hnyb⟩
      rw [if_pos hy, if_pos ⟨y, hyx, himp x y hexy⟩,
          Nat.zero_add, Nat.zero_add]
      exact hlt
  · rw [if_neg hy, if_pos ⟨b, hb, hab'⟩, Nat.zero_add, Nat.add_comm]
    exact Nat.lt_succ_of_le (countClasses_le_of_imp himp xs)

/-- Strict second law, abstract form: a coarsening that freshly identifies
two members of the ensemble strictly reduces the class count. Reflexivity,
symmetry, and transitivity are taken as hypotheses (all trivial for
`EqOn`); no classical axioms enter. -/
theorem countClasses_lt_of_strict_merge {eqv eqv' : α → α → Prop}
    [DecidableRel eqv] [DecidableRel eqv']
    (hrefl : ∀ a, eqv a a)
    (hsymm : ∀ a b, eqv a b → eqv b a)
    (htrans : ∀ a b c, eqv a b → eqv b c → eqv a c)
    (himp : ∀ a b, eqv a b → eqv' a b)
    (hsymm' : ∀ a b, eqv' a b → eqv' b a)
    (htrans' : ∀ a b c, eqv' a b → eqv' b c → eqv' a c) :
    ∀ l : List α, (∃ a, a ∈ l ∧ ∃ b, b ∈ l ∧ eqv' a b ∧ ¬ eqv a b) →
      countClasses eqv' l < countClasses eqv l := by
  intro l
  induction l with
  | nil =>
    intro hw
    match hw with
    | ⟨a, ha, _⟩ => cases ha
  | cons x xs ih =>
    intro hw
    match hw with
    | ⟨a, ha, b, hb, hab', hnab⟩ =>
      cases ha with
      | head =>
        cases hb with
        | head => exact absurd (hrefl x) hnab
        | tail _ hbx =>
          exact countClasses_lt_head_witness himp htrans hsymm' htrans'
            hbx hab' hnab ih
      | tail _ hax =>
        cases hb with
        | head =>
          exact countClasses_lt_head_witness himp htrans hsymm' htrans'
            hax (hsymm' a x hab') (fun h => hnab (hsymm x a h)) ih
        | tail _ hbx =>
          have hlt := ih ⟨a, hax, b, hbx, hab', hnab⟩
          show (if ∃ y ∈ xs, eqv' x y then 0 else 1) + countClasses eqv' xs <
               (if ∃ y ∈ xs, eqv x y then 0 else 1) + countClasses eqv xs
          by_cases hy : ∃ y ∈ xs, eqv x y
          · have hy' : ∃ y ∈ xs, eqv' x y :=
              match hy with
              | ⟨y, hyx, he⟩ => ⟨y, hyx, himp x y he⟩
            rw [if_pos hy, if_pos hy', Nat.zero_add, Nat.zero_add]
            exact hlt
          · rw [if_neg hy]
            by_cases hy' : ∃ y ∈ xs, eqv' x y
            · rw [if_pos hy', Nat.zero_add, Nat.add_comm]
              exact Nat.lt_succ_of_le (Nat.le_of_lt hlt)
            · rw [if_neg hy']
              exact Nat.add_lt_add_left hlt 1

/-- A step-antitone sequence is antitone. -/
theorem antitone_of_step {u : Nat → Nat} (hstep : ∀ n, u (n+1) ≤ u n) :
    ∀ s t, s ≤ t → u t ≤ u s := by
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
    · exact Nat.le_trans (hstep n)
        (ih (Nat.le_of_lt_succ (Nat.lt_of_le_of_ne hst h)))

/-- Law equality at a horizon is a decidable relation on contents. -/
instance lawEqvDecidable (RLs : List RL) (f : C → RL → Q) :
    DecidableRel (fun c₁ c₂ => EqOn RLs (f c₁) (f c₂)) :=
  fun c₁ c₂ => List.decidableBAll (fun r => f c₁ r = f c₂ r) RLs

/-- Distinguishability classes of a content ensemble at horizon `n`. -/
def lawClasses (RLs : List RL) (law : Nat → C → RL → Q) (n : Nat)
    (Cs : List C) : Nat :=
  countClasses (fun c₁ c₂ => EqOn RLs (law n c₁) (law n c₂)) Cs

/-- One-step transport: an autonomous step carries law agreement at `n` to
law agreement at `n+1` (garble_congr, pointwise on contents). -/
theorem law_agree_step (RLs : List RL) {law : Nat → C → RL → Q}
    {g : RL → RL → Q}
    (hstep : ∀ c n, ∀ r, r ∈ RLs → law (n+1) c r = garble RLs (law n c) g r)
    (n : Nat) {c₁ c₂ : C} (h : EqOn RLs (law n c₁) (law n c₂)) :
    EqOn RLs (law (n+1) c₁) (law (n+1) c₂) := by
  intro r hr
  rw [hstep c₁ n r hr, hstep c₂ n r hr]
  exact garble_congr RLs h g r

/-- **The second law, arrow clause.** Under an autonomous stochastic law,
the number of distinguishability classes of any content ensemble is
antitone in time. -/
theorem second_law_arrow (RLs : List RL) (law : Nat → C → RL → Q)
    (g : RL → RL → Q)
    (hstep : ∀ c n, ∀ r, r ∈ RLs → law (n+1) c r = garble RLs (law n c) g r)
    (Cs : List C) :
    ∀ s t, s ≤ t → lawClasses RLs law t Cs ≤ lawClasses RLs law s Cs :=
  antitone_of_step (fun n =>
    countClasses_le_of_imp
      (fun _ _ h => law_agree_step RLs hstep n h) Cs)

/-- **The second law, strict clause.** A merge event -- a pair of ensemble
contents separated at `n` and merged at `n+1` -- strictly reduces the class
count. -/
theorem second_law_strict (RLs : List RL) (law : Nat → C → RL → Q)
    (g : RL → RL → Q)
    (hstep : ∀ c n, ∀ r, r ∈ RLs → law (n+1) c r = garble RLs (law n c) g r)
    (Cs : List C) {c₁ c₂ : C} (h₁ : c₁ ∈ Cs) (h₂ : c₂ ∈ Cs) (n : Nat)
    (hsep : ¬ EqOn RLs (law n c₁) (law n c₂))
    (hmerge : EqOn RLs (law (n+1) c₁) (law (n+1) c₂)) :
    lawClasses RLs law (n+1) Cs < lawClasses RLs law n Cs :=
  countClasses_lt_of_strict_merge
    (eqv := fun c₁ c₂ => EqOn RLs (law n c₁) (law n c₂))
    (eqv' := fun c₁ c₂ => EqOn RLs (law (n+1) c₁) (law (n+1) c₂))
    (fun _ _ _ => rfl)
    (fun _ _ h r hr => (h r hr).symm)
    (fun _ _ _ hab hbc r hr => Eq.trans (hab r hr) (hbc r hr))
    (fun _ _ h => law_agree_step RLs hstep n h)
    (fun _ _ h r hr => (h r hr).symm)
    (fun _ _ _ hab hbc r hr => Eq.trans (hab r hr) (hbc r hr))
    Cs ⟨c₁, h₁, c₂, h₂, hmerge, hsep⟩

/-! ### The ledger: distinct environment records -/

/-- Pairwise distinctness of a list. -/
def Distinct : List α → Prop
  | [] => True
  | x :: xs => (∀ y, y ∈ xs → x ≠ y) ∧ Distinct xs

/-- Removal of one occurrence (prelude-safe, no BEq). -/
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

/-- Membership elimination for `map`, axiom-free (core's `List.mem_map`
carries `propext`). -/
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

/-- K-fold merge, distinctness clause: pairwise-distinct states sent to one
system record by an injective dilation write pairwise-distinct environment
records — `env_records_distinct` iterated. -/
theorem env_records_distinct_list {X E S E' : Type} (G : X × E → S × E')
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

/-- **The second law, ledger clause.** Counting form of the ln K bound:
the environment alphabet of an injective dilation is at least the merge
in-degree. Distinguishability lost under `second_law_strict` is written
as pairwise-distinct environment records. -/
theorem env_alphabet_ge_indegree {X E S E' : Type} [DecidableEq E']
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

/-! ## Second law (quantitative form)

Collision probability (purity) `Σ_r p(r)²` contracts under every doubly
stochastic kernel, so the Tsallis-2-shaped counting functional `1 - Σp²` never decreases. The only
inequality input is two-point convexity of squares, `(a-b)² ≥ 0`. The
algebraic interface is the ordered bundle `EOR`. -/

section Quantitative

variable [OfNat Q 1] [LE Q]

/-- Ordered commutative-semiring fragment for the quantitative layer.
    `amgm2` is `(a-b)² ≥ 0` without subtraction; `halve` is order-halving. -/
class EOR (Q : Type) [Add Q] [Mul Q] [OfNat Q 0] [OfNat Q 1] [LE Q] : Prop where
  addA   : ∀ a b c : Q, a + b + c = a + (b + c)
  addC   : ∀ a b : Q, a + b = b + a
  zadd   : ∀ a : Q, 0 + a = a
  mulA   : ∀ a b c : Q, a * b * c = a * (b * c)
  mulC   : ∀ a b : Q, a * b = b * a
  mone   : ∀ a : Q, a * 1 = a
  mzero  : ∀ a : Q, a * 0 = 0
  zmul   : ∀ a : Q, 0 * a = 0
  distL  : ∀ a b c : Q, a * (b + c) = a * b + a * c
  distR  : ∀ a b c : Q, (a + b) * c = a * c + b * c
  lrefl  : ∀ a : Q, a ≤ a
  ltrans : ∀ {a b c : Q}, a ≤ b → b ≤ c → a ≤ c
  addle  : ∀ {a b c d : Q}, a ≤ b → c ≤ d → a + c ≤ b + d
  mulle  : ∀ {a b c : Q}, a ≤ b → 0 ≤ c → a * c ≤ b * c
  amgm2  : ∀ a b : Q, a * b + a * b ≤ a * a + b * b
  halve  : ∀ {a b : Q}, a + a ≤ b + b → a ≤ b

open EOR

variable [EOR Q]

theorem one_mul' (a : Q) : 1 * a = a := by rw [mulC]; exact mone a

theorem add_add_add_comm' (a b c d : Q) :
    (a + b) + (c + d) = (a + c) + (b + d) := by
  rw [addA a b (c + d), ← addA b c d, addC b c, addA c b d, ← addA a c (b + d)]

theorem mul_mul_mul_comm' (a b c d : Q) :
    (a * b) * (c * d) = (a * c) * (b * d) := by
  rw [mulA a b (c * d), ← mulA b c d, mulC b c, mulA c b d, ← mulA a c (b * d)]

theorem lsum_add_eor (l : List α) (f g : α → Q) :
    lsum l (fun x => f x + g x) = lsum l f + lsum l g := by
  induction l with
  | nil => exact (zadd 0).symm
  | cons x xs ih =>
    show (f x + g x) + lsum xs (fun x => f x + g x) =
         (f x + lsum xs f) + (g x + lsum xs g)
    rw [ih, add_add_add_comm']

theorem lsum_zero_eor (l : List α) : lsum l (fun _ => (0 : Q)) = 0 := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    show 0 + lsum xs (fun _ => (0 : Q)) = 0
    rw [ih, zadd]

theorem mul_lsum (a : Q) (l : List α) (f : α → Q) :
    a * lsum l f = lsum l (fun x => a * f x) := by
  induction l with
  | nil => exact mzero a
  | cons x xs ih =>
    show a * (f x + lsum xs f) = a * f x + lsum xs (fun x => a * f x)
    rw [distL, ih]

theorem lsum_mul (a : Q) (l : List α) (f : α → Q) :
    lsum l f * a = lsum l (fun x => f x * a) := by
  induction l with
  | nil => exact zmul a
  | cons x xs ih =>
    show (f x + lsum xs f) * a = f x * a + lsum xs (fun x => f x * a)
    rw [distR, ih]

theorem lsum_swap_eor (l : List α) (m : List β) (F : α → β → Q) :
    lsum l (fun x => lsum m (fun y => F x y)) =
    lsum m (fun y => lsum l (fun x => F x y)) := by
  induction l with
  | nil => exact (lsum_zero_eor m).symm
  | cons x xs ih =>
    show lsum m (fun y => F x y) + lsum xs (fun x => lsum m (fun y => F x y)) =
         lsum m (fun y => F x y + lsum xs (fun x => F x y))
    rw [lsum_add_eor m (fun y => F x y) (fun y => lsum xs (fun x => F x y)), ih]

theorem lsum_le_lsum_eor {l : List α} {f g : α → Q}
    (h : ∀ x, x ∈ l → f x ≤ g x) : lsum l f ≤ lsum l g := by
  induction l with
  | nil => exact lrefl 0
  | cons x xs ih =>
    exact addle (h x (mem_head x xs)) (ih (fun y hy => h y (mem_tail x hy)))

theorem lsum_nonneg_eor {l : List α} {f : α → Q}
    (h : ∀ x, x ∈ l → 0 ≤ f x) : 0 ≤ lsum l f := by
  have h0 := lsum_le_lsum_eor (l := l) (f := fun _ => (0 : Q)) (g := f)
    (fun x hx => h x hx)
  rw [lsum_zero_eor] at h0
  exact h0

theorem lsum_mul_lsum (l : List α) (m : List β) (f : α → Q) (h : β → Q) :
    lsum l f * lsum m h = lsum l (fun x => lsum m (fun y => f x * h y)) := by
  rw [lsum_mul (lsum m h) l f]
  exact lsum_congr (fun x _ => mul_lsum (f x) m h)


theorem mulnn {a b : Q} (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a * b := by
  have h := mulle ha hb
  rw [zmul] at h
  exact h

/-- Collision probability (purity): the quantitative Lyapunov function. -/
def purity (S : List RL) (p : RL → Q) : Q := lsum S (fun r => p r * p r)

/-- Row overlap of a kernel: `(g gᵀ) r s`. -/
def rowOverlap (S : List RL) (g : RL → RL → Q) (r s : RL) : Q :=
  lsum S (fun r' => g r r' * g s r')

theorem rowOverlap_nonneg (S : List RL) (g : RL → RL → Q)
    (hpos : ∀ r, r ∈ S → ∀ r', r' ∈ S → 0 ≤ g r r')
    {r s : RL} (hr : r ∈ S) (hs : s ∈ S) :
    0 ≤ rowOverlap S g r s :=
  lsum_nonneg_eor (fun r' hr' => mulnn (hpos r hr r' hr') (hpos s hs r' hr'))

theorem rowOverlap_row (S : List RL) (g : RL → RL → Q)
    (hrow : ∀ r, r ∈ S → lsum S (fun r' => g r r') = 1)
    (hcol : ∀ r', r' ∈ S → lsum S (fun r => g r r') = 1)
    {r : RL} (hr : r ∈ S) :
    lsum S (fun s => rowOverlap S g r s) = 1 := by
  have h1 : lsum S (fun s => rowOverlap S g r s) =
      lsum S (fun r' => lsum S (fun s => g r r' * g s r')) :=
    lsum_swap_eor S S (fun s r' => g r r' * g s r')
  rw [h1]
  have h2 : lsum S (fun r' => lsum S (fun s => g r r' * g s r')) =
      lsum S (fun r' => g r r') :=
    lsum_congr (fun r' hr' => by
      rw [← mul_lsum (g r r') S (fun s => g s r'), hcol r' hr', mone])
  rw [h2]
  exact hrow r hr

theorem rowOverlap_col (S : List RL) (g : RL → RL → Q)
    (hrow : ∀ r, r ∈ S → lsum S (fun r' => g r r') = 1)
    (hcol : ∀ r', r' ∈ S → lsum S (fun r => g r r') = 1)
    {s : RL} (hs : s ∈ S) :
    lsum S (fun r => rowOverlap S g r s) = 1 := by
  have h1 : lsum S (fun r => rowOverlap S g r s) =
      lsum S (fun r' => lsum S (fun r => g r r' * g s r')) :=
    lsum_swap_eor S S (fun r r' => g r r' * g s r')
  rw [h1]
  have h2 : lsum S (fun r' => lsum S (fun r => g r r' * g s r')) =
      lsum S (fun r' => g s r') :=
    lsum_congr (fun r' hr' => by
      rw [← lsum_mul (g s r') S (fun r => g r r'), hcol r' hr', one_mul'])
  rw [h2]
  exact hrow s hs

/-- **The quantitative second law, exact form.** Purity contracts under any
doubly stochastic kernel: convexity of squares (`amgm2`) is the only
inequality consumed. -/
theorem purity_garble_le (S : List RL) (p : RL → Q) (g : RL → RL → Q)
    (hpos : ∀ r, r ∈ S → ∀ r', r' ∈ S → 0 ≤ g r r')
    (hrow : ∀ r, r ∈ S → lsum S (fun r' => g r r') = 1)
    (hcol : ∀ r', r' ∈ S → lsum S (fun r => g r r') = 1) :
    purity S (garble S p g) ≤ purity S p := by
  -- Step 1: purity of the pushforward as a double sum against the overlap.
  have hexp : purity S (garble S p g) =
      lsum S (fun r => lsum S (fun s =>
        (p r * p s) * rowOverlap S g r s)) := by
    have e1 : purity S (garble S p g) =
        lsum S (fun r' => lsum S (fun r => lsum S (fun s =>
          (p r * p s) * (g r r' * g s r')))) :=
      lsum_congr (fun r' _ =>
        (lsum_mul_lsum S S (fun r => p r * g r r')
            (fun s => p s * g s r')).trans
          (lsum_congr (fun r _ => lsum_congr (fun s _ =>
            mul_mul_mul_comm' (p r) (g r r') (p s) (g s r')))))
    have e2 : lsum S (fun r' => lsum S (fun r => lsum S (fun s =>
          (p r * p s) * (g r r' * g s r')))) =
        lsum S (fun r => lsum S (fun r' => lsum S (fun s =>
          (p r * p s) * (g r r' * g s r')))) :=
      lsum_swap_eor S S (fun r' r => lsum S (fun s =>
        (p r * p s) * (g r r' * g s r')))
    have e3 : lsum S (fun r => lsum S (fun r' => lsum S (fun s =>
          (p r * p s) * (g r r' * g s r')))) =
        lsum S (fun r => lsum S (fun s => lsum S (fun r' =>
          (p r * p s) * (g r r' * g s r')))) :=
      lsum_congr (fun r _ =>
        lsum_swap_eor S S (fun r' s => (p r * p s) * (g r r' * g s r')))
    have e4 : lsum S (fun r => lsum S (fun s => lsum S (fun r' =>
          (p r * p s) * (g r r' * g s r')))) =
        lsum S (fun r => lsum S (fun s =>
          (p r * p s) * rowOverlap S g r s)) :=
      lsum_congr (fun r _ => lsum_congr (fun s _ =>
        (mul_lsum (p r * p s) S (fun r' => g r r' * g s r')).symm))
    exact ((e1.trans e2).trans e3).trans e4
  -- Step 2: the doubled inequality.
  have hdouble :
      purity S (garble S p g) + purity S (garble S p g) ≤
      purity S p + purity S p := by
    rw [hexp]
    -- fold the doubled sum inward
    have hfold : lsum S (fun r => lsum S (fun s =>
          (p r * p s) * rowOverlap S g r s)) +
        lsum S (fun r => lsum S (fun s =>
          (p r * p s) * rowOverlap S g r s)) =
        lsum S (fun r => lsum S (fun s =>
          (p r * p s) * rowOverlap S g r s +
          (p r * p s) * rowOverlap S g r s)) := by
      rw [← lsum_add_eor S (fun r => lsum S (fun s =>
            (p r * p s) * rowOverlap S g r s))
          (fun r => lsum S (fun s => (p r * p s) * rowOverlap S g r s))]
      exact lsum_congr (fun r _ =>
        (lsum_add_eor S (fun s => (p r * p s) * rowOverlap S g r s)
          (fun s => (p r * p s) * rowOverlap S g r s)).symm)
    rw [hfold]
    -- termwise amgm2, then evaluate the two marginal sums
    have hterm : lsum S (fun r => lsum S (fun s =>
          (p r * p s) * rowOverlap S g r s +
          (p r * p s) * rowOverlap S g r s)) ≤
        lsum S (fun r => lsum S (fun s =>
          (p r * p r) * rowOverlap S g r s +
          (p s * p s) * rowOverlap S g r s)) :=
      lsum_le_lsum_eor (fun r hr => lsum_le_lsum_eor (fun s hs => by
        rw [← distR (p r * p s) (p r * p s) (rowOverlap S g r s),
            ← distR (p r * p r) (p s * p s) (rowOverlap S g r s)]
        exact mulle (amgm2 (p r) (p s))
          (rowOverlap_nonneg S g hpos hr hs)))
    have hsplit : lsum S (fun r => lsum S (fun s =>
          (p r * p r) * rowOverlap S g r s +
          (p s * p s) * rowOverlap S g r s)) =
        purity S p + purity S p := by
      have s1 : lsum S (fun r => lsum S (fun s =>
            (p r * p r) * rowOverlap S g r s +
            (p s * p s) * rowOverlap S g r s)) =
          lsum S (fun r => lsum S (fun s =>
            (p r * p r) * rowOverlap S g r s)) +
          lsum S (fun r => lsum S (fun s =>
            (p s * p s) * rowOverlap S g r s)) := by
        rw [← lsum_add_eor S
            (fun r => lsum S (fun s => (p r * p r) * rowOverlap S g r s))
            (fun r => lsum S (fun s => (p s * p s) * rowOverlap S g r s))]
        exact lsum_congr (fun r _ =>
          lsum_add_eor S (fun s => (p r * p r) * rowOverlap S g r s)
            (fun s => (p s * p s) * rowOverlap S g r s))
      have s2 : lsum S (fun r => lsum S (fun s =>
            (p r * p r) * rowOverlap S g r s)) = purity S p :=
        lsum_congr (fun r hr => by
          rw [← mul_lsum (p r * p r) S (fun s => rowOverlap S g r s),
              rowOverlap_row S g hrow hcol hr, mone])
      have s3 : lsum S (fun r => lsum S (fun s =>
            (p s * p s) * rowOverlap S g r s)) = purity S p := by
        have sw : lsum S (fun r => lsum S (fun s =>
              (p s * p s) * rowOverlap S g r s)) =
            lsum S (fun s => lsum S (fun r =>
              (p s * p s) * rowOverlap S g r s)) :=
          lsum_swap_eor S S (fun r s => (p s * p s) * rowOverlap S g r s)
        rw [sw]
        exact lsum_congr (fun s hs => by
          rw [← mul_lsum (p s * p s) S (fun r => rowOverlap S g r s),
              rowOverlap_col S g hrow hcol hs, mone])
      rw [s1, s2, s3]
    exact hsplit ▸ hterm
  exact halve hdouble

/-- A step-antitone `Q`-valued sequence is antitone (order interface only). -/
theorem antitone_of_step_le {u : Nat → Q} (hstep : ∀ n, u (n+1) ≤ u n) :
    ∀ s t, s ≤ t → u t ≤ u s := by
  intro s t
  induction t with
  | zero =>
    intro hst
    cases Nat.eq_zero_of_le_zero hst
    exact lrefl _
  | succ n ih =>
    intro hst
    by_cases h : s = n + 1
    · rw [h]
      exact lrefl _
    · exact ltrans (hstep n)
        (ih (Nat.le_of_lt_succ (Nat.lt_of_le_of_ne hst h)))

/-- **The second law, quantitative clause.** Under an autonomous doubly
stochastic law, purity is antitone over all horizons: the exact-arithmetic
H-theorem-shaped monotonicity, sharing its step hypothesis with the counting arrow. -/
theorem second_law_purity (S : List RL) (law : Nat → RL → Q)
    (g : RL → RL → Q)
    (hstep : ∀ n, ∀ r, r ∈ S → law (n+1) r = garble S (law n) g r)
    (hpos : ∀ r, r ∈ S → ∀ r', r' ∈ S → 0 ≤ g r r')
    (hrow : ∀ r, r ∈ S → lsum S (fun r' => g r r') = 1)
    (hcol : ∀ r', r' ∈ S → lsum S (fun r => g r r') = 1) :
    ∀ s t, s ≤ t → purity S (law t) ≤ purity S (law s) :=
  antitone_of_step_le (fun n => by
    have he : purity S (law (n+1)) = purity S (garble S (law n) g) :=
      lsum_congr (fun r hr => by rw [hstep n r hr])
    rw [he]
    exact purity_garble_le S (law n) g hpos hrow hcol)

/-- Tsallis-2-shaped counting functional `1 - Σp²` never decreases: the second law
read through any order-reversing subtraction (the hypothesis `hsub`,
trivially true at rationals). -/
theorem second_law_tsallis [Sub Q] (S : List RL) (law : Nat → RL → Q)
    (g : RL → RL → Q)
    (hsub : ∀ {a b : Q}, a ≤ b → (1 : Q) - b ≤ 1 - a)
    (hstep : ∀ n, ∀ r, r ∈ S → law (n+1) r = garble S (law n) g r)
    (hpos : ∀ r, r ∈ S → ∀ r', r' ∈ S → 0 ≤ g r r')
    (hrow : ∀ r, r ∈ S → lsum S (fun r' => g r r') = 1)
    (hcol : ∀ r', r' ∈ S → lsum S (fun r => g r r') = 1) :
    ∀ s t, s ≤ t →
      (1 : Q) - purity S (law s) ≤ 1 - purity S (law t) :=
  fun s t hst =>
    hsub (second_law_purity S law g hstep hpos hrow hcol s t hst)

end Quantitative

/-! ### Non-vacuity witness for the ordered layer

The quantitative second law (`purity_garble_le`, `second_law_purity`,
`second_law_tsallis`) uses the ordered bundle `EOR` (order, `amgm2`,
order-halving). `natEOR` exhibits a nondegenerate model: `Nat` with its
native order. -/

/-- Right distributivity on `Nat`, reproved from the axiom-free core facts
(`Nat.add_mul` may carry `propext`). -/
theorem nat_add_mul (a b c : Nat) : (a + b) * c = a * c + b * c := by
  rw [Nat.mul_comm (a + b) c, Nat.mul_add, Nat.mul_comm c a, Nat.mul_comm c b]

/-- Associativity of `Nat` multiplication, reproved axiom-free (this
`Nat.mul_assoc` may carry `propext`). -/
theorem nat_mul_assoc (a b : Nat) : ∀ c : Nat, a * b * c = a * (b * c) := by
  intro c
  induction c with
  | zero => rw [Nat.mul_zero, Nat.mul_zero, Nat.mul_zero]
  | succ n ih =>
    rw [Nat.mul_add (a * b) n 1, Nat.mul_add b n 1, Nat.mul_one, Nat.mul_one,
        Nat.mul_add a (b * n) b, ih]

/-- Two-point AM-GM on `Nat`, ordered case: for `a ≤ b`,
`2ab ≤ a² + b²` -- subtraction-free, via `b = a + k`. -/
theorem nat_amgm2_of_le {a b : Nat} (h : a ≤ b) :
    a * b + a * b ≤ a * a + b * b := by
  match Nat.le.dest h with
  | ⟨k, hk⟩ =>
    have hab : a * b = a * a + a * k := by
      rw [← hk, Nat.mul_add]
    have hbb : b * b = (a * a + a * k) + k * b := by
      calc b * b = (a + k) * b := by rw [hk]
        _ = a * b + k * b := nat_add_mul a k b
        _ = (a * a + a * k) + k * b := by rw [hab]
    have hak : a * k ≤ k * b := by
      rw [Nat.mul_comm a k]
      exact Nat.mul_le_mul_left k h
    calc a * b + a * b
        = (a * a + a * k) + (a * a + a * k) := by rw [hab]
      _ = (a * a + (a * a + a * k)) + a * k := by
          rw [Nat.add_assoc, Nat.add_comm (a * k) (a * a + a * k),
              ← Nat.add_assoc]
      _ ≤ (a * a + (a * a + a * k)) + k * b :=
          Nat.add_le_add_left hak _
      _ = a * a + b * b := by rw [Nat.add_assoc, ← hbb]

/-- **The ordered bundle is inhabited.** `Nat` satisfies every field of
`EOR` at an empty axiom footprint: the ordered layer of the second law is
not vacuous. -/
theorem natEOR : EOR Nat where
  addA := Nat.add_assoc
  addC := Nat.add_comm
  zadd := Nat.zero_add
  mulA := nat_mul_assoc
  mulC := Nat.mul_comm
  mone := Nat.mul_one
  mzero := Nat.mul_zero
  zmul := Nat.zero_mul
  distL := Nat.mul_add
  distR := nat_add_mul
  lrefl := Nat.le_refl
  ltrans := fun h1 h2 => Nat.le_trans h1 h2
  addle := fun h1 h2 => Nat.add_le_add h1 h2
  mulle := fun h _ => Nat.mul_le_mul_right _ h
  amgm2 := fun a b =>
    match Nat.le_total a b with
    | Or.inl h => nat_amgm2_of_le h
    | Or.inr h => by
        have h2 := nat_amgm2_of_le h
        rw [Nat.mul_comm b a] at h2
        rw [Nat.add_comm (b * b) (a * a)] at h2
        exact h2
  halve := fun {a b} h => by
    by_cases hab : a ≤ b
    · exact hab
    · have hba : b < a := Nat.gt_of_not_le hab
      have h2 : b + b < a + a := Nat.add_lt_add hba hba
      exact absurd h (Nat.not_le_of_gt h2)

end Obs.StochasticUnlock

-- #print axioms
#print axioms Obs.StochasticUnlock.exists_mem_not_of_not_ball
#print axioms Obs.StochasticUnlock.access_price
#print axioms Obs.StochasticUnlock.autonomy_price
#print axioms Obs.StochasticUnlock.marginal_autonomy_price
#print axioms Obs.StochasticUnlock.merged_forever
#print axioms Obs.StochasticUnlock.crossing
#print axioms Obs.StochasticUnlock.unlock_trichotomy
#print axioms Obs.StochasticUnlock.labels_exclusive
#print axioms Obs.StochasticUnlock.access_or_autonomy
#print axioms Obs.StochasticUnlock.garbling_refines_merging
#print axioms Obs.StochasticUnlock.ensemble_access_price
#print axioms Obs.StochasticUnlock.pair_ext
#print axioms Obs.StochasticUnlock.env_records_distinct
#print axioms Obs.StochasticUnlock.countClasses_le_of_imp
#print axioms Obs.StochasticUnlock.countClasses_lt_of_strict_merge
#print axioms Obs.StochasticUnlock.antitone_of_step
#print axioms Obs.StochasticUnlock.second_law_arrow
#print axioms Obs.StochasticUnlock.second_law_strict
#print axioms Obs.StochasticUnlock.length_le_of_distinct_mem
#print axioms Obs.StochasticUnlock.env_records_distinct_list
#print axioms Obs.StochasticUnlock.env_alphabet_ge_indegree
#print axioms Obs.StochasticUnlock.lsum_swap_eor
#print axioms Obs.StochasticUnlock.purity_garble_le
#print axioms Obs.StochasticUnlock.second_law_purity
#print axioms Obs.StochasticUnlock.second_law_tsallis
#print axioms Obs.StochasticUnlock.natEOR