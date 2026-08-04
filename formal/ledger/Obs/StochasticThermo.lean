import Obs.StochasticUnlock

/-!
# Obs.StochasticThermo

Total-variation data processing and Lyapunov forms for stochastic unlock.
-/

set_option linter.unusedSectionVars false

namespace Obs.StochasticUnlock

variable {Q : Type} [Add Q] [Mul Q] [Sub Q] [OfNat Q 0] [OfNat Q 1] [LE Q]
  [DecidableEq Q]
variable {R RL RU X C : Type}

/-- The ordered-ring hypothesis bundle: the sixteen facts about `Q` that the
quantitative second law consumes. -/
structure AbsData (Q : Type) [Add Q] [Mul Q] [Sub Q] [OfNat Q 0]
    [OfNat Q 1] [LE Q] where
  abs : Q → Q
  le_refl : ∀ a : Q, a ≤ a
  le_trans : ∀ a b c : Q, a ≤ b → b ≤ c → a ≤ c
  add_le_add : ∀ a b c d : Q, a ≤ b → c ≤ d → a + c ≤ b + d
  add_comm : ∀ a b : Q, a + b = b + a
  add_assoc : ∀ a b c : Q, (a + b) + c = a + (b + c)
  zero_add : ∀ a : Q, 0 + a = a
  mul_zero : ∀ a : Q, a * 0 = 0
  mul_one : ∀ a : Q, a * 1 = a
  mul_add : ∀ a b c : Q, a * (b + c) = a * b + a * c
  sub_mul : ∀ a b c : Q, (a - b) * c = a * c - b * c
  add_sub_add : ∀ a b c d : Q, (a + b) - (c + d) = (a - c) + (b - d)
  sub_self : ∀ a : Q, a - a = 0
  abs_zero : abs 0 = 0
  abs_add_le : ∀ a b : Q, abs (a + b) ≤ abs a + abs b
  abs_mul_nonneg : ∀ a b : Q, (0 : Q) ≤ b → abs (a * b) = abs a * b

/-! ### Summation calculus over `lsum` -/

theorem lsum_zero (D : AbsData Q) (l : List α) :
    lsum l (fun _ : α => (0 : Q)) = 0 := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    show (0 : Q) + lsum xs (fun _ => (0 : Q)) = 0
    rw [ih]
    exact D.zero_add 0

theorem add_add_add_comm (D : AbsData Q) (a b c d : Q) :
    (a + b) + (c + d) = (a + c) + (b + d) := by
  rw [D.add_assoc a b (c + d), ← D.add_assoc b c d, D.add_comm b c,
      D.add_assoc c b d, ← D.add_assoc a c (b + d)]

theorem lsum_add (D : AbsData Q) (l : List α) (f g : α → Q) :
    lsum l (fun a => f a + g a) = lsum l f + lsum l g := by
  induction l with
  | nil => exact (D.zero_add 0).symm
  | cons x xs ih =>
    show (f x + g x) + lsum xs (fun a => f a + g a) =
         (f x + lsum xs f) + (g x + lsum xs g)
    rw [ih]
    exact add_add_add_comm D (f x) (g x) (lsum xs f) (lsum xs g)

theorem lsum_sub (D : AbsData Q) (l : List α) (f g : α → Q) :
    lsum l (fun a => f a - g a) = lsum l f - lsum l g := by
  induction l with
  | nil =>
    show (0 : Q) = 0 - 0
    rw [D.sub_self 0]
  | cons x xs ih =>
    show (f x - g x) + lsum xs (fun a => f a - g a) =
         (f x + lsum xs f) - (g x + lsum xs g)
    rw [ih, D.add_sub_add]

theorem lsum_swap (D : AbsData Q) (l : List α) (m : List β) (f : α → β → Q) :
    lsum l (fun a => lsum m (f a)) =
    lsum m (fun b => lsum l (fun a => f a b)) := by
  induction l with
  | nil =>
    exact (lsum_zero D m).symm
  | cons x xs ih =>
    show lsum m (f x) + lsum xs (fun a => lsum m (f a)) =
         lsum m (fun b => f x b + lsum xs (fun a => f a b))
    rw [lsum_add D m (fun b => f x b) (fun b => lsum xs (fun a => f a b)), ih]

theorem lsum_mul_left (D : AbsData Q) (l : List α) (c : Q) (f : α → Q) :
    lsum l (fun a => c * f a) = c * lsum l f := by
  induction l with
  | nil => exact (D.mul_zero c).symm
  | cons x xs ih =>
    show c * f x + lsum xs (fun a => c * f a) = c * (f x + lsum xs f)
    rw [ih, D.mul_add]

theorem lsum_le_lsum (D : AbsData Q) (l : List α) {f g : α → Q}
    (h : ∀ x, x ∈ l → f x ≤ g x) : lsum l f ≤ lsum l g := by
  induction l with
  | nil => exact D.le_refl 0
  | cons x xs ih =>
    exact D.add_le_add _ _ _ _ (h x (mem_head x xs))
      (ih (fun y hy => h y (mem_tail x hy)))

/-- Triangle inequality for sums: the absolute value of a sum is bounded by
the sum of absolute values. -/
theorem abs_lsum_le (D : AbsData Q) (l : List α) (f : α → Q) :
    D.abs (lsum l f) ≤ lsum l (fun a => D.abs (f a)) := by
  induction l with
  | nil =>
    show D.abs 0 ≤ (0 : Q)
    rw [D.abs_zero]
    exact D.le_refl 0
  | cons x xs ih =>
    show D.abs (f x + lsum xs f) ≤ D.abs (f x) + lsum xs (fun a => D.abs (f a))
    exact D.le_trans _ _ _ (D.abs_add_le (f x) (lsum xs f))
      (D.add_le_add _ _ _ _ (D.le_refl (D.abs (f x))) ih)

/-! ### Total variation -/

/-- Total-variation distance between two laws on the declared readout
values (unnormalized: the sum of pointwise absolute differences). -/
def dTV (D : AbsData Q) (l : List R) (p q : R → Q) : Q :=
  lsum l (fun r => D.abs (p r - q r))

/-- Laws equal on the declared values sit at distance zero. -/
theorem dtv_zero_of_eqOn (D : AbsData Q) (l : List R) {p q : R → Q}
    (h : EqOn l p q) : dTV D l p q = 0 := by
  show lsum l (fun r => D.abs (p r - q r)) = 0
  rw [lsum_congr (fun r hr => by rw [h r hr, D.sub_self, D.abs_zero])]
  exact lsum_zero D l

/-! ### The data-processing inequality -/

/-- **The total-variation data-processing inequality (Theorem S7').**
Any stochastic channel -- nonnegative entries, rows summing to one on the
declared probe values -- contracts the total-variation distance between laws:
`||p g - q g|| <= ||p - q||`. This is the quantitative core of the second law
at zero axioms: an f-divergence DPI with `f(x) = |x - 1|`, no logarithm. -/
theorem tv_data_processing (D : AbsData Q) (RLs : List RL) (RUs : List RU)
    (g : RL → RU → Q)
    (hpos : ∀ r r', r ∈ RLs → r' ∈ RUs → (0 : Q) ≤ g r r')
    (hrow : ∀ r, r ∈ RLs → lsum RUs (fun r' => g r r') = 1)
    (p q : RL → Q) :
    dTV D RUs (garble RLs p g) (garble RLs q g) ≤ dTV D RLs p q := by
  -- Pointwise on each probe value: |Σ_r (p r - q r) g r r'| ≤ Σ_r |p r - q r| g r r'
  have key : ∀ r', r' ∈ RUs →
      D.abs (garble RLs p g r' - garble RLs q g r') ≤
      lsum RLs (fun r => D.abs (p r - q r) * g r r') := by
    intro r' hr'
    have h1 : garble RLs p g r' - garble RLs q g r' =
        lsum RLs (fun r => (p r - q r) * g r r') := by
      show lsum RLs (fun r => p r * g r r') -
           lsum RLs (fun r => q r * g r r') = _
      rw [← lsum_sub D RLs (fun r => p r * g r r') (fun r => q r * g r r')]
      exact lsum_congr (fun r _ => (D.sub_mul (p r) (q r) (g r r')).symm)
    have h2 := abs_lsum_le D RLs (fun r => (p r - q r) * g r r')
    have h3 : lsum RLs (fun r => D.abs ((p r - q r) * g r r')) =
        lsum RLs (fun r => D.abs (p r - q r) * g r r') :=
      lsum_congr (fun r hr =>
        D.abs_mul_nonneg (p r - q r) (g r r') (hpos r r' hr hr'))
    rw [h1, ← h3]
    exact h2
  -- Sum over probe values, swap the sums, and collapse each row to 1.
  have step1 : dTV D RUs (garble RLs p g) (garble RLs q g) ≤
      lsum RUs (fun r' => lsum RLs (fun r => D.abs (p r - q r) * g r r')) :=
    lsum_le_lsum D RUs key
  have step2 : lsum RUs (fun r' =>
        lsum RLs (fun r => D.abs (p r - q r) * g r r')) =
      lsum RLs (fun r =>
        lsum RUs (fun r' => D.abs (p r - q r) * g r r')) :=
    (lsum_swap D RLs RUs (fun r r' => D.abs (p r - q r) * g r r')).symm
  have step3 : lsum RLs (fun r =>
        lsum RUs (fun r' => D.abs (p r - q r) * g r r')) = dTV D RLs p q :=
    lsum_congr (fun r hr => by
      rw [lsum_mul_left D RUs (D.abs (p r - q r)) (fun r' => g r r'),
          hrow r hr, D.mul_one])
  rw [step2, step3] at step1
  exact step1

/-! ### The quantitative second law -/

/-- Antitone from step-antitone, over the abstract order (the `Q`-valued
sibling of the parent file's `antitone_of_step`). -/
theorem le_antitone_of_step (D : AbsData Q) {u : Nat → Q}
    (hstep : ∀ n, u (n + 1) ≤ u n) : ∀ s t, s ≤ t → u t ≤ u s := by
  intro s t
  induction t with
  | zero =>
    intro hst
    cases Nat.eq_zero_of_le_zero hst
    exact D.le_refl _
  | succ n ih =>
    intro hst
    by_cases h : s = n + 1
    · rw [h]
      exact D.le_refl _
    · exact D.le_trans _ _ _ (hstep n)
        (ih (Nat.le_of_lt_succ (Nat.lt_of_le_of_ne hst h)))

/-- **The second law, quantitative arrow (Theorem S8).** Under any autonomous
stochastic law, the total-variation distance between the laws of any two
ensemble contents is antitone in time: the quantitative refinement of
`second_law_arrow`, obtained by iterating the DPI. -/
theorem tv_arrow (D : AbsData Q) (RLs : List RL) (g : RL → RL → Q)
    (hpos : ∀ r r', r ∈ RLs → r' ∈ RLs → (0 : Q) ≤ g r r')
    (hrow : ∀ r, r ∈ RLs → lsum RLs (fun r' => g r r') = 1)
    (law₁ law₂ : Nat → RL → Q)
    (hstep₁ : ∀ n, ∀ r, r ∈ RLs → law₁ (n+1) r = garble RLs (law₁ n) g r)
    (hstep₂ : ∀ n, ∀ r, r ∈ RLs → law₂ (n+1) r = garble RLs (law₂ n) g r) :
    ∀ s t, s ≤ t →
      dTV D RLs (law₁ t) (law₂ t) ≤ dTV D RLs (law₁ s) (law₂ s) :=
  le_antitone_of_step D
    (u := fun t => dTV D RLs (law₁ t) (law₂ t))
    (fun n => by
      show dTV D RLs (law₁ (n+1)) (law₂ (n+1)) ≤ dTV D RLs (law₁ n) (law₂ n)
      have h : dTV D RLs (law₁ (n+1)) (law₂ (n+1)) =
          dTV D RLs (garble RLs (law₁ n) g) (garble RLs (law₂ n) g) :=
        lsum_congr (fun r hr => by rw [hstep₁ n r hr, hstep₂ n r hr])
      rw [h]
      exact tv_data_processing D RLs RLs g hpos hrow (law₁ n) (law₂ n))

/-- **Lyapunov / free-energy arrow (Theorem S9).** Distance to any
stationary law `π` of the autonomous kernel never increases (TV form of
non-increasing free energy). A stationary law is a fixed point of its own
garbling. -/
theorem lyapunov_arrow (D : AbsData Q) (RLs : List RL) (g : RL → RL → Q)
    (hpos : ∀ r r', r ∈ RLs → r' ∈ RLs → (0 : Q) ≤ g r r')
    (hrow : ∀ r, r ∈ RLs → lsum RLs (fun r' => g r r') = 1)
    (π : RL → Q) (hπ : ∀ r, r ∈ RLs → π r = garble RLs π g r)
    (law : Nat → RL → Q)
    (hstep : ∀ n, ∀ r, r ∈ RLs → law (n+1) r = garble RLs (law n) g r) :
    ∀ s t, s ≤ t → dTV D RLs (law t) π ≤ dTV D RLs (law s) π :=
  tv_arrow D RLs g hpos hrow law (fun _ => π) hstep
    (fun _ r hr => hπ r hr)

/-- Soundness meets the metric: a pair merged at imprint is not merely merged
at every horizon (`merged_forever`) -- it sits at total-variation distance
exactly zero at every horizon. No revival, quantitatively. -/
theorem merged_at_distance_zero (D : AbsData Q) (RLs : List RL)
    {law₁ law₂ : Nat → RL → Q} (g : RL → RL → Q)
    (hstep₁ : ∀ n, ∀ r, r ∈ RLs → law₁ (n+1) r = garble RLs (law₁ n) g r)
    (hstep₂ : ∀ n, ∀ r, r ∈ RLs → law₂ (n+1) r = garble RLs (law₂ n) g r)
    (h0 : EqOn RLs (law₁ 0) (law₂ 0)) :
    ∀ t, dTV D RLs (law₁ t) (law₂ t) = 0 :=
  fun t => dtv_zero_of_eqOn D RLs
    (merged_forever RLs g hstep₁ hstep₂ h0 t)

/-!
# Obs.StochasticThermo

Total-variation data processing and Lyapunov forms for stochastic unlock.
-/

section UnitWitness

local instance : Add Unit := ⟨fun _ _ => ()⟩
local instance : Mul Unit := ⟨fun _ _ => ()⟩
local instance : Sub Unit := ⟨fun _ _ => ()⟩
local instance : OfNat Unit 0 := ⟨()⟩
local instance : OfNat Unit 1 := ⟨()⟩
local instance : LE Unit := ⟨fun _ _ => True⟩

/-- One-point model: the bundle is consistent. -/
def unitAbsData : AbsData Unit where
  abs := fun a => a
  le_refl := fun _ => trivial
  le_trans := fun _ _ _ _ _ => trivial
  add_le_add := fun _ _ _ _ _ _ => trivial
  add_comm := fun _ _ => rfl
  add_assoc := fun _ _ _ => rfl
  zero_add := fun _ => rfl
  mul_zero := fun _ => rfl
  mul_one := fun _ => rfl
  mul_add := fun _ _ _ => rfl
  sub_mul := fun _ _ _ => rfl
  add_sub_add := fun _ _ _ _ => rfl
  sub_self := fun _ => rfl
  abs_zero := rfl
  abs_add_le := fun _ _ => trivial
  abs_mul_nonneg := fun _ _ _ => rfl

end UnitWitness

/-- Nondegenerate model over `Int`. May report `propext` from Lean `Int` lemmas. -/
def intAbsData : AbsData Int where
  abs := fun a => (a.natAbs : Int)
  le_refl := fun a => Int.le_refl a
  le_trans := fun _ _ _ h1 h2 => Int.le_trans h1 h2
  add_le_add := fun _ _ _ _ h1 h2 => Int.add_le_add h1 h2
  add_comm := Int.add_comm
  add_assoc := Int.add_assoc
  zero_add := Int.zero_add
  mul_zero := Int.mul_zero
  mul_one := Int.mul_one
  mul_add := Int.mul_add
  sub_mul := Int.sub_mul
  add_sub_add := fun a b c d => by omega
  sub_self := Int.sub_self
  abs_zero := rfl
  abs_add_le := fun a b => by
    show ((a + b).natAbs : Int) ≤ (a.natAbs : Int) + (b.natAbs : Int)
    omega
  abs_mul_nonneg := fun a b hb => by
    show ((a * b).natAbs : Int) = (a.natAbs : Int) * b
    rw [Int.natAbs_mul, Int.natCast_mul, Int.natAbs_of_nonneg hb]

end Obs.StochasticUnlock

-- #print axioms
#print axioms Obs.StochasticUnlock.lsum_swap
#print axioms Obs.StochasticUnlock.abs_lsum_le
#print axioms Obs.StochasticUnlock.dtv_zero_of_eqOn
#print axioms Obs.StochasticUnlock.tv_data_processing
#print axioms Obs.StochasticUnlock.tv_arrow
#print axioms Obs.StochasticUnlock.lyapunov_arrow
#print axioms Obs.StochasticUnlock.merged_at_distance_zero
#print axioms Obs.StochasticUnlock.unitAbsData
-- intAbsData / intFDivData may report propext (Lean Int lemmas).
#print axioms Obs.StochasticUnlock.intAbsData

