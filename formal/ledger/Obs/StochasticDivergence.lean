import Obs.StochasticUnlock
import Obs.TotalVariationDPI

/-!
# Obs.StochasticDivergence

f-divergence data processing for stochastic unlock.
-/

set_option linter.unusedSectionVars false

namespace Obs.StochasticUnlock

variable {Q : Type} [Add Q] [Mul Q] [Sub Q] [OfNat Q 0] [OfNat Q 1] [LE Q]
  [DecidableEq Q]
variable {R RL RU X C : Type}

/-- The divergence-kernel bundle: the four facts about `F` that the
data-processing inequality consumes, and nothing else. For
`F(a,b) = a log(a/b)` over `Real` these are the log-sum inequality and its
companions; for `F(a,b) = |a - b|` they follow from `AbsData`
(`absFDivData` below). -/
structure FDivData (Q : Type) [Add Q] [Mul Q] [Sub Q] [OfNat Q 0] [OfNat Q 1]
    [LE Q] where
  F : Q → Q → Q
  F_self : ∀ a : Q, F a a = 0
  F_superadd : ∀ a b c d : Q, (0 : Q) ≤ a → (0 : Q) ≤ b → (0 : Q) ≤ c →
    (0 : Q) ≤ d → F (a + b) (c + d) ≤ F a c + F b d
  F_mul_right : ∀ a b c : Q, (0 : Q) ≤ c → F (a * c) (b * c) = F a b * c
  mul_nonneg : ∀ a b : Q, (0 : Q) ≤ a → (0 : Q) ≤ b → (0 : Q) ≤ a * b

/-- The F-divergence between two laws on the declared readout values. -/
def fDiv (E : FDivData Q) (l : List R) (p q : R → Q) : Q :=
  lsum l (fun r => E.F (p r) (q r))

/-! ### Nonnegativity plumbing -/

theorem lsum_nonneg (D : AbsData Q) (l : List α) {f : α → Q}
    (h : ∀ x, x ∈ l → (0 : Q) ≤ f x) : (0 : Q) ≤ lsum l f := by
  induction l with
  | nil => exact D.le_refl 0
  | cons x xs ih =>
    show (0 : Q) ≤ f x + lsum xs f
    have h0 : (0 : Q) = 0 + 0 := (D.zero_add 0).symm
    rw [h0]
    exact D.add_le_add _ _ _ _ (h x (mem_head x xs))
      (ih (fun y hy => h y (mem_tail x hy)))

/-- Laws stay nonnegative under any stochastic evolution. -/
theorem law_nonneg_forever (D : AbsData Q) (E : FDivData Q) (RLs : List RL)
    (g : RL → RL → Q)
    (hpos : ∀ r r', r ∈ RLs → r' ∈ RLs → (0 : Q) ≤ g r r')
    (law : Nat → RL → Q)
    (hstep : ∀ n, ∀ r, r ∈ RLs → law (n+1) r = garble RLs (law n) g r)
    (h0 : ∀ r, r ∈ RLs → (0 : Q) ≤ law 0 r) :
    ∀ n, ∀ r, r ∈ RLs → (0 : Q) ≤ law n r := by
  intro n
  induction n with
  | zero => exact h0
  | succ m ih =>
    intro r hr
    rw [hstep m r hr]
    exact lsum_nonneg D RLs (fun r' hr' =>
      E.mul_nonneg _ _ (ih r' hr') (hpos r' r hr' hr))

/-! ### The list log-sum inequality -/

/-- Superadditivity of the kernel extends from two points to any declared
list: `F(Σf, Σg) ≤ Σ F(f, g)` on nonnegatives. For `F = a log(a/b)` this is
the log-sum inequality itself; here it is pure induction. -/
theorem F_lsum_le (D : AbsData Q) (E : FDivData Q) (l : List α)
    {f g : α → Q} (hf : ∀ x, x ∈ l → (0 : Q) ≤ f x)
    (hg : ∀ x, x ∈ l → (0 : Q) ≤ g x) :
    E.F (lsum l f) (lsum l g) ≤ lsum l (fun a => E.F (f a) (g a)) := by
  induction l with
  | nil =>
    show E.F (0 : Q) 0 ≤ (0 : Q)
    rw [E.F_self]
    exact D.le_refl 0
  | cons x xs ih =>
    show E.F (f x + lsum xs f) (g x + lsum xs g) ≤
         E.F (f x) (g x) + lsum xs (fun a => E.F (f a) (g a))
    have hfx := hf x (mem_head x xs)
    have hgx := hg x (mem_head x xs)
    have hf' : ∀ y, y ∈ xs → (0 : Q) ≤ f y :=
      fun y hy => hf y (mem_tail x hy)
    have hg' : ∀ y, y ∈ xs → (0 : Q) ≤ g y :=
      fun y hy => hg y (mem_tail x hy)
    exact D.le_trans _ _ _
      (E.F_superadd (f x) (lsum xs f) (g x) (lsum xs g) hfx
        (lsum_nonneg D xs hf') hgx (lsum_nonneg D xs hg'))
      (D.add_le_add _ _ _ _ (D.le_refl _) (ih hf' hg'))

/-! ### The data-processing inequality, for every divergence at once -/

/-- **The f-divergence data-processing inequality (Theorem S10).** Any
stochastic channel contracts every divergence in the family: total variation,
KL, and the rest, in one proof. Same skeleton as the
`tv_data_processing`: pointwise log-sum, one sum swap, rows collapse to 1. -/
theorem f_data_processing (D : AbsData Q) (E : FDivData Q) (RLs : List RL)
    (RUs : List RU) (g : RL → RU → Q)
    (hpos : ∀ r r', r ∈ RLs → r' ∈ RUs → (0 : Q) ≤ g r r')
    (hrow : ∀ r, r ∈ RLs → lsum RUs (fun r' => g r r') = 1)
    (p q : RL → Q)
    (hp : ∀ r, r ∈ RLs → (0 : Q) ≤ p r)
    (hq : ∀ r, r ∈ RLs → (0 : Q) ≤ q r) :
    fDiv E RUs (garble RLs p g) (garble RLs q g) ≤ fDiv E RLs p q := by
  have key : ∀ r', r' ∈ RUs →
      E.F (garble RLs p g r') (garble RLs q g r') ≤
      lsum RLs (fun r => E.F (p r) (q r) * g r r') := by
    intro r' hr'
    have h1 : E.F (garble RLs p g r') (garble RLs q g r') ≤
        lsum RLs (fun r => E.F (p r * g r r') (q r * g r r')) :=
      F_lsum_le D E RLs
        (fun r hr => E.mul_nonneg _ _ (hp r hr) (hpos r r' hr hr'))
        (fun r hr => E.mul_nonneg _ _ (hq r hr) (hpos r r' hr hr'))
    have h2 : lsum RLs (fun r => E.F (p r * g r r') (q r * g r r')) =
        lsum RLs (fun r => E.F (p r) (q r) * g r r') :=
      lsum_congr (fun r hr =>
        E.F_mul_right (p r) (q r) (g r r') (hpos r r' hr hr'))
    rw [h2] at h1
    exact h1
  have step1 : fDiv E RUs (garble RLs p g) (garble RLs q g) ≤
      lsum RUs (fun r' => lsum RLs (fun r => E.F (p r) (q r) * g r r')) :=
    lsum_le_lsum D RUs key
  have step2 : lsum RUs (fun r' =>
        lsum RLs (fun r => E.F (p r) (q r) * g r r')) =
      lsum RLs (fun r =>
        lsum RUs (fun r' => E.F (p r) (q r) * g r r')) :=
    (lsum_swap D RLs RUs (fun r r' => E.F (p r) (q r) * g r r')).symm
  have step3 : lsum RLs (fun r =>
        lsum RUs (fun r' => E.F (p r) (q r) * g r r')) = fDiv E RLs p q :=
    lsum_congr (fun r hr => by
      rw [lsum_mul_left D RUs (E.F (p r) (q r)) (fun r' => g r r'),
          hrow r hr, D.mul_one])
  rw [step2, step3] at step1
  exact step1

/-! ### The divergence second law -/

/-- **The second law, divergence form (Theorem S11).** Under any autonomous
stochastic law, every f-divergence between the laws of two ensemble contents
is antitone in time. Laws need only start nonnegative; they stay so. -/
theorem f_arrow (D : AbsData Q) (E : FDivData Q) (RLs : List RL)
    (g : RL → RL → Q)
    (hpos : ∀ r r', r ∈ RLs → r' ∈ RLs → (0 : Q) ≤ g r r')
    (hrow : ∀ r, r ∈ RLs → lsum RLs (fun r' => g r r') = 1)
    (law₁ law₂ : Nat → RL → Q)
    (hstep₁ : ∀ n, ∀ r, r ∈ RLs → law₁ (n+1) r = garble RLs (law₁ n) g r)
    (hstep₂ : ∀ n, ∀ r, r ∈ RLs → law₂ (n+1) r = garble RLs (law₂ n) g r)
    (h0₁ : ∀ r, r ∈ RLs → (0 : Q) ≤ law₁ 0 r)
    (h0₂ : ∀ r, r ∈ RLs → (0 : Q) ≤ law₂ 0 r) :
    ∀ s t, s ≤ t →
      fDiv E RLs (law₁ t) (law₂ t) ≤ fDiv E RLs (law₁ s) (law₂ s) :=
  le_antitone_of_step D
    (u := fun t => fDiv E RLs (law₁ t) (law₂ t))
    (fun n => by
      show fDiv E RLs (law₁ (n+1)) (law₂ (n+1)) ≤
           fDiv E RLs (law₁ n) (law₂ n)
      have h : fDiv E RLs (law₁ (n+1)) (law₂ (n+1)) =
          fDiv E RLs (garble RLs (law₁ n) g) (garble RLs (law₂ n) g) :=
        lsum_congr (fun r hr => by rw [hstep₁ n r hr, hstep₂ n r hr])
      rw [h]
      exact f_data_processing D E RLs RLs g hpos hrow (law₁ n) (law₂ n)
        (law_nonneg_forever D E RLs g hpos law₁ hstep₁ h0₁ n)
        (law_nonneg_forever D E RLs g hpos law₂ hstep₂ h0₂ n))

/-- **The Lyapunov arrow, divergence form (Theorem S12).** Every f-divergence
to a stationary law never increases. With `F(a,b) = a log(a/b)` this IS
"non-equilibrium free energy D(law_n || pi) is non-increasing" -- the
thermodynamic second law -- pending only the four-fact discharge of the
kernel bundle. -/
theorem f_lyapunov (D : AbsData Q) (E : FDivData Q) (RLs : List RL)
    (g : RL → RL → Q)
    (hpos : ∀ r r', r ∈ RLs → r' ∈ RLs → (0 : Q) ≤ g r r')
    (hrow : ∀ r, r ∈ RLs → lsum RLs (fun r' => g r r') = 1)
    (π : RL → Q) (hπ : ∀ r, r ∈ RLs → π r = garble RLs π g r)
    (hπ0 : ∀ r, r ∈ RLs → (0 : Q) ≤ π r)
    (law : Nat → RL → Q)
    (hstep : ∀ n, ∀ r, r ∈ RLs → law (n+1) r = garble RLs (law n) g r)
    (h0 : ∀ r, r ∈ RLs → (0 : Q) ≤ law 0 r) :
    ∀ s t, s ≤ t → fDiv E RLs (law t) π ≤ fDiv E RLs (law s) π :=
  f_arrow D E RLs g hpos hrow law (fun _ => π) hstep
    (fun _ r hr => hπ r hr) h0 hπ0

/-- **Gibbs' inequality, abstract form (Theorem S13).** A divergence between
laws of equal total mass (in particular, two probability laws) is
nonnegative. The floor of the Lyapunov function exists, at zero axioms. -/
theorem f_nonneg (D : AbsData Q) (E : FDivData Q) (l : List R)
    {p q : R → Q} (hp : ∀ r, r ∈ l → (0 : Q) ≤ p r)
    (hq : ∀ r, r ∈ l → (0 : Q) ≤ q r)
    (hsum : lsum l p = lsum l q) : (0 : Q) ≤ fDiv E l p q := by
  have h := F_lsum_le D E l hp hq
  rw [hsum, E.F_self] at h
  exact h

/-! ### Total variation is an instance, not an analogue -/

/-- Any `AbsData` generates a divergence kernel `F(a,b) = |a - b|`; the only
extra fact needed is `mul_nonneg`. -/
def absFDivData (D : AbsData Q)
    (hmul : ∀ a b : Q, (0 : Q) ≤ a → (0 : Q) ≤ b → (0 : Q) ≤ a * b) :
    FDivData Q where
  F := fun a b => D.abs (a - b)
  F_self := fun a => by
    show D.abs (a - a) = 0
    rw [D.sub_self, D.abs_zero]
  F_superadd := fun a b c d _ _ _ _ => by
    show D.abs ((a + b) - (c + d)) ≤ D.abs (a - c) + D.abs (b - d)
    rw [D.add_sub_add]
    exact D.abs_add_le (a - c) (b - d)
  F_mul_right := fun a b c hc => by
    show D.abs (a * c - b * c) = D.abs (a - b) * c
    rw [← D.sub_mul]
    exact D.abs_mul_nonneg (a - b) c hc
  mul_nonneg := hmul

/-- Total variation is definitionally the divergence of the
absolute-value kernel: `tv_data_processing` is the `f(x) = |x - 1|` member of
`f_data_processing`, literally. -/
theorem fdiv_abs_eq_dtv (D : AbsData Q)
    (hmul : ∀ a b : Q, (0 : Q) ≤ a → (0 : Q) ≤ b → (0 : Q) ≤ a * b)
    (l : List R) (p q : R → Q) :
    fDiv (absFDivData D hmul) l p q = dTV D l p q := rfl

/-- The linear kernel `F(a,b) = a - b`: the degenerate member of the family
(its divergence vanishes on equal-mass laws) and a consistency witness that
costs nothing. -/
def subFDivData (D : AbsData Q)
    (hmul : ∀ a b : Q, (0 : Q) ≤ a → (0 : Q) ≤ b → (0 : Q) ≤ a * b) :
    FDivData Q where
  F := fun a b => a - b
  F_self := D.sub_self
  F_superadd := fun a b c d _ _ _ _ => by
    show (a + b) - (c + d) ≤ (a - c) + (b - d)
    rw [D.add_sub_add]
    exact D.le_refl _
  F_mul_right := fun a b c _ => (D.sub_mul a b c).symm
  mul_nonneg := hmul

/-!
# Obs.StochasticDivergence

f-divergence data processing for stochastic unlock.
-/

section UnitWitness

local instance : Add Unit := ⟨fun _ _ => ()⟩
local instance : Mul Unit := ⟨fun _ _ => ()⟩
local instance : Sub Unit := ⟨fun _ _ => ()⟩
local instance : OfNat Unit 0 := ⟨()⟩
local instance : OfNat Unit 1 := ⟨()⟩
local instance : LE Unit := ⟨fun _ _ => True⟩

/-- One-point model: the four-field bundle is consistent. -/
def unitFDivData : FDivData Unit where
  F := fun _ _ => ()
  F_self := fun _ => rfl
  F_superadd := fun _ _ _ _ _ _ _ _ => trivial
  F_mul_right := fun _ _ _ _ => rfl
  mul_nonneg := fun _ _ _ _ => trivial

end UnitWitness

/-- Total variation over `Int` via `intAbsData`. May report `propext`. -/
def intFDivData : FDivData Int :=
  absFDivData intAbsData (fun _ _ ha hb => Int.mul_nonneg ha hb)

end Obs.StochasticUnlock

-- #print axioms
#print axioms Obs.StochasticUnlock.lsum_nonneg
#print axioms Obs.StochasticUnlock.law_nonneg_forever
#print axioms Obs.StochasticUnlock.F_lsum_le
#print axioms Obs.StochasticUnlock.f_data_processing
#print axioms Obs.StochasticUnlock.f_arrow
#print axioms Obs.StochasticUnlock.f_lyapunov
#print axioms Obs.StochasticUnlock.f_nonneg
#print axioms Obs.StochasticUnlock.absFDivData
#print axioms Obs.StochasticUnlock.fdiv_abs_eq_dtv
#print axioms Obs.StochasticUnlock.subFDivData
#print axioms Obs.StochasticUnlock.unitFDivData
-- intAbsData / intFDivData may report propext (Lean Int lemmas).
#print axioms Obs.StochasticUnlock.intFDivData

