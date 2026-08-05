import TwoBounce

/-!
# WaveEquation (EXPERIMENTAL — quarantined; exports nothing to the paper)

Probe: a wave equation over the corpus's own alphabet. The discrete
d'Alembert form `u(t+1) = u(t-1) + Δu(t)` becomes, over `Bool` with
addition as xor, a second-order field equation
`next i = prev i ^^ X cur i`, with the spatial coupling `X` left
completely general. Results:

* **Two-bounce in closed form** (`step_eq_two_bounce`): the wave step
  *is* `swap ∘ shear`, with both factors involutive. The corpus's
  factorisation theorem holds here by explicit construction, with the
  pair exhibited, and the identity is definitional.
* **The constructive I-1 witness** (`waveFactor`): the pair is
  packaged as a `Bridge.TwoBounce.TwoBounceFactor (step X)` — the
  corpus factorisation holds here by a definitional closed-form
  pair, not by the bounded orbit search through which
  `Bridge.TwoBounce.factor_fin` (itself computable and axiom-free)
  extracts its factors. The involution laws at function level use
  `Prod.ext` and `funext` over the pointwise lemmas, as
  `reverse_step` already does.
* **Time reversal is the bounce swap** (`reverse_is_swapped_pair`,
  `reverse_step_pointwise`): the inverse evolution is presented by the
  swapped pair `shear ∘ swap`, which instantiates the corpus's
  swap-equals-reversal at field level. The pointwise cancellation is
  axiom-free.
* **Translation symmetry on the ring** (`ringX_rot_pointwise`,
  `step_rot_pointwise`, `iterN_step_rot_pointwise`): spatial rotation
  by one site commutes with the ring coupling, with the step, and
  with every iterate of the step, pointwise on both layers and with
  no function extensionality.
* **The spectrum is translation-invariant**
  (`return_iff_rot_return`): a state returns to itself at time `T`
  exactly when its rotation does (converse inverted via rotation by
  `+1`). The boundary-selected spectrum is invariant under the ring
  symmetry — the discrete seed of a dispersion relation.
* **Boundary conditions select the spectrum**: with the same rule and
  a single-pulse initial state, the kernel decides the full period
  table for ring sizes 2–6 (periods 2, 6, 4, 10, 6) and Dirichlet
  sizes 3–5 (periods 8, 10, 12). These instantiate the numerical
  pattern (ring: n even ↦ n, n odd ↦ 2n; fixed ends ↦ 2n + 2) for
  rings at every size from 2 through 6 and for fixed ends at sizes
  3 through 5; Dirichlet n = 6 and everything at n ≥ 7 remain
  numerical conjecture, reproducible for 2 ≤ n ≤ 12 by
  `exhibits/wave/periods.py`, and the closed forms in general `n`
  are marked targets. The ring-of-two instance is degenerate (the
  coupling cancels); see `ring2_period_two`.

What is absent, stated plainly: no frequencies over the reals, no
dispersion relation, no continuum limit, no closed-form period law
in general `n`. The probe shows the *shape* of wave dynamics (second
order, reversible, symmetric, boundary-sensitive spectrum) living
natively on `Bool`.
-/
namespace Experimental.Wave

open Bridge.TwoBounce (EndoInj)

variable {n : Nat}

/-- A field configuration: one pole per site. -/
abbrev Field (n : Nat) : Type := Fin n → Bool

/-- Evolution state: previous and current configuration. -/
abbrev WState (n : Nat) : Type := Field n × Field n

/-- General second-order Z/2 field equation with spatial coupling `X`:
    `next i = prev i ^^ X cur i`. -/
def step (X : Field n → Fin n → Bool) (s : WState n) : WState n :=
  (s.2, fun i => s.1 i ^^ X s.2 i)

/-- Channel swap on the state pair. -/
def swap (s : WState n) : WState n := (s.2, s.1)

/-- The shear: flip the previous layer by the coupling of the current
    layer, and hold the current layer still. -/
def shear (X : Field n → Fin n → Bool) (s : WState n) : WState n :=
  (fun i => s.1 i ^^ X s.2 i, s.2)

theorem xor_cancel (a b : Bool) : ((a ^^ b) ^^ b) = a := by
  cases a <;> cases b <;> rfl

/-! ## The wave step is two flips, in closed form -/

/-- `swap` is an involution (definitional, by structure eta). -/
theorem swap_involution (s : WState n) : swap (swap s) = s := rfl

/-- `shear` is an involution, pointwise and axiom-free. -/
theorem shear_involution_pointwise (X : Field n → Fin n → Bool)
    (s : WState n) :
    (∀ i, (shear X (shear X s)).1 i = s.1 i) ∧
    (∀ i, (shear X (shear X s)).2 i = s.2 i) :=
  ⟨fun i => xor_cancel (s.1 i) (X s.2 i), fun _ => rfl⟩

/-- **The wave step is exactly two flips**: `step X = swap ∘ shear X`,
    definitionally. The two-bounce factorisation of the corpus holds
    here by explicit construction. -/
theorem step_eq_two_bounce (X : Field n → Fin n → Bool) (s : WState n) :
    step X s = swap (shear X s) := rfl

/-! ## Time reversal is the bounce swap -/

/-- The reverse evolution, presented by the swapped pair. -/
def reverse (X : Field n → Fin n → Bool) (s : WState n) : WState n :=
  shear X (swap s)

/-- The reverse is the conjugate of the step by the channel swap,
    definitionally: `reverse = swap ∘ step ∘ swap` and equally the
    swapped two-bounce pair `shear ∘ swap`. -/
theorem reverse_is_swapped_pair (X : Field n → Fin n → Bool)
    (s : WState n) :
    reverse X s = swap (step X (swap s)) := rfl

/-- Pointwise, axiom-free cancellation: the swapped pair inverts the
    step on both layers, in both composition orders. -/
theorem reverse_step_pointwise (X : Field n → Fin n → Bool)
    (s : WState n) :
    (∀ i, (reverse X (step X s)).1 i = s.1 i) ∧
    (∀ i, (reverse X (step X s)).2 i = s.2 i) ∧
    (∀ i, (step X (reverse X s)).1 i = s.1 i) ∧
    (∀ i, (step X (reverse X s)).2 i = s.2 i) :=
  ⟨fun i => xor_cancel (s.1 i) (X s.2 i),
   fun _ => rfl,
   fun _ => rfl,
   fun i => xor_cancel (s.2 i) (X s.1 i)⟩

/-- Packaged reversal (uses function extensionality; footprint noted
    in the build log). -/
theorem reverse_step (X : Field n → Fin n → Bool) (s : WState n) :
    reverse X (step X s) = s := by
  have h := reverse_step_pointwise X s
  exact Prod.ext (funext h.1) (funext h.2.1)

/-- The wave evolution is lossless for every coupling and every size:
    no two histories merge. -/
theorem step_lossless (X : Field n → Fin n → Bool) :
    EndoInj (step X) := by
  intro a b h
  calc a = reverse X (step X a) := (reverse_step X a).symm
    _ = reverse X (step X b) := by rw [h]
    _ = b := reverse_step X b

/-! ## Boundary conditions -/

/-- Periodic boundary: ring coupling (carrier kept inhabited so the
    neighbour literals exist). -/
def ringX {m : Nat} (c : Field (m + 1)) (i : Fin (m + 1)) : Bool :=
  c (i - 1) ^^ c (i + 1)

/-- Padded lookup with walls fixed at `false`. -/
def wallAt (c : Field n) (m : Nat) : Bool :=
  if h : m < n then c ⟨m, h⟩ else false

/-- Fixed ends (Dirichlet): wall coupling. -/
def dirichletX (c : Field n) (i : Fin n) : Bool :=
  (if i.val = 0 then false else wallAt c (i.val - 1)) ^^
    wallAt c (i.val + 1)

/-- Iterate. -/
def iterN {α : Type} (f : α → α) : Nat → α → α
  | 0, a => a
  | m + 1, a => iterN f m (f a)

/-- The head-first fold also peels its last application: one step of
    `f` on the outside. -/
theorem iterN_succ_out {α : Type} (f : α → α) (T : Nat) (a : α) :
    iterN f (T + 1) a = f (iterN f T a) := by
  induction T generalizing a with
  | zero => rfl
  | succ T ih =>
    show iterN f (T + 1) (f a) = f (iterN f (T + 1) a)
    rw [ih (f a)]
    rfl

/-! ## The exhibited two-bounce witness -/

/-- **Explicit closed-form factorisation.** The corpus's I-1
    two-bounce form holds for the wave step by a definitional pair
    exhibited in closed form — `φ := shear X`, `σ := swap` — rather
    than by the bounded orbit search through which
    `Bridge.TwoBounce.factor_fin` (itself computable and axiom-free)
    extracts its factors. The involution laws at function level are
    lifted from the pointwise lemmas via `Prod.ext` and `funext`;
    that use of function extensionality is noted here, as for
    `reverse_step`. -/
def waveFactor (X : Field n → Fin n → Bool) :
    Bridge.TwoBounce.TwoBounceFactor (step X) where
  φ := shear X
  σ := swap
  φ_inv := fun s =>
    Prod.ext (funext (shear_involution_pointwise X s).1)
      (funext (shear_involution_pointwise X s).2)
  σ_inv := swap_involution
  factor := step_eq_two_bounce X

/-! ## Translation symmetry on the ring

Spatial rotation by one site, on fields and on states. Two `Fin`
helper lemmas at value level make the wrap-around arithmetic exact.
All symmetry statements below are pointwise on both layers; no
function extensionality is used in this section. -/

/-- On `Fin (m+1)`, subtracting then adding one is the identity. -/
theorem fin_sub_one_add_one {m : Nat} (i : Fin (m + 1)) :
    (i - 1) + 1 = i := by
  apply Fin.ext
  rw [Fin.add_def, Fin.sub_def]
  show ((m + 1 - 1 % (m + 1) + i.val) % (m + 1) + 1 % (m + 1)) % (m + 1)
      = i.val
  have ho : 1 % (m + 1) ≤ m + 1 :=
    Nat.le_of_lt (Nat.mod_lt 1 (Nat.succ_pos m))
  generalize 1 % (m + 1) = o at ho ⊢
  rw [Nat.mod_add_mod]
  have h : m + 1 - o + i.val + o = i.val + (m + 1) := by omega
  rw [h, Nat.add_mod_right, Nat.mod_eq_of_lt i.isLt]

/-- On `Fin (m+1)`, adding then subtracting one is the identity. -/
theorem fin_add_one_sub_one {m : Nat} (i : Fin (m + 1)) :
    (i + 1) - 1 = i := by
  apply Fin.ext
  rw [Fin.sub_def, Fin.add_def]
  show (m + 1 - 1 % (m + 1) + (i.val + 1 % (m + 1)) % (m + 1)) % (m + 1)
      = i.val
  have ho : 1 % (m + 1) ≤ m + 1 :=
    Nat.le_of_lt (Nat.mod_lt 1 (Nat.succ_pos m))
  generalize 1 % (m + 1) = o at ho ⊢
  rw [Nat.add_mod_mod]
  have h : m + 1 - o + (i.val + o) = i.val + (m + 1) := by omega
  rw [h, Nat.add_mod_right, Nat.mod_eq_of_lt i.isLt]

/-- Spatial rotation on fields: site `i` reads from site `i - 1`. -/
def rotF {m : Nat} (c : Field (m + 1)) : Field (m + 1) :=
  fun i => c (i - 1)

/-- Rotation lifted to states componentwise. -/
def rotS {m : Nat} (s : WState (m + 1)) : WState (m + 1) :=
  (rotF s.1, rotF s.2)

/-- Inverse rotation on fields: site `i` reads from site `i + 1`. -/
def rotFInv {m : Nat} (c : Field (m + 1)) : Field (m + 1) :=
  fun i => c (i + 1)

/-- Inverse rotation lifted to states componentwise. -/
def rotSInv {m : Nat} (s : WState (m + 1)) : WState (m + 1) :=
  (rotFInv s.1, rotFInv s.2)

/-- The ring coupling is equivariant under rotation, pointwise. -/
theorem ringX_rot_pointwise {m : Nat} (c : Field (m + 1))
    (i : Fin (m + 1)) :
    ringX (rotF c) i = ringX c (i - 1) := by
  show (c ((i - 1) - 1) ^^ c ((i + 1) - 1))
      = (c ((i - 1) - 1) ^^ c ((i - 1) + 1))
  rw [fin_add_one_sub_one, fin_sub_one_add_one]

/-- The ring coupling is equivariant under the inverse rotation,
    pointwise. -/
theorem ringX_rotInv_pointwise {m : Nat} (c : Field (m + 1))
    (i : Fin (m + 1)) :
    ringX (rotFInv c) i = ringX c (i + 1) := by
  show (c ((i - 1) + 1) ^^ c ((i + 1) + 1))
      = (c ((i + 1) - 1) ^^ c ((i + 1) + 1))
  rw [fin_sub_one_add_one, fin_add_one_sub_one]

/-- The ring step commutes with rotation, pointwise on both layers. -/
theorem step_rot_pointwise {m : Nat} (s : WState (m + 1)) :
    (∀ i, (step ringX (rotS s)).1 i = (rotS (step ringX s)).1 i) ∧
    (∀ i, (step ringX (rotS s)).2 i = (rotS (step ringX s)).2 i) :=
  ⟨fun _ => rfl,
   fun i => by
     show (s.1 (i - 1) ^^ ringX (rotF s.2) i)
         = (s.1 (i - 1) ^^ ringX s.2 (i - 1))
     rw [ringX_rot_pointwise]⟩

/-- The ring step commutes with the inverse rotation, pointwise on
    both layers. -/
theorem step_rotInv_pointwise {m : Nat} (s : WState (m + 1)) :
    (∀ i, (step ringX (rotSInv s)).1 i = (rotSInv (step ringX s)).1 i) ∧
    (∀ i, (step ringX (rotSInv s)).2 i = (rotSInv (step ringX s)).2 i) :=
  ⟨fun _ => rfl,
   fun i => by
     show (s.1 (i + 1) ^^ ringX (rotFInv s.2) i)
         = (s.1 (i + 1) ^^ ringX s.2 (i + 1))
     rw [ringX_rotInv_pointwise]⟩

/-! ## The spectrum is translation-invariant

Iterating the ring step commutes with rotation at every time `T`
(pointwise induction, no extensionality), so a state returns to
itself at time `T` exactly when its rotation does. The
boundary-selected spectrum is invariant under the ring symmetry —
the discrete seed of a dispersion relation. -/

/-- The ring step sends pointwise-equal states to pointwise-equal
    states (the coupling reads only three sites). -/
theorem step_ringX_congr {m : Nat} (a b : WState (m + 1))
    (h1 : ∀ i, a.1 i = b.1 i) (h2 : ∀ i, a.2 i = b.2 i) :
    (∀ i, (step ringX a).1 i = (step ringX b).1 i) ∧
    (∀ i, (step ringX a).2 i = (step ringX b).2 i) :=
  ⟨h2,
   fun i => by
     show (a.1 i ^^ (a.2 (i - 1) ^^ a.2 (i + 1)))
         = (b.1 i ^^ (b.2 (i - 1) ^^ b.2 (i + 1)))
     rw [h1 i, h2 (i - 1), h2 (i + 1)]⟩

/-- Pointwise-equal states stay pointwise equal under every number of
    ring steps. -/
theorem iterN_step_ringX_congr {m : Nat} (T : Nat) :
    ∀ a b : WState (m + 1),
      (∀ i, a.1 i = b.1 i) → (∀ i, a.2 i = b.2 i) →
      (∀ i, (iterN (step ringX) T a).1 i
          = (iterN (step ringX) T b).1 i) ∧
      (∀ i, (iterN (step ringX) T a).2 i
          = (iterN (step ringX) T b).2 i) := by
  induction T with
  | zero => exact fun _ _ h1 h2 => ⟨h1, h2⟩
  | succ T ih =>
    intro a b h1 h2
    have hs := step_ringX_congr a b h1 h2
    exact ih (step ringX a) (step ringX b) hs.1 hs.2

/-- Iterating the ring step commutes with rotation for every `T`,
    pointwise on both layers. -/
theorem iterN_step_rot_pointwise {m : Nat} (T : Nat)
    (s : WState (m + 1)) :
    (∀ i, (iterN (step ringX) T (rotS s)).1 i
        = (rotS (iterN (step ringX) T s)).1 i) ∧
    (∀ i, (iterN (step ringX) T (rotS s)).2 i
        = (rotS (iterN (step ringX) T s)).2 i) := by
  induction T with
  | zero => exact ⟨fun _ => rfl, fun _ => rfl⟩
  | succ T ih =>
    have hcong := step_ringX_congr (iterN (step ringX) T (rotS s))
      (rotS (iterN (step ringX) T s)) ih.1 ih.2
    have hcomm := step_rot_pointwise (iterN (step ringX) T s)
    refine ⟨fun i => ?_, fun i => ?_⟩
    · rw [iterN_succ_out (step ringX) T (rotS s),
        iterN_succ_out (step ringX) T s]
      exact (hcong.1 i).trans (hcomm.1 i)
    · rw [iterN_succ_out (step ringX) T (rotS s),
        iterN_succ_out (step ringX) T s]
      exact (hcong.2 i).trans (hcomm.2 i)

/-- Iterating the ring step commutes with the inverse rotation for
    every `T`, pointwise on both layers. -/
theorem iterN_step_rotInv_pointwise {m : Nat} (T : Nat)
    (s : WState (m + 1)) :
    (∀ i, (iterN (step ringX) T (rotSInv s)).1 i
        = (rotSInv (iterN (step ringX) T s)).1 i) ∧
    (∀ i, (iterN (step ringX) T (rotSInv s)).2 i
        = (rotSInv (iterN (step ringX) T s)).2 i) := by
  induction T with
  | zero => exact ⟨fun _ => rfl, fun _ => rfl⟩
  | succ T ih =>
    have hcong := step_ringX_congr (iterN (step ringX) T (rotSInv s))
      (rotSInv (iterN (step ringX) T s)) ih.1 ih.2
    have hcomm := step_rotInv_pointwise (iterN (step ringX) T s)
    refine ⟨fun i => ?_, fun i => ?_⟩
    · rw [iterN_succ_out (step ringX) T (rotSInv s),
        iterN_succ_out (step ringX) T s]
      exact (hcong.1 i).trans (hcomm.1 i)
    · rw [iterN_succ_out (step ringX) T (rotSInv s),
        iterN_succ_out (step ringX) T s]
      exact (hcong.2 i).trans (hcomm.2 i)

/-- If a state returns to itself at time `T` (pointwise, both layers)
    then so does its rotation. -/
theorem return_rot_pointwise {m : Nat} (T : Nat) (s : WState (m + 1))
    (h1 : ∀ i, (iterN (step ringX) T s).1 i = s.1 i)
    (h2 : ∀ i, (iterN (step ringX) T s).2 i = s.2 i) :
    (∀ i, (iterN (step ringX) T (rotS s)).1 i = (rotS s).1 i) ∧
    (∀ i, (iterN (step ringX) T (rotS s)).2 i = (rotS s).2 i) := by
  have hc := iterN_step_rot_pointwise T s
  exact ⟨fun i => (hc.1 i).trans (h1 (i - 1)),
    fun i => (hc.2 i).trans (h2 (i - 1))⟩

/-- If a state returns to itself at time `T` then so does its inverse
    rotation. -/
theorem return_rotInv_pointwise {m : Nat} (T : Nat) (s : WState (m + 1))
    (h1 : ∀ i, (iterN (step ringX) T s).1 i = s.1 i)
    (h2 : ∀ i, (iterN (step ringX) T s).2 i = s.2 i) :
    (∀ i, (iterN (step ringX) T (rotSInv s)).1 i = (rotSInv s).1 i) ∧
    (∀ i, (iterN (step ringX) T (rotSInv s)).2 i = (rotSInv s).2 i) := by
  have hc := iterN_step_rotInv_pointwise T s
  exact ⟨fun i => (hc.1 i).trans (h1 (i + 1)),
    fun i => (hc.2 i).trans (h2 (i + 1))⟩

/-- Converse: if the rotation of a state returns at time `T` then the
    state itself does (invert via rotation by `+1`). -/
theorem return_of_rot_return {m : Nat} (T : Nat) (s : WState (m + 1))
    (h1 : ∀ i, (iterN (step ringX) T (rotS s)).1 i = (rotS s).1 i)
    (h2 : ∀ i, (iterN (step ringX) T (rotS s)).2 i = (rotS s).2 i) :
    (∀ i, (iterN (step ringX) T s).1 i = s.1 i) ∧
    (∀ i, (iterN (step ringX) T s).2 i = s.2 i) := by
  have hr := return_rotInv_pointwise T (rotS s) h1 h2
  have hid1 : ∀ i, (rotSInv (rotS s)).1 i = s.1 i :=
    fun i => congrArg s.1 (fin_add_one_sub_one i)
  have hid2 : ∀ i, (rotSInv (rotS s)).2 i = s.2 i :=
    fun i => congrArg s.2 (fin_add_one_sub_one i)
  have hc := iterN_step_ringX_congr T (rotSInv (rotS s)) s hid1 hid2
  exact ⟨fun i => ((hc.1 i).symm.trans (hr.1 i)).trans (hid1 i),
    fun i => ((hc.2 i).symm.trans (hr.2 i)).trans (hid2 i)⟩

/-- **The spectrum is translation-invariant.** A state returns to
    itself at time `T` (pointwise, both layers) if and only if its
    rotation does. -/
theorem return_iff_rot_return {m : Nat} (T : Nat) (s : WState (m + 1)) :
    ((∀ i, (iterN (step ringX) T s).1 i = s.1 i) ∧
     (∀ i, (iterN (step ringX) T s).2 i = s.2 i)) ↔
    ((∀ i, (iterN (step ringX) T (rotS s)).1 i = (rotS s).1 i) ∧
     (∀ i, (iterN (step ringX) T (rotS s)).2 i = (rotS s).2 i)) :=
  ⟨fun h => return_rot_pointwise T s h.1 h.2,
   fun h => return_of_rot_return T s h.1 h.2⟩

/-! ## Boundary conditions select the spectrum: four sites -/

/-- The single pulse on four sites: silent previous layer, one live
    site now. -/
def pulse4 : WState 4 :=
  (fun _ => false, fun i => decide (i = 0))

/-- On the ring of four, the pulse has state period 4: it returns at
    step 4 and at no positive step before. -/
theorem ring4_period_four :
    (∀ i, (iterN (step ringX) 4 pulse4).1 i = pulse4.1 i) ∧
    (∀ i, (iterN (step ringX) 4 pulse4).2 i = pulse4.2 i) ∧
    (∀ k : Fin 4, k.val ≠ 0 →
      (∃ i, (iterN (step ringX) k.val pulse4).1 i ≠ pulse4.1 i) ∨
      (∃ i, (iterN (step ringX) k.val pulse4).2 i ≠ pulse4.2 i)) := by
  decide

/-- With fixed ends on the same four sites, the same pulse under the
    same rule has state period 10: it returns at step 10 and at no
    positive step before. Boundary alone reshapes the spectrum. -/
theorem dirichlet4_period_ten :
    (∀ i, (iterN (step dirichletX) 10 pulse4).1 i = pulse4.1 i) ∧
    (∀ i, (iterN (step dirichletX) 10 pulse4).2 i = pulse4.2 i) ∧
    (∀ k : Fin 10, k.val ≠ 0 →
      (∃ i, (iterN (step dirichletX) k.val pulse4).1 i ≠ pulse4.1 i) ∨
      (∃ i, (iterN (step dirichletX) k.val pulse4).2 i ≠ pulse4.2 i)) := by
  decide

/-! ## Period table beyond four sites

The same single-pulse experiment at other sizes, each decided by the
kernel. Ring sizes 2, 3, 5, 6 and Dirichlet sizes 3, 5 join size 4;
together they instantiate the numerical pattern (ring: n even ↦ n,
n odd ↦ 2n; Dirichlet ↦ 2n + 2) for rings at every size from 2
through 6 and for fixed ends at sizes 3 through 5. Dirichlet n = 6
(numerically period 14) is part of the conjectural remainder. -/

/-- The single pulse on `m + 1` sites: silent previous layer, one
    live site now. -/
def pulseN (m : Nat) : WState (m + 1) :=
  (fun _ => false, fun i => decide (i = 0))

/-- Ring of two: state period 2 (n even ↦ n). Degenerate instance: on
    `Fin 2` the two neighbours coincide (`i - 1 = i + 1`), so the
    coupling cancels (`ringX c i = false` identically) and the step
    reduces to the free exchange `next = prev` — the period-2 return
    is the fundamental beat, not wave propagation. -/
theorem ring2_period_two :
    (∀ i, (iterN (step ringX) 2 (pulseN 1)).1 i = (pulseN 1).1 i) ∧
    (∀ i, (iterN (step ringX) 2 (pulseN 1)).2 i = (pulseN 1).2 i) ∧
    (∀ k : Fin 2, k.val ≠ 0 →
      (∃ i, (iterN (step ringX) k.val (pulseN 1)).1 i ≠ (pulseN 1).1 i) ∨
      (∃ i, (iterN (step ringX) k.val (pulseN 1)).2 i ≠ (pulseN 1).2 i)) := by
  decide

/-- Ring of three: state period 6 (n odd ↦ 2n). -/
theorem ring3_period_six :
    (∀ i, (iterN (step ringX) 6 (pulseN 2)).1 i = (pulseN 2).1 i) ∧
    (∀ i, (iterN (step ringX) 6 (pulseN 2)).2 i = (pulseN 2).2 i) ∧
    (∀ k : Fin 6, k.val ≠ 0 →
      (∃ i, (iterN (step ringX) k.val (pulseN 2)).1 i ≠ (pulseN 2).1 i) ∨
      (∃ i, (iterN (step ringX) k.val (pulseN 2)).2 i ≠ (pulseN 2).2 i)) := by
  decide

/-- Ring of five: state period 10 (n odd ↦ 2n). -/
theorem ring5_period_ten :
    (∀ i, (iterN (step ringX) 10 (pulseN 4)).1 i = (pulseN 4).1 i) ∧
    (∀ i, (iterN (step ringX) 10 (pulseN 4)).2 i = (pulseN 4).2 i) ∧
    (∀ k : Fin 10, k.val ≠ 0 →
      (∃ i, (iterN (step ringX) k.val (pulseN 4)).1 i ≠ (pulseN 4).1 i) ∨
      (∃ i, (iterN (step ringX) k.val (pulseN 4)).2 i ≠ (pulseN 4).2 i)) := by
  decide

/-- Ring of six: state period 6 (n even ↦ n). -/
theorem ring6_period_six :
    (∀ i, (iterN (step ringX) 6 (pulseN 5)).1 i = (pulseN 5).1 i) ∧
    (∀ i, (iterN (step ringX) 6 (pulseN 5)).2 i = (pulseN 5).2 i) ∧
    (∀ k : Fin 6, k.val ≠ 0 →
      (∃ i, (iterN (step ringX) k.val (pulseN 5)).1 i ≠ (pulseN 5).1 i) ∨
      (∃ i, (iterN (step ringX) k.val (pulseN 5)).2 i ≠ (pulseN 5).2 i)) := by
  decide

/-- Fixed ends on three sites: state period 8 (2n + 2). -/
theorem dirichlet3_period_eight :
    (∀ i, (iterN (step dirichletX) 8 (pulseN 2)).1 i = (pulseN 2).1 i) ∧
    (∀ i, (iterN (step dirichletX) 8 (pulseN 2)).2 i = (pulseN 2).2 i) ∧
    (∀ k : Fin 8, k.val ≠ 0 →
      (∃ i, (iterN (step dirichletX) k.val (pulseN 2)).1 i
        ≠ (pulseN 2).1 i) ∨
      (∃ i, (iterN (step dirichletX) k.val (pulseN 2)).2 i
        ≠ (pulseN 2).2 i)) := by
  decide

/-- Fixed ends on five sites: state period 12 (2n + 2). -/
theorem dirichlet5_period_twelve :
    (∀ i, (iterN (step dirichletX) 12 (pulseN 4)).1 i = (pulseN 4).1 i) ∧
    (∀ i, (iterN (step dirichletX) 12 (pulseN 4)).2 i = (pulseN 4).2 i) ∧
    (∀ k : Fin 12, k.val ≠ 0 →
      (∃ i, (iterN (step dirichletX) k.val (pulseN 4)).1 i
        ≠ (pulseN 4).1 i) ∨
      (∃ i, (iterN (step dirichletX) k.val (pulseN 4)).2 i
        ≠ (pulseN 4).2 i)) := by
  decide

#print axioms Experimental.Wave.xor_cancel
#print axioms Experimental.Wave.swap_involution
#print axioms Experimental.Wave.reverse_is_swapped_pair
#print axioms Experimental.Wave.shear_involution_pointwise
#print axioms Experimental.Wave.step_eq_two_bounce
#print axioms Experimental.Wave.reverse_step_pointwise
#print axioms Experimental.Wave.reverse_step
#print axioms Experimental.Wave.step_lossless
#print axioms Experimental.Wave.ring4_period_four
#print axioms Experimental.Wave.dirichlet4_period_ten
#print axioms Experimental.Wave.waveFactor
#print axioms Experimental.Wave.iterN_succ_out
#print axioms Experimental.Wave.fin_sub_one_add_one
#print axioms Experimental.Wave.fin_add_one_sub_one
#print axioms Experimental.Wave.ringX_rot_pointwise
#print axioms Experimental.Wave.ringX_rotInv_pointwise
#print axioms Experimental.Wave.step_rot_pointwise
#print axioms Experimental.Wave.step_rotInv_pointwise
#print axioms Experimental.Wave.step_ringX_congr
#print axioms Experimental.Wave.iterN_step_ringX_congr
#print axioms Experimental.Wave.iterN_step_rot_pointwise
#print axioms Experimental.Wave.iterN_step_rotInv_pointwise
#print axioms Experimental.Wave.return_rot_pointwise
#print axioms Experimental.Wave.return_rotInv_pointwise
#print axioms Experimental.Wave.return_of_rot_return
#print axioms Experimental.Wave.return_iff_rot_return
#print axioms Experimental.Wave.ring2_period_two
#print axioms Experimental.Wave.ring3_period_six
#print axioms Experimental.Wave.ring5_period_ten
#print axioms Experimental.Wave.ring6_period_six
#print axioms Experimental.Wave.dirichlet3_period_eight
#print axioms Experimental.Wave.dirichlet5_period_twelve

end Experimental.Wave
