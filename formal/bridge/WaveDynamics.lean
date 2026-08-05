import TwoBounce

/-!
# WaveDynamics: the second-order Z/2 field equation and its two-bounce form

Promoted from the experimental `WaveEquation` probe. The discrete
d'Alembert form `u(t+1) = u(t-1) + Δu(t)` becomes, over `Bool` with
addition as xor, a second-order field equation
`next i = prev i ^^ X cur i`, with the spatial coupling `X` left
completely general. Results:

* **Two-bounce in closed form** (`step_eq_two_bounce`): the wave step
  equals `swap ∘ shear` definitionally, with both factors involutive.
  The corpus's factorisation theorem holds here by explicit
  construction, with the pair exhibited.
* **Time reversal is the bounce swap** (`reverse_is_swapped_pair`,
  `reverse_step_pointwise`): the inverse evolution is presented by the
  swapped pair `shear ∘ swap`, which instantiates the corpus's
  swap-equals-reversal at field level. The pointwise cancellation is
  axiom-free.
* **Losslessness for every coupling** (`step_lossless`): no two
  histories merge, for every coupling `X` and every carrier size.
* **Boundary conditions select the spectrum** (`ring4_period_four`,
  `dirichlet4_period_ten`): with the same rule and the same
  single-pulse initial state, the ring of four returns at period 4 and
  the fixed-end line of four returns at period 10, each decided by the
  kernel. Boundary alone reshapes the spectrum.

Footprint split, preserved deliberately: the pointwise theorems
(`xor_cancel`, `swap_involution`, `shear_involution_pointwise`,
`reverse_is_swapped_pair`, `reverse_step_pointwise`) and
`step_eq_two_bounce` are axiom-free; the packaged theorems
`reverse_step` and `step_lossless` lift the pointwise lemmas to
function-level equality through `funext` and `Prod.ext` and therefore
carry `Quot.sound`; the two kernel-decided period theorems carry
propext and `Quot.sound` through the `Decidable` instances. The
packaged theorems are proved directly from the pointwise ones so that
the extensionality use stays in daylight; the split is part of the
result.

The quarantined remainder of the probe (translation symmetry of the
ring, the rotation-orbit invariance of the return spectrum, the period
table beyond four sites, and the packaged `TwoBounceFactor` witness)
stays in `formal/experimental/WaveEquation.lean`.
-/
namespace Bridge.WaveDynamics

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

/-- Packaged reversal. Uses function extensionality (`Quot.sound`);
    the lift from the pointwise lemma is made in daylight through
    `funext` and `Prod.ext`. -/
theorem reverse_step (X : Field n → Fin n → Bool) (s : WState n) :
    reverse X (step X s) = s := by
  have h := reverse_step_pointwise X s
  exact Prod.ext (funext h.1) (funext h.2.1)

/-- The wave evolution is lossless for every coupling and every size:
    no two histories merge. Inherits the function-extensionality
    footprint of `reverse_step`. -/
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

#print axioms Bridge.WaveDynamics.xor_cancel
#print axioms Bridge.WaveDynamics.swap_involution
#print axioms Bridge.WaveDynamics.shear_involution_pointwise
#print axioms Bridge.WaveDynamics.step_eq_two_bounce
#print axioms Bridge.WaveDynamics.reverse_is_swapped_pair
#print axioms Bridge.WaveDynamics.reverse_step_pointwise
#print axioms Bridge.WaveDynamics.reverse_step
#print axioms Bridge.WaveDynamics.step_lossless
#print axioms Bridge.WaveDynamics.ring4_period_four
#print axioms Bridge.WaveDynamics.dirichlet4_period_ten

end Bridge.WaveDynamics
