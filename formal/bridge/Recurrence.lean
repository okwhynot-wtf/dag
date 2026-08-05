import WaveDynamics

/-!
# Recurrence: finite-orbit return for the Z/2 wave, within capacity

Promoted from the experimental `Recurrence` probe. The wave step is
lossless for every coupling (`WaveDynamics.step_lossless`) and the
carrier is finite, so no orbit can leak: every state returns exactly,
for every coupling `X` and every carrier size `n`, within the
state-space capacity `2^n · 2^n = 2^(2n)` steps. Results:

* **Binary encoding** (`encodeF`, `encodeF_lt`, `encodeF_inj`): a
  field reads as a Nat below `2^n` by positional binary. Uniqueness
  of binary digits is proved by splitting the lowest bit (parity)
  and recursing on the tail. Injectivity is stated pointwise on
  sites.
* **State encoding** (`encodeS`, `encodeS_lt`, `encodeS_inj`): the
  two layers pair by base-`2^n` positional arithmetic into a Nat
  below `2^n · 2^n`; injectivity is div/mod uniqueness, again
  landing in pointwise form on both layers.
* **Constructive pigeonhole** (`exists_collision`): a Nat sequence
  bounded by `C` repeats inside the window `0 … C`. The proof is by
  induction on the bound with a decidable bounded search at each
  stage: either some earlier index already collides with the top
  index, or the top value redirects one value of the window and the
  induction hypothesis applies. The experimental version extracted
  the witness classically from the spine pigeonhole; this promoted
  version is choice-free, as the promotion gate for this module
  requires, and `Classical.choice` does not appear in its footprint.
* **Recurrence** (`wave_recurrence_bounded`, `wave_recurrence`,
  `wave_recurrence_pow`): losslessness cancels the common prefix
  of the two colliding orbit points, leaving an exact return at
  the difference time `p` with `0 < p ≤ 2^n · 2^n = 2^(2n)`. The
  wave cannot leak, and its recurrence time is capped by the
  carrier capacity. The returns themselves are stated pointwise on
  both layers.

Footprint note. The colliding states are packaged into a
function-level equality with `funext` and `Prod.ext` before the
cancellation, so the recurrence theorems carry propext and
`Quot.sound`; that use of function extensionality is recorded here
and in `AXIOMS.md`. The use is essential for the general statement:
the coupling `X` is an arbitrary functional on fields, and applying
it to two pointwise-equal layers is related only through function
equality. No proof in this module uses `Classical.choice`.

Capacity language only: the recurrence time is capped by the
carrier capacity `2^(2n)`. No ledger claim is made.

Documented target (out of scope here): the closed-form pulse
period law on the ring (`n` even maps to `n`, `n` odd maps to `2n`),
which needs polynomial algebra over GF(2) that this file does not
build. The finite instances remain in the experimental
`WaveEquation` module.
-/
namespace Bridge.Recurrence

open Bridge.WaveDynamics
open Bridge.TwoBounce (EndoInj)

/-! ## Binary encoding of a field -/

/-- Positional binary value of the first `m` bits of a Nat-indexed
    bit stream: `encodeAux g m = Σ_{j<m} 2^j · (g j).toNat`, folded
    with the lowest bit outermost. -/
def encodeAux : (Nat → Bool) → Nat → Nat
  | _, 0 => 0
  | g, m + 1 => (g 0).toNat + 2 * encodeAux (fun j => g (j + 1)) m

/-- Unfolding equation for `encodeAux` at a successor length. -/
theorem encodeAux_succ (g : Nat → Bool) (m : Nat) :
    encodeAux g (m + 1)
      = (g 0).toNat + 2 * encodeAux (fun j => g (j + 1)) m := rfl

/-- Lowest-bit split: if `a.toNat + 2x = b.toNat + 2y` then the bits
    agree (parity) and the tails agree (cancel the doubled part). -/
private theorem bit_cancel {a b : Bool} {x y : Nat}
    (h : a.toNat + 2 * x = b.toNat + 2 * y) : a = b ∧ x = y := by
  have h0 : Bool.toNat false = 0 := rfl
  have h1 : Bool.toNat true = 1 := rfl
  cases a <;> cases b <;> simp only [h0, h1] at h
  · exact ⟨rfl, by omega⟩
  · exact False.elim (by omega)
  · exact False.elim (by omega)
  · exact ⟨rfl, by omega⟩

/-- The binary value of `m` bits is below `2^m`. -/
theorem encodeAux_lt : ∀ (m : Nat) (g : Nat → Bool),
    encodeAux g m < 2 ^ m := by
  intro m
  induction m with
  | zero => intro g; exact Nat.zero_lt_one
  | succ m ih =>
    intro g
    have ht := ih (fun j => g (j + 1))
    have hb : (g 0).toNat ≤ 1 := by cases g 0 <;> decide
    have hp : 2 ^ (m + 1) = 2 ^ m * 2 := by rw [Nat.pow_succ]
    rw [encodeAux_succ]
    omega

/-- Binary-positional uniqueness: equal values force equal bits at
    every index below the length. Lowest bit by parity, tail by
    recursion. -/
theorem encodeAux_inj : ∀ (m : Nat) (g h : Nat → Bool),
    encodeAux g m = encodeAux h m → ∀ j, j < m → g j = h j := by
  intro m
  induction m with
  | zero =>
    intro g h _ j hj
    exact absurd hj (Nat.not_lt_zero j)
  | succ m ih =>
    intro g h heq j hj
    rw [encodeAux_succ, encodeAux_succ] at heq
    have hb := bit_cancel heq
    cases j with
    | zero => exact hb.1
    | succ j =>
      exact ih (fun t => g (t + 1)) (fun t => h (t + 1)) hb.2 j
        (Nat.lt_of_succ_lt_succ hj)

/-- A field as a Nat below `2^n`: read the sites through the padded
    lookup `WaveDynamics.wallAt` and take the positional binary
    value. -/
def encodeF {n : Nat} (c : Field n) : Nat :=
  encodeAux (fun m => wallAt c m) n

/-- The field code is below the layer capacity `2^n`. -/
theorem encodeF_lt {n : Nat} (c : Field n) : encodeF c < 2 ^ n :=
  encodeAux_lt n (fun m => wallAt c m)

/-- Pointwise injectivity of the field code: equal codes force equal
    poles at every site. -/
theorem encodeF_inj {n : Nat} (c c' : Field n)
    (h : encodeF c = encodeF c') : ∀ i, c i = c' i := by
  intro i
  have hw : wallAt c i.val = wallAt c' i.val :=
    encodeAux_inj n (fun m => wallAt c m) (fun m => wallAt c' m) h
      i.val i.isLt
  have hc : wallAt c i.val = c i := dif_pos i.isLt
  have hc' : wallAt c' i.val = c' i := dif_pos i.isLt
  rw [← hc, ← hc']
  exact hw

/-! ## Pairing the two layers -/

/-- Powers of two are positive (local, to keep the file core-only). -/
private theorem two_pow_pos : ∀ n : Nat, 0 < 2 ^ n := by
  intro n
  induction n with
  | zero => exact Nat.zero_lt_one
  | succ n ih =>
    have h : 2 ^ (n + 1) = 2 ^ n * 2 := by rw [Nat.pow_succ]
    omega

/-- A state as a Nat below `2^n · 2^n`: the previous layer is the
    low block, the current layer the high block, base `2^n`. -/
def encodeS {n : Nat} (s : WState n) : Nat :=
  encodeF s.1 + 2 ^ n * encodeF s.2

/-- The state code is below the state-space capacity `2^n · 2^n`. -/
theorem encodeS_lt {n : Nat} (s : WState n) :
    encodeS s < 2 ^ n * 2 ^ n := by
  have h1 := encodeF_lt s.1
  have h2 := encodeF_lt s.2
  calc encodeS s
      = encodeF s.1 + 2 ^ n * encodeF s.2 := rfl
    _ < 2 ^ n + 2 ^ n * encodeF s.2 := Nat.add_lt_add_right h1 _
    _ = 2 ^ n * (encodeF s.2 + 1) := by
        rw [Nat.mul_add, Nat.mul_one, Nat.add_comm]
    _ ≤ 2 ^ n * 2 ^ n := Nat.mul_le_mul (Nat.le_refl (2 ^ n)) h2

/-- Pointwise injectivity of the state code: equal codes force equal
    poles at every site of both layers (div/mod uniqueness in base
    `2^n`). -/
theorem encodeS_inj {n : Nat} (s t : WState n)
    (h : encodeS s = encodeS t) :
    (∀ i, s.1 i = t.1 i) ∧ (∀ i, s.2 i = t.2 i) := by
  have hu : encodeF s.1 + 2 ^ n * encodeF s.2
      = encodeF t.1 + 2 ^ n * encodeF t.2 := h
  have h1 := encodeF_lt s.1
  have h2 := encodeF_lt t.1
  have hlow : encodeF s.1 = encodeF t.1 := by
    have e1 : (encodeF s.1 + 2 ^ n * encodeF s.2) % 2 ^ n
        = encodeF s.1 := by
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h1]
    have e2 : (encodeF t.1 + 2 ^ n * encodeF t.2) % 2 ^ n
        = encodeF t.1 := by
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h2]
    rw [← e1, ← e2, hu]
  rw [hlow] at hu
  have hhigh : encodeF s.2 = encodeF t.2 :=
    Nat.eq_of_mul_eq_mul_left (two_pow_pos n) (Nat.add_left_cancel hu)
  exact ⟨encodeF_inj s.1 t.1 hlow, encodeF_inj s.2 t.2 hhigh⟩

/-! ## Iterate bookkeeping

Two facts about `WaveDynamics.iterN` (the head-first fold): iterates
add by composition, and injectivity of the step lifts to every
iterate. -/

/-- Splitting an iterate: `a + b` steps are `a` steps then `b`. -/
theorem iterN_add {α : Type} (f : α → α) (a b : Nat) (s : α) :
    iterN f (a + b) s = iterN f b (iterN f a s) := by
  induction a generalizing s with
  | zero =>
    rw [Nat.zero_add]
    rfl
  | succ a ih =>
    have h : a + 1 + b = (a + b) + 1 := by omega
    rw [h]
    show iterN f (a + b) (f s) = iterN f b (iterN f a (f s))
    exact ih (f s)

/-- Injectivity of the step lifts to every iterate. -/
theorem iterN_inj {α : Type} (f : α → α) (hf : EndoInj f) :
    ∀ (m : Nat) (a b : α), iterN f m a = iterN f m b → a = b := by
  intro m
  induction m with
  | zero => intro a b h; exact h
  | succ m ih =>
    intro a b h
    exact hf a b (ih (f a) (f b) h)

/-! ## Constructive pigeonhole on the coded orbit -/

/-- Bounded search below an inclusive bound: a pointwise decidable
    property either holds at some index `j ≤ n` or fails at every
    index `j ≤ n`. Constructive, by induction on the bound. -/
private theorem search_le (P : Nat → Prop)
    [inst : ∀ j, Decidable (P j)] :
    ∀ n : Nat, (∃ j, j ≤ n ∧ P j) ∨ (∀ j, j ≤ n → ¬ P j) := by
  intro n
  induction n with
  | zero =>
    cases inst 0 with
    | isTrue h => exact Or.inl ⟨0, Nat.le_refl 0, h⟩
    | isFalse h =>
      refine Or.inr ?_
      intro j hj
      have hj0 : j = 0 := Nat.le_zero.mp hj
      rw [hj0]
      exact h
  | succ n ih =>
    cases inst (n + 1) with
    | isTrue h => exact Or.inl ⟨n + 1, Nat.le_refl (n + 1), h⟩
    | isFalse h =>
      cases ih with
      | inl hex =>
        obtain ⟨j, hj, hp⟩ := hex
        exact Or.inl ⟨j, Nat.le_succ_of_le hj, hp⟩
      | inr hall =>
        refine Or.inr ?_
        intro j hj
        cases Nat.lt_or_ge j (n + 1) with
        | inl hlt => exact hall j (Nat.le_of_lt_succ hlt)
        | inr hge =>
          have hj1 : j = n + 1 := Nat.le_antisymm hj hge
          rw [hj1]
          exact h

/-- Constructive pigeonhole on an inclusive window: if `f` maps every
    index `t ≤ C` to a value below `C`, two indices `t1 < t2 ≤ C`
    carry the same value. Induction on `C`: either the bounded search
    finds an earlier index colliding with the top index, or the top
    value redirects the value `C - 1` inside the window and the
    induction hypothesis applies to the redirected sequence. -/
private theorem pigeon_window :
    ∀ (C : Nat) (f : Nat → Nat), (∀ t, t ≤ C → f t < C) →
      ∃ t1 t2, t1 < t2 ∧ t2 ≤ C ∧ f t1 = f t2 := by
  intro C
  induction C with
  | zero =>
    intro f hb
    exact absurd (hb 0 (Nat.le_refl 0)) (Nat.not_lt_zero (f 0))
  | succ n ih =>
    intro f hb
    cases search_le (fun j => f j = f (n + 1)) n with
    | inl hex =>
      obtain ⟨j, hj, hp⟩ := hex
      exact ⟨j, n + 1, Nat.lt_succ_of_le hj, Nat.le_refl (n + 1), hp⟩
    | inr hall =>
      have hg : ∀ t, t ≤ n →
          (if f t = n then f (n + 1) else f t) < n := by
        intro t ht
        cases Nat.decEq (f t) n with
        | isTrue heq =>
          rw [if_pos heq]
          have h1 : f (n + 1) < n + 1 := hb (n + 1) (Nat.le_refl (n + 1))
          have h2 : f (n + 1) ≠ n := by
            intro hcontra
            exact hall t ht (heq.trans hcontra.symm)
          omega
        | isFalse hne =>
          rw [if_neg hne]
          have h1 : f t < n + 1 := hb t (Nat.le_succ_of_le ht)
          omega
      obtain ⟨t1, t2, hlt, hle, heq⟩ :=
        ih (fun t => if f t = n then f (n + 1) else f t) hg
      cases Nat.decEq (f t1) n with
      | isTrue h1 =>
        cases Nat.decEq (f t2) n with
        | isTrue h2 =>
          exact ⟨t1, t2, hlt, Nat.le_succ_of_le hle, h1.trans h2.symm⟩
        | isFalse h2 =>
          rw [if_pos h1, if_neg h2] at heq
          exact absurd heq.symm (hall t2 hle)
      | isFalse h1 =>
        cases Nat.decEq (f t2) n with
        | isTrue h2 =>
          rw [if_neg h1, if_pos h2] at heq
          exact absurd heq
            (hall t1 (Nat.le_of_lt (Nat.lt_of_lt_of_le hlt hle)))
        | isFalse h2 =>
          rw [if_neg h1, if_neg h2] at heq
          exact ⟨t1, t2, hlt, Nat.le_succ_of_le hle, heq⟩

/-- A Nat sequence bounded by `C` collides inside the window `0 … C`:
    two indices `t1 < t2 ≤ C` carry the same value. Constructive; the
    experimental predecessor of this theorem extracted the witness by
    `Classical.byContradiction`, and this proof replaces that step
    with the bounded-search pigeonhole `pigeon_window`, so
    `Classical.choice` does not enter the bridge. -/
theorem exists_collision (C : Nat) (f : Nat → Nat)
    (hb : ∀ t, f t < C) :
    ∃ t1 t2, t1 < t2 ∧ t2 ≤ C ∧ f t1 = f t2 :=
  pigeon_window C f (fun t _ => hb t)

/-! ## Finite-orbit return at Z/2 -/

/-- **Recurrence within capacity.** Every wave state on every finite
    carrier returns exactly, for every coupling `X`, at some
    positive time `p ≤ 2^n · 2^n`: the coded orbit is bounded by
    the capacity, so it collides inside the window `0 … 2^n · 2^n`;
    the colliding states are equal (pointwise injectivity of the
    code, packaged to function equality with `funext` and
    `Prod.ext`); and losslessness (`WaveDynamics.step_lossless`)
    cancels the common prefix, leaving the return at the difference
    time. The returns are stated pointwise on both layers. -/
theorem wave_recurrence_bounded {n : Nat}
    (X : Field n → Fin n → Bool) (s : WState n) :
    ∃ p, 0 < p ∧ p ≤ 2 ^ n * 2 ^ n ∧
      (∀ i, (iterN (step X) p s).1 i = s.1 i) ∧
      (∀ i, (iterN (step X) p s).2 i = s.2 i) := by
  obtain ⟨t1, t2, hlt, hle, hcode⟩ :=
    exists_collision (2 ^ n * 2 ^ n)
      (fun t => encodeS (iterN (step X) t s))
      (fun t => encodeS_lt (iterN (step X) t s))
  have hpw := encodeS_inj (iterN (step X) t1 s) (iterN (step X) t2 s)
    hcode
  have hstate : iterN (step X) t1 s = iterN (step X) t2 s :=
    Prod.ext (funext hpw.1) (funext hpw.2)
  have hsplit : t2 - t1 + t1 = t2 :=
    Nat.sub_add_cancel (Nat.le_of_lt hlt)
  have hadd : iterN (step X) (t2 - t1 + t1) s
      = iterN (step X) t1 (iterN (step X) (t2 - t1) s) :=
    iterN_add (step X) (t2 - t1) t1 s
  rw [hsplit] at hadd
  have hcancel : iterN (step X) (t2 - t1) s = s := by
    apply iterN_inj (step X) (step_lossless X) t1
    rw [← hadd, ← hstate]
  refine ⟨t2 - t1, ?_, ?_, ?_, ?_⟩
  · omega
  · omega
  · exact fun i => congrArg (fun w : WState n => w.1 i) hcancel
  · exact fun i => congrArg (fun w : WState n => w.2 i) hcancel

/-- **Finite-orbit return at Z/2.** Every wave state on every finite
    carrier returns, for every coupling `X`: losslessness plus
    finite capacity forces a bounded return, so the wave cannot
    leak. The bound-free form of `wave_recurrence_bounded`. -/
theorem wave_recurrence {n : Nat}
    (X : Field n → Fin n → Bool) (s : WState n) :
    ∃ p, 0 < p ∧
      (∀ i, (iterN (step X) p s).1 i = s.1 i) ∧
      (∀ i, (iterN (step X) p s).2 i = s.2 i) := by
  obtain ⟨p, hp, _, h1, h2⟩ := wave_recurrence_bounded X s
  exact ⟨p, hp, h1, h2⟩

/-- The capacity in exponent form: `2^n · 2^n = 2^(2n)`. -/
theorem capacity_eq (n : Nat) : 2 ^ n * 2 ^ n = 2 ^ (2 * n) := by
  rw [Nat.two_mul, Nat.pow_add]

/-- Recurrence with the capacity written as `2^(2n)`: the recurrence
    time is capped by the number of states of the carrier. -/
theorem wave_recurrence_pow {n : Nat}
    (X : Field n → Fin n → Bool) (s : WState n) :
    ∃ p, 0 < p ∧ p ≤ 2 ^ (2 * n) ∧
      (∀ i, (iterN (step X) p s).1 i = s.1 i) ∧
      (∀ i, (iterN (step X) p s).2 i = s.2 i) := by
  obtain ⟨p, hp, hle, h1, h2⟩ := wave_recurrence_bounded X s
  refine ⟨p, hp, ?_, h1, h2⟩
  rw [← capacity_eq]
  exact hle

#print axioms Bridge.Recurrence.encodeAux_succ
#print axioms Bridge.Recurrence.bit_cancel
#print axioms Bridge.Recurrence.encodeAux_lt
#print axioms Bridge.Recurrence.encodeAux_inj
#print axioms Bridge.Recurrence.encodeF_lt
#print axioms Bridge.Recurrence.encodeF_inj
#print axioms Bridge.Recurrence.two_pow_pos
#print axioms Bridge.Recurrence.encodeS_lt
#print axioms Bridge.Recurrence.encodeS_inj
#print axioms Bridge.Recurrence.iterN_add
#print axioms Bridge.Recurrence.iterN_inj
#print axioms Bridge.Recurrence.search_le
#print axioms Bridge.Recurrence.pigeon_window
#print axioms Bridge.Recurrence.exists_collision
#print axioms Bridge.Recurrence.wave_recurrence_bounded
#print axioms Bridge.Recurrence.wave_recurrence
#print axioms Bridge.Recurrence.capacity_eq
#print axioms Bridge.Recurrence.wave_recurrence_pow

end Bridge.Recurrence
