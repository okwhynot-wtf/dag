/-!
# Frequencies (EXPERIMENTAL — quarantined; exports nothing to the paper)

Probe: frequency and ratio without a continuum. On a finite carrier the
honest surrogate for frequency is *order*: the k-th harmonic is the
shift by k, its frequency is the least period, and order ratios stand in
for frequency ratios. On the twelve-carrier
(the chromatic circle) the classical facts become decidable:
composition of intervals adds shifts, the whole-tone has order 6, the
major third order 3, the tritone order 2, and the fifth generates the
entire carrier (`fifth_generates`; the circle of fifths closes after
twelve steps and not before).

The general gcd law is proved: on `Fin n` the order of `shift k` is
`n / gcd n k` (`order_eq_div_gcd`). The displacement formula
`iterN_shift_val` reduces the fixed-point condition to divisibility of
the total displacement by the carrier size
(`iterN_shift_eq_self_iff`); the return half is gcd cancellation
(`shift_order_returns`) and the minimality half is Euclid's lemma on
the coprime quotients (`shift_order_minimal`). The edge `k = 0` is an
instance: `gcd n 0 = n` gives order one and the shift is the
identity. All statements are pointwise on carrier elements; no
function extensionality is used. The twelve-carrier facts remain
verified independently by decision procedure, and the instance of the
general law on twelve (`order_eq_div_gcd_twelve_general`,
`circle_of_fifths_minimal`) adds the minimality half the pointwise
check did not state.
-/
namespace Experimental.Frequencies

/-- Shift by `k`: the `k`-th harmonic on the carrier `Fin n`. -/
def shift {n : Nat} (k : Fin n) : Fin n → Fin n := fun i => i + k

/-- Iterate. -/
def iterN {α : Type} (f : α → α) : Nat → α → α
  | 0, a => a
  | m + 1, a => iterN f m (f a)

/-! ## The twelve-carrier -/

/-- The fundamental step on the chromatic circle. -/
def semitone : Fin 12 → Fin 12 := shift 1

/-- The fifth. -/
def fifth : Fin 12 → Fin 12 := shift 7

/-- Interval composition adds shifts: shift arithmetic on the
    twelve-carrier, decidably. -/
theorem interval_addition :
    ∀ (j k : Fin 12) (i : Fin 12),
      shift j (shift k i) = shift (k + j) i := by
  decide

/-- Every harmonic is an iterate of the fundamental: the k-th overtone
    is k beats of the semitone. -/
theorem harmonics_are_iterates :
    ∀ (k : Fin 12) (i : Fin 12),
      iterN semitone k.val i = shift k i := by
  decide

/-- Return checks on the twelve-carrier: the whole tone returns at 6,
    the minor third at 4, the major third at 3, the tritone at 2, the
    semitone and the fifth at 12. Return half only; that these counts
    are the exact orders (minimality) is an instance of the general
    law (`order_eq_div_gcd_twelve_general`). -/
theorem orders_twelve :
    (∀ i, iterN (shift (2 : Fin 12)) 6 i = i) ∧
    (∀ i, iterN (shift (3 : Fin 12)) 4 i = i) ∧
    (∀ i, iterN (shift (4 : Fin 12)) 3 i = i) ∧
    (∀ i, iterN (shift (6 : Fin 12)) 2 i = i) ∧
    (∀ i, iterN semitone 12 i = i) ∧
    (∀ i, iterN fifth 12 i = i) := by
  decide

/-- The circle of fifths closes after twelve steps and at no positive
    step before: the fifth is a generator, so its order is twelve and its shift is
    seven. -/
theorem circle_of_fifths :
    (∀ i, iterN fifth 12 i = i) ∧
    (∀ k : Fin 12, k.val ≠ 0 → ∃ i, iterN fifth k.val i ≠ i) := by
  decide

/-- The fifth reaches every pitch class from every starting point
    within twelve steps: its orbit is the entire carrier, decidably —
    the generation fact behind the circle of fifths. -/
theorem fifth_generates :
    ∀ i j : Fin 12, ∃ t : Fin 12, iterN fifth t.val i = j := by
  decide

/-- Return half of the gcd law at every point of the twelve-carrier:
    `12 / gcd 12 k` beats of `shift k` restore every point, checked
    decidably. The minimality half is supplied by the general law
    (`order_eq_div_gcd_twelve_general`). -/
theorem order_eq_div_gcd_twelve :
    ∀ k : Fin 12, ∀ i : Fin 12,
      iterN (shift k) (12 / Nat.gcd 12 k.val) i = i := by
  decide

/-! ## The general gcd law -/

/-- Head-first unfolding of the iterate: one application peels off on
    the outside. `iterN` folds head-first by definition; this is the
    tail-first equation. -/
theorem iterN_succ {α : Type} (f : α → α) :
    ∀ (m : Nat) (a : α), iterN f (m + 1) a = f (iterN f m a) := by
  intro m
  induction m with
  | zero => intro a; rfl
  | succ p ih => intro a; exact ih (f a)

/-- Value of a shift: addition modulo the carrier size. -/
theorem shift_val {n : Nat} (k i : Fin n) :
    (shift k i).val = (i.val + k.val) % n :=
  Fin.val_add i k

/-- Displacement formula: `m` beats of the `k`-th harmonic land at
    `(i + m·k) mod n`. -/
theorem iterN_shift_val {n : Nat} (k : Fin n) (m : Nat) (i : Fin n) :
    (iterN (shift k) m i).val = (i.val + m * k.val) % n := by
  induction m with
  | zero =>
    show i.val = (i.val + 0 * k.val) % n
    rw [Nat.zero_mul, Nat.add_zero, Nat.mod_eq_of_lt i.isLt]
  | succ p ih =>
    rw [iterN_succ, shift_val, ih, Nat.mod_add_mod, Nat.add_mul,
      Nat.one_mul, ← Nat.add_assoc]

/-- Adding `s` fixes a reduced residue `i < n` modulo `n` exactly when
    `s` vanishes modulo `n`. -/
private theorem add_mod_eq_self_iff {n i s : Nat} (hi : i < n) :
    (i + s) % n = i ↔ s % n = 0 := by
  have hn : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le i) hi
  constructor
  · intro h
    rw [Nat.add_mod, Nat.mod_eq_of_lt hi] at h
    have hr : s % n < n := Nat.mod_lt s hn
    revert h hr
    generalize s % n = r
    intro h hr
    cases Nat.lt_or_ge (i + r) n with
    | inl hlt =>
      rw [Nat.mod_eq_of_lt hlt] at h
      omega
    | inr hge =>
      have hlt2 : i + r - n < n := by omega
      rw [Nat.mod_eq_sub_mod hge, Nat.mod_eq_of_lt hlt2] at h
      omega
  · intro h
    rw [Nat.add_mod, h, Nat.add_zero, Nat.mod_eq_of_lt hi]
    exact Nat.mod_eq_of_lt hi

/-- Euclid step: if `n` divides `m * k`, the coprime part `n / gcd n k`
    divides `m`. The gcd is cancelled on both sides and Euclid's lemma
    applies to the coprime quotients. -/
private theorem div_gcd_dvd_of_dvd_mul {n k m : Nat} (hn : 0 < n)
    (h : n ∣ m * k) : n / Nat.gcd n k ∣ m := by
  have hg : 0 < Nat.gcd n k := Nat.gcd_pos_of_pos_left k hn
  have hgn : Nat.gcd n k ∣ n := Nat.gcd_dvd_left n k
  have hgk : Nat.gcd n k ∣ k := Nat.gcd_dvd_right n k
  have hco : Nat.Coprime (n / Nat.gcd n k) (k / Nat.gcd n k) :=
    Nat.coprime_div_gcd_div_gcd hg
  have h1 : Nat.gcd n k * (m * (k / Nat.gcd n k)) = m * k := by
    rw [Nat.mul_left_comm, Nat.mul_div_cancel' hgk]
  have h2 : Nat.gcd n k * (n / Nat.gcd n k) ∣
      Nat.gcd n k * (m * (k / Nat.gcd n k)) := by
    rw [Nat.mul_div_cancel' hgn, h1]
    exact h
  exact hco.dvd_of_dvd_mul_right ((Nat.mul_dvd_mul_iff_left hg).mp h2)

/-- A shift iterate fixes a point exactly when the carrier size divides
    the total displacement; the criterion is uniform in the point. -/
theorem iterN_shift_eq_self_iff {n : Nat} (k : Fin n) (m : Nat)
    (i : Fin n) :
    iterN (shift k) m i = i ↔ n ∣ m * k.val := by
  rw [← Fin.val_inj, iterN_shift_val]
  exact (add_mod_eq_self_iff i.isLt).trans Nat.dvd_iff_mod_eq_zero.symm

/-- The claimed order is positive: the gcd divides `n`, so the quotient
    is at least one. -/
theorem shift_order_pos {n : Nat} (k : Fin n) :
    0 < n / Nat.gcd n k.val :=
  Nat.div_pos (Nat.le_of_dvd k.pos (Nat.gcd_dvd_left n k.val))
    (Nat.gcd_pos_of_pos_left k.val k.pos)

/-- Return half of the gcd law: `n / gcd n k` beats of the `k`-th
    harmonic return every point, since `(n / gcd n k) · k` is the
    multiple `n · (k / gcd n k)` of the carrier size. -/
theorem shift_order_returns {n : Nat} (k : Fin n) (i : Fin n) :
    iterN (shift k) (n / Nat.gcd n k.val) i = i := by
  apply (iterN_shift_eq_self_iff k _ i).mpr
  have hgn : Nat.gcd n k.val ∣ n := Nat.gcd_dvd_left n k.val
  have hgk : Nat.gcd n k.val ∣ k.val := Nat.gcd_dvd_right n k.val
  have h1 : n / Nat.gcd n k.val * Nat.gcd n k.val *
      (k.val / Nat.gcd n k.val) = n / Nat.gcd n k.val * k.val := by
    rw [Nat.mul_assoc, Nat.mul_div_cancel' hgk]
  rw [← h1, Nat.div_mul_cancel hgn]
  exact Nat.dvd_mul_right n _

/-- Minimality half of the gcd law: below `n / gcd n k` no positive
    beat count fixes any point. A fixed point would force
    `n ∣ m · k`, hence `n / gcd n k ∣ m` by Euclid, hence
    `n / gcd n k ≤ m`. -/
theorem shift_order_minimal {n : Nat} (k : Fin n) {m : Nat}
    (hm : 0 < m) (hlt : m < n / Nat.gcd n k.val) (i : Fin n) :
    iterN (shift k) m i ≠ i := by
  intro h
  have hdvd : n ∣ m * k.val := (iterN_shift_eq_self_iff k m i).mp h
  have hle : n / Nat.gcd n k.val ≤ m :=
    Nat.le_of_dvd hm (div_gcd_dvd_of_dvd_mul k.pos hdvd)
  omega

/-- The gcd law on any finite carrier: the order of `shift k` on
    `Fin n` is `n / gcd n k` — the candidate period is positive, it
    returns every point, and no smaller positive beat count fixes any
    point. -/
theorem order_eq_div_gcd {n : Nat} (k : Fin n) :
    0 < n / Nat.gcd n k.val ∧
    (∀ i, iterN (shift k) (n / Nat.gcd n k.val) i = i) ∧
    (∀ m, 0 < m → m < n / Nat.gcd n k.val →
      ∀ i, iterN (shift k) m i ≠ i) :=
  ⟨shift_order_pos k, shift_order_returns k,
    fun _m hm hlt i => shift_order_minimal k hm hlt i⟩

/-- The twelve-carrier gcd law rederived as an instance of the general
    theorem, now with the minimality half the pointwise check
    (`order_eq_div_gcd_twelve`) did not state. -/
theorem order_eq_div_gcd_twelve_general (k : Fin 12) :
    (∀ i, iterN (shift k) (12 / Nat.gcd 12 k.val) i = i) ∧
    (∀ m, 0 < m → m < 12 / Nat.gcd 12 k.val →
      ∀ i, iterN (shift k) m i ≠ i) :=
  ⟨(order_eq_div_gcd k).2.1, (order_eq_div_gcd k).2.2⟩

/-- Strengthened circle of fifths from the general law: below twelve no
    positive iterate of the fifth fixes any point (`circle_of_fifths`
    exhibits only one moved point per step). -/
theorem circle_of_fifths_minimal :
    ∀ m, 0 < m → m < 12 → ∀ i, iterN fifth m i ≠ i := by
  have h12 : 12 / Nat.gcd 12 (7 : Fin 12).val = 12 := by decide
  intro m hm hlt i
  exact (order_eq_div_gcd (7 : Fin 12)).2.2 m hm
    (by rw [h12]; exact hlt) i

#print axioms Experimental.Frequencies.interval_addition
#print axioms Experimental.Frequencies.harmonics_are_iterates
#print axioms Experimental.Frequencies.orders_twelve
#print axioms Experimental.Frequencies.circle_of_fifths
#print axioms Experimental.Frequencies.fifth_generates
#print axioms Experimental.Frequencies.order_eq_div_gcd_twelve
#print axioms Experimental.Frequencies.iterN_succ
#print axioms Experimental.Frequencies.shift_val
#print axioms Experimental.Frequencies.iterN_shift_val
#print axioms Experimental.Frequencies.add_mod_eq_self_iff
#print axioms Experimental.Frequencies.div_gcd_dvd_of_dvd_mul
#print axioms Experimental.Frequencies.iterN_shift_eq_self_iff
#print axioms Experimental.Frequencies.shift_order_pos
#print axioms Experimental.Frequencies.shift_order_returns
#print axioms Experimental.Frequencies.shift_order_minimal
#print axioms Experimental.Frequencies.order_eq_div_gcd
#print axioms Experimental.Frequencies.order_eq_div_gcd_twelve_general
#print axioms Experimental.Frequencies.circle_of_fifths_minimal

end Experimental.Frequencies
