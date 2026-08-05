import PeriodSpectrum

/-!
# Frequencies (EXPERIMENTAL: quarantined; exports nothing to the paper)

The core of this probe has been promoted to `Bridge.PeriodSpectrum`:
the shift, the iterate, the general gcd law `order_eq_div_gcd` with
its displacement formula and both halves, and the twelve-carrier
exhibits (`interval_addition`, `harmonics_are_iterates`,
`orders_twelve`, `circle_of_fifths`). This module re-exports those
names under `Experimental.Frequencies` so downstream experiments keep
compiling, and it retains the quarantined remainder:

* `fifth_generates`: the fifth reaches every pitch class from every
  starting point within twelve steps, decidably.
* `order_eq_div_gcd_twelve`: the return half of the gcd law checked
  pointwise on the twelve-carrier by decision procedure, independent
  of the general law.
* `order_eq_div_gcd_twelve_general`: the twelve-carrier gcd law
  rederived as an instance of the promoted general theorem, with the
  minimality half the pointwise check did not state.
* `circle_of_fifths_minimal`: below twelve no positive iterate of the
  fifth fixes any point, from the general law.
-/
namespace Experimental.Frequencies

export Bridge.PeriodSpectrum (shift iterN semitone fifth
  interval_addition harmonics_are_iterates orders_twelve
  circle_of_fifths iterN_succ shift_val iterN_shift_val
  iterN_shift_eq_self_iff shift_order_pos shift_order_returns
  shift_order_minimal order_eq_div_gcd)

/-- The fifth reaches every pitch class from every starting point
    within twelve steps: its orbit is the entire carrier, decidably.
    This is the generation fact behind the circle of fifths. -/
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

#print axioms Experimental.Frequencies.fifth_generates
#print axioms Experimental.Frequencies.order_eq_div_gcd_twelve
#print axioms Experimental.Frequencies.order_eq_div_gcd_twelve_general
#print axioms Experimental.Frequencies.circle_of_fifths_minimal

end Experimental.Frequencies
