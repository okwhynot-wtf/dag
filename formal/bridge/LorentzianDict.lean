import Expansion
import OneZ2
import Alphabet
import Capacity
import Obs.Dimension
import Obs.CausalOrder
import Density

/-!
# Partial Lorentzian dictionary (no Lorentz group)

What the corpus can say with order dimension 1 + capacity growth,
without boosts / Unruh temperature / continuum Lorentzian metric.

Ingredients:
* causal ascent order has combinatorial dimension 1
* capacity / counted volume grows as `K^t` under `NumberEqualsVolume`
* only ℤ/2 underdetermination (T-7) — no continuous boost orbit (O-2)

Not a Lorentzian metric, not Malament reconstruction, not Unruh `T`,
not continuum O-4. Separate from the structural O-2 gap.
-/

namespace Bridge.LorentzianDict

open Bridge.Expansion
open Bridge.OneZ2

/-- Causal ascent is combinatorially 1-dimensional (a chain). -/
theorem order_dim_one (tTurn : Nat) :
    Obs.Dimension.OrderDimEq tTurn
      (Obs.CausalOrder.fwdPrecedes tTurn) 1 :=
  Obs.Dimension.ascent_order_dim_eq_one tTurn

/-- Counted volume / capacity growth at `K = 2` (one bit per tick). -/
theorem counted_volume_growth (T : Nat) :
    countedVolume 2 (T + 1) = 2 * countedVolume 2 T :=
  discrete_Hubble_one_bit_per_tick numberEqualsVolume T

/-- Underdetermination is only ℤ/2 — no continuous boost family. -/
theorem only_Z2_underdetermination :
    (∀ f b, project f (project f b) = b) ∧
    Bridge.Alphabet.Kmin = 2 :=
  ⟨project_involution, Bridge.Alphabet.Kmin_eq⟩

/-- Continuum Lorentzian limit is not derived (O-4 marker). -/
def continuum_lorentzian_refused : True := True.intro

/-- Boost / Unruh temperature is not derived (O-2 marker). -/
def boost_Unruh_open : True := True.intro

/-- ω-shaped capacity clock: caps and levelCard keep growing. -/
theorem omega_shape_echo :
    (∀ T, Bridge.Capacity.caps T = 2 ^ (T + 2)) ∧
    (∀ k, Density.levelCard k = k + 2) :=
  ⟨Bridge.Capacity.caps_eq, Bridge.Capacity.levelCard_eq⟩

/-- **Partial Lorentzian dictionary.** Order dim-1 + capacity growth +
    ℤ/2-only underdetermination. Not a Lorentz group; O-2/O-4 remain. -/
theorem partial_lorentzian_dictionary :
    (∀ tTurn, Obs.Dimension.OrderDimEq tTurn
      (Obs.CausalOrder.fwdPrecedes tTurn) 1) ∧
    NumberEqualsVolume ∧
    (∀ T, countedVolume 2 (T + 1) = 2 * countedVolume 2 T) ∧
    (∀ f b, project f (project f b) = b) ∧
    continuum_lorentzian_refused = True.intro ∧
    boost_Unruh_open = True.intro ∧
    Bridge.Alphabet.Kmin = 2 :=
  ⟨order_dim_one, number_equals_volume_flagged,
   counted_volume_growth, project_involution, rfl, rfl,
   Bridge.Alphabet.Kmin_eq⟩

#print axioms order_dim_one
#print axioms counted_volume_growth
#print axioms partial_lorentzian_dictionary

end Bridge.LorentzianDict
