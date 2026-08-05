import Orthoset

/-!
# CompositeN — rank caps at two on every finite composite

Generalisation of `Composite`: take `n` fundamentals side by side,
carrier `Fin n → Bool`, with the `n` componentwise flips, and let
orthogonality be generated jointly by all of them (states orthogonal
when one componentwise act carries one to the other). The main theorem
is a parity obstruction: no three states are pairwise orthogonal, at
any `n` (`rank_cap_two_all`). Three unit flips cannot compose to the
identity, so the act-generated orthogonality of a composite of any
finite number of fundamentals has rank exactly two.

Consequence for the wall: composition never opens rank, at any width.
Together with `Composite.irredundancy_fails` (the two-fold composite
carries a phase and collapses to the classical bit at ray grade), the
status of superposition sharpens to a schema: it is underivable from
one fundamental (`Classical.no_third_state`), from two
(`Composite.composite_classicality`), and, for rank, from any finite
composition whatsoever. Superposition is the sole quantum clause, and
no act-generated reading at any width supplies it.

All statements are pointwise; the module is axiom-free.
-/
namespace Quantum.CompositeN

/-- Composite of `n` fundamentals. -/
abbrev C (n : Nat) : Type := Fin n → Bool

/-- Orthogonality generated jointly by the componentwise flips,
    stated pointwise: some site flips and every other site holds. -/
def nperp {n : Nat} (x y : C n) : Prop :=
  ∃ k : Fin n, ∀ i, y i = if i = k then !(x i) else x i

theorem nperp_symm {n : Nat} (x y : C n) (h : nperp x y) : nperp y x := by
  obtain ⟨k, e⟩ := h
  refine ⟨k, fun i => ?_⟩
  by_cases hik : i = k
  · rw [if_pos hik, e i, if_pos hik, Bool.not_not]
  · rw [if_neg hik, e i, if_neg hik]

theorem nperp_irrefl {n : Nat} (x : C n) : ¬ nperp x x := by
  intro ⟨k, e⟩
  have h := e k
  rw [if_pos rfl] at h
  cases hx : x k <;> rw [hx] at h <;> exact Bool.noConfusion h

/-- The composite's joint orthogonality space. -/
def compOrtho (n : Nat) : Quantum.Orthoset.Orthoset (C n) where
  perp := nperp
  symm := nperp_symm
  irrefl := nperp_irrefl

/-- **Rank caps at two on every composite.** Three unit flips cannot
    compose to the identity: no three states of any finite composite
    are pairwise orthogonal under the act-generated reading. -/
theorem rank_cap_two_all {n : Nat} (x y z : C n)
    (h1 : nperp x y) (h2 : nperp y z) (h3 : nperp x z) : False := by
  obtain ⟨k1, e1⟩ := h1
  obtain ⟨k2, e2⟩ := h2
  obtain ⟨k3, e3⟩ := h3
  by_cases h12 : k1 = k2
  · -- two flips at one site cancel, so z = x, and h3 refutes rest
    have hzx : ∀ i, z i = x i := by
      intro i
      by_cases hik : i = k1
      · rw [e2 i, hik, ← h12, if_pos rfl, e1 k1, if_pos rfl,
          Bool.not_not]
      · rw [e2 i, ← h12, if_neg hik, e1 i, if_neg hik]
    have h := e3 k3
    rw [if_pos rfl, hzx k3] at h
    cases hx : x k3 <;> rw [hx] at h <;> exact Bool.noConfusion h
  · -- distinct sites force k3 = k1 and k3 = k2, a contradiction
    have hk31 : k1 = k3 := by
      by_cases hne : k1 = k3
      · exact hne
      exfalso
      have hz := e3 k1
      rw [if_neg hne] at hz
      have hz' := e2 k1
      rw [if_neg h12, e1 k1, if_pos rfl] at hz'
      rw [hz'] at hz
      cases hx : x k1 <;> rw [hx] at hz <;> exact Bool.noConfusion hz
    have hk32 : k2 = k3 := by
      by_cases hne : k2 = k3
      · exact hne
      exfalso
      have hz := e3 k2
      rw [if_neg hne] at hz
      have hz' := e2 k2
      rw [if_pos rfl, e1 k2,
        if_neg (fun h : k2 = k1 => h12 h.symm)] at hz'
      rw [hz'] at hz
      cases hx : x k2 <;> rw [hx] at hz <;> exact Bool.noConfusion hz
    exact h12 (hk31.trans hk32.symm)

/-- The orthoset form: no composite has rank three. -/
theorem not_rank3_all (n : Nat) :
    ¬ Quantum.Orthoset.HasRank3 (compOrtho n) := by
  intro ⟨x, y, z, h1, h2, h3⟩
  exact rank_cap_two_all x y z h1 h2 h3

#print axioms Quantum.CompositeN.nperp_symm
#print axioms Quantum.CompositeN.nperp_irrefl
#print axioms Quantum.CompositeN.rank_cap_two_all
#print axioms Quantum.CompositeN.not_rank3_all

end Quantum.CompositeN
