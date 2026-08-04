import Alphabet
import Geom.Gradient
import Obs.CausalOrder
import Obs.Dimension

/-!
# T-14 Forman–Ricci curvature on the branch tree

Measure-free combinatorial curvature (Forman): for an unweighted edge,
`Ric_F = (4 + #faces) − deg(u) − deg(v)`. Continuum / measure-theoretic
Ollivier–Ricci is not derived; a finite counting trial lives in
`BranchMeasure.ollivier_trial_fragment`. Metric/Riemann curvature remains
unstateable (needs space + signature — R-1), which is absence, not
preclusion.

On the K-ary branch tree with `K = Kmin = 2`:
  root degree 2; every internal node degree `K+1 = 3`.
Internal edges have strictly negative Forman (faces = 0).

Attaching a registered 2-cell (recombination cycle) increments `#faces`
on the edges it touches and therefore strictly raises their Forman
quantity toward zero. Recombination is the only combinatorial cure for
tree-scale Forman negativity.

R-1 concerns the cost in registered recombinations of near-flatness
versus the registration / aliveness budget.
-/

namespace Bridge.Forman

/-- Unweighted Forman on a pure graph edge is strictly negative. -/
def StrictlyNegative (degU degV : Nat) : Prop :=
  4 < degU + degV

/-- Face-augmented Forman negativity (`#faces` = attached 2-cells). -/
def StrictlyNegativeFaced (degU degV faces : Nat) : Prop :=
  4 + faces < degU + degV

/-- Forman quantity for comparison (larger ⇒ less negatively curved).
    Ricci ~ quantity − (degU + degV); we track the quantity `4 + faces`. -/
def quantity (faces : Nat) : Nat := 4 + faces

/-- Binary / Kmin internal node degree: parent + K children. -/
def internalDeg (K : Nat) : Nat := K + 1

def rootDeg : Nat := 2

theorem Kmin_internal_deg :
    internalDeg Bridge.Alphabet.Kmin = 3 := by
  rw [Bridge.Alphabet.Kmin_eq]
  rfl

theorem four_lt_five : 4 < 5 := Nat.lt_succ_self 4

theorem four_lt_six : 4 < 6 :=
  Nat.lt_trans four_lt_five (Nat.lt_succ_self 5)

/-- Root–child edge on the binary tree: deg 2 and 3. -/
theorem root_edge_forman_neg :
    StrictlyNegative rootDeg (internalDeg 2) :=
  four_lt_five

/-- Internal edge on the binary tree: deg 3 and 3. -/
theorem internal_edge_forman_neg :
    StrictlyNegative (internalDeg 2) (internalDeg 2) :=
  four_lt_six

/-- At `Kmin`, every tree-style edge among internal degrees is Forman-negative. -/
theorem Kmin_tree_edges_forman_neg :
    StrictlyNegative rootDeg (internalDeg Bridge.Alphabet.Kmin) ∧
    StrictlyNegative (internalDeg Bridge.Alphabet.Kmin)
      (internalDeg Bridge.Alphabet.Kmin) := by
  rw [Kmin_internal_deg]
  exact ⟨root_edge_forman_neg, internal_edge_forman_neg⟩

/-- Faces = 0 restates pure-graph negativity. -/
theorem faced_zero_iff (dU dV : Nat) :
    StrictlyNegativeFaced dU dV 0 ↔ StrictlyNegative dU dV :=
  Iff.rfl

/-- **Recombination raises Forman.** Attaching one more 2-cell strictly
    increases the Forman quantity on an edge (toward zero / positive). -/
theorem recombination_raises_quantity (faces : Nat) :
    quantity faces < quantity (faces + 1) :=
  Nat.add_lt_add_left (Nat.lt_succ_self faces) 4

/-- Same degrees: one more face weakens Forman-negativity (may exit it). -/
theorem recombination_weakens_negativity (dU dV faces : Nat)
    (h : StrictlyNegativeFaced dU dV (faces + 1)) :
    StrictlyNegativeFaced dU dV faces :=
  Nat.lt_trans (recombination_raises_quantity faces) h

theorem five_lt_six : 5 < 6 := Nat.lt_succ_self 5

/-- Internal binary edge: still negative at 1 face; zero-line at 2 faces
    (`4 + 2 = 3 + 3`). Quantitative lower bound toward flatness. -/
theorem internal_still_neg_at_one_face :
    StrictlyNegativeFaced 3 3 1 := by
  show 4 + 1 < 3 + 3
  exact five_lt_six

theorem internal_not_neg_at_two_faces :
    ¬ StrictlyNegativeFaced 3 3 2 := by
  intro h
  -- h : 4 + 2 < 3 + 3, i.e. 6 < 6
  show False
  have h' : 6 < 6 := h
  exact Nat.lt_irrefl 6 h'

theorem internal_flat_budget :
    StrictlyNegativeFaced 3 3 0 ∧
    StrictlyNegativeFaced 3 3 1 ∧
    ¬ StrictlyNegativeFaced 3 3 2 :=
  ⟨internal_edge_forman_neg, internal_still_neg_at_one_face,
   internal_not_neg_at_two_faces⟩

/-! ## Worked complex (face-count insurance for T-14 → T-16) -/

/-- Named toy edges for a census: line, tree-internal, recombined. -/
structure ToyEdge where
  degU : Nat
  degV : Nat
  faces : Nat

def toyLine : ToyEdge := ⟨2, 2, 0⟩
def toyTreeInternal : ToyEdge := ⟨3, 3, 0⟩
def toyRecombinedUnfilled : ToyEdge := ⟨3, 3, 0⟩
def toyRecombinedFilled : ToyEdge := ⟨3, 3, 2⟩

/-- Forman quantity on a toy edge. -/
def ToyEdge.formanQty (e : ToyEdge) : Nat := 4 + e.faces

/-- Line edge is not Forman-negative (deg 2+2 = 4). -/
theorem toy_line_not_neg :
    ¬ StrictlyNegativeFaced toyLine.degU toyLine.degV toyLine.faces := by
  intro h
  -- 4 + 0 < 2 + 2
  exact Nat.lt_irrefl 4 h

/-- Tree-internal (and unfilled recombined) is Forman-negative. -/
theorem toy_tree_neg :
    StrictlyNegativeFaced toyTreeInternal.degU toyTreeInternal.degV
      toyTreeInternal.faces :=
  internal_edge_forman_neg

/-- Filling with 2 faces exits negativity — the recombination budget. -/
theorem toy_filled_not_neg :
    ¬ StrictlyNegativeFaced toyRecombinedFilled.degU
        toyRecombinedFilled.degV toyRecombinedFilled.faces :=
  internal_not_neg_at_two_faces

/-- Face count from unfilled to filled is exactly two recombinations. -/
theorem toy_fill_costs_two :
    toyRecombinedFilled.faces = toyRecombinedUnfilled.faces + 2 ∧
    toyRecombinedFilled.formanQty =
      toyRecombinedUnfilled.formanQty + 2 :=
  ⟨rfl, rfl⟩

/-- **Worked complex package.** Concrete edge census: line non-neg;
    tree neg; two faces cure internal negativity. Guards off-by-one in
    the T-14 → T-16 face count. -/
theorem worked_recombination_complex :
    ¬ StrictlyNegativeFaced 2 2 0 ∧
    StrictlyNegativeFaced 3 3 0 ∧
    ¬ StrictlyNegativeFaced 3 3 2 ∧
    quantity 0 + 2 = quantity 2 :=
  ⟨toy_line_not_neg, toy_tree_neg, toy_filled_not_neg, rfl⟩

/-- **Ledger side (unconditional):** eternal aliveness forces non-flat
    capacity profile — the framework anti-precludes counted flatness. -/
theorem live_forbids_flat_profile {K : Nat} (hK : 2 ≤ K)
    (prof : Nat → Nat)
    (halive : ∀ T, K ^ T ≤ K ^ (prof T)) :
    ∀ C, ¬ (∀ t, prof t = C) :=
  Geom.Gradient.eternal_aliveness_needs_gradient hK prof halive

/-- Order dim 1: the only place curvature is *precluded* (Riemann
    vacuous on a line). Says nothing about the system at large. -/
theorem curvature_precluded_only_on_the_line (tTurn : Nat) :
    Obs.Dimension.OrderDimEq tTurn (Obs.CausalOrder.fwdPrecedes tTurn) 1 :=
  Obs.Dimension.ascent_order_dim_eq_one tTurn

/-- **T-14.** Tree Forman negative; recombination raises quantity
    (flatness paid by faces); live ⇒ ¬flat(prof); preclusion only on
    the 1-d line. -/
theorem T14_forman_tree_curvature :
    StrictlyNegative (internalDeg 2) (internalDeg 2) ∧
    (∀ faces, quantity faces < quantity (faces + 1)) ∧
    ¬ StrictlyNegativeFaced 3 3 2 ∧
    (∀ {K : Nat}, 2 ≤ K → ∀ (prof : Nat → Nat),
      (∀ T, K ^ T ≤ K ^ (prof T)) →
        ∀ C, ¬ (∀ t, prof t = C)) ∧
    Bridge.Alphabet.Kmin = 2 :=
  ⟨internal_edge_forman_neg, recombination_raises_quantity,
   internal_not_neg_at_two_faces, live_forbids_flat_profile,
   Bridge.Alphabet.Kmin_eq⟩

#print axioms root_edge_forman_neg
#print axioms internal_edge_forman_neg
#print axioms recombination_raises_quantity
#print axioms internal_flat_budget
#print axioms worked_recombination_complex
#print axioms live_forbids_flat_profile
#print axioms T14_forman_tree_curvature

end Bridge.Forman
