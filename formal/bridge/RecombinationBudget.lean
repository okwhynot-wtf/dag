import Alphabet
import Capacity
import Forman
import EinsteinSkeleton
import EffectiveMatter
import Geom.Profile

/-!
# R-1 recombination budget

Whether the registration / aliveness budget can buy near-flatness
(Forman ≥ 0) on the branch tree.

Crude census: a full binary tree of depth `d` has `2^(d+1) - 2` edges;
each Kmin edge needs `Kmin = 2` faces to leave Forman negativity.
Total face demand `2 * (2^(d+1) - 2)` fits inside `|caps d| = 2^(d+2)`
once written as `2^(d+2) - 4`.

This establishes the counting half of R-1 for the complete binary tree.
The ultrametric ≠ Archimedean-space obstruction remains: budget for
Forman zero does not manufacture a spatial metric.
-/

namespace Bridge.RecombinationBudget

open Bridge.Forman
open Bridge.EinsteinSkeleton
open Bridge.EffectiveMatter

/-- Edges in a full binary tree of depth `d` (nodes `2^(d+1)-1`). -/
def treeEdges (d : Nat) : Nat := 2 ^ (d + 1) - 2

/-- Faces needed to flatten every edge, at 2 faces/edge (`Kmin`). -/
def facesToFlatten (d : Nat) : Nat := 2 * treeEdges d

/-- Per-edge unpaid flatness on a Kmin internal edge (faces = 0). -/
def perEdgeCost : Nat :=
  unpaidFlatness
    (internalDeg Bridge.Alphabet.Kmin)
    (internalDeg Bridge.Alphabet.Kmin) 0

theorem perEdgeCost_eq_two : perEdgeCost = 2 := by
  simp only [perEdgeCost, unpaidFlatness, internalDeg, Bridge.Alphabet.Kmin_eq]

/-- `2 * (2^(d+1) - 2) = 2^(d+2) - 4` when `2 ≤ 2^(d+1)`. -/
theorem faces_closed_form (d : Nat) (hd : 1 ≤ d) :
    facesToFlatten d = 2 ^ (d + 2) - 4 := by
  unfold facesToFlatten treeEdges
  have h2le : 2 ≤ 2 ^ (d + 1) := by
    have hle : 1 ≤ d + 1 := Nat.le_succ_of_le hd
    have : (2 : Nat) ^ 1 ≤ 2 ^ (d + 1) :=
      Nat.pow_le_pow_right (by decide : 0 < 2) hle
    exact this
  -- Goal: 2 * (2^(d+1) - 2) = 2^(d+2) - 4
  have hmul :
      2 * (2 ^ (d + 1) - 2) = 2 * 2 ^ (d + 1) - 4 := by
    have h := Nat.mul_sub_left_distrib 2 (2 ^ (d + 1)) 2
    simpa using h
  have hpow : 2 * 2 ^ (d + 1) = 2 ^ (d + 2) := by
    rw [Nat.mul_comm, ← Nat.pow_succ]
  rw [hmul, hpow]

/-- **R-1 counting (positive).** Face demand to Forman-flatten a depth-`d`
    binary tree fits inside committed capacity `|caps d|`. -/
theorem r1_faces_within_caps (d : Nat) (hd : 1 ≤ d) :
    facesToFlatten d ≤ Bridge.Capacity.caps d := by
  rw [faces_closed_form d hd, Bridge.Capacity.caps_eq]
  exact Nat.sub_le (2 ^ (d + 2)) 4

/-- Expand budget `2^d` can fail: at `d = 1`, demand 4 > expand 2. -/
theorem r1_faces_exceed_expand_at_one :
    ¬ facesToFlatten 1 ≤ Geom.Profile.capacityOf 2 Geom.Profile.expand 1 := by
  decide

/-- Per-edge cost (= 2) fits aliveness `|caps T|` at every horizon. -/
theorem per_edge_within_aliveness (T : Nat) :
    perEdgeCost ≤ alivenessBudget T := by
  rw [perEdgeCost_eq_two]
  -- 2 ≤ caps T = 2^(T+2)
  have h := kmin_flatness_within_caps_budget T
  -- recombinationsNeeded Kmin internal = 2
  simpa [recombinationsNeeded, unpaidFlatness, internalDeg,
    Bridge.Alphabet.Kmin_eq, alivenessBudget] using h

/-- Small-depth census: d=1 demand equals 4; caps(1)=8; expand(1)=2. -/
theorem r1_census_depth_one :
    facesToFlatten 1 = 4 ∧
    Bridge.Capacity.caps 1 = 8 ∧
    Geom.Profile.capacityOf 2 Geom.Profile.expand 1 = 2 := by
  decide

/-- **R-1 budget package.** Tree-wide Forman face demand ≤ `|caps d|`;
    per-edge cost ≤ aliveness; expand budget can fail (d=1 witness).
    Ultrametric ≠ space remains structural. -/
theorem r1_recombination_budget_fragment :
    (∀ d, 1 ≤ d → facesToFlatten d ≤ Bridge.Capacity.caps d) ∧
    (∀ T, perEdgeCost ≤ alivenessBudget T) ∧
    (¬ facesToFlatten 1 ≤
      Geom.Profile.capacityOf 2 Geom.Profile.expand 1) ∧
    Bridge.Alphabet.Kmin = 2 :=
  ⟨r1_faces_within_caps, per_edge_within_aliveness,
   r1_faces_exceed_expand_at_one, Bridge.Alphabet.Kmin_eq⟩

#print axioms faces_closed_form
#print axioms r1_faces_within_caps
#print axioms r1_faces_exceed_expand_at_one
#print axioms r1_recombination_budget_fragment

end Bridge.RecombinationBudget
