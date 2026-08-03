import Alphabet
import Capacity
import Forman
import Saturation
import SecondLaw
import Measurement
import RegistrationSpine
import Obs.Budget
import Obs.StochasticUnlock
import Obs.Dimension
import Obs.CausalOrder
import Geom.Profile
import Geom.Registration
import Diagonal
import Observer
import Ladder
import Branch

/-!
# T-16 Discrete Einstein / Jacobson skeleton

**Attempt.** Jacobson derived continuum Einstein equations from horizon
thermodynamics: entropy/area bound + Clausius at local Rindler horizons.
This module asks how far that logical shape survives in DAG's discrete
ledger, now that Forman curvature (T-14) and saturation EoS (T-15) exist.

**What falls out (proved below).**
1. Entropy/capacity bound (T-9).
2. Clausius/Landauer: merge ⇒ record (T-4 / T-11).
3. Local horizon: seal-per-reading + observers_forced (Jacobson quantifier).
4. Saturation equation of state (T-15): alive ⇔ records ≤ caps; equality
   fixes flux.
5. Forman curvature accounting (T-14): tree edges Forman-negative; each
   registered face pays one unit of unpaid flatness.
6. Discrete Einstein caricature `G ~ T`: unpaid Forman flatness on an
   edge is paid exactly by registered 2-cells; at the flatness threshold
   Ricci is no longer strictly negative. Stress-energy proxy = record
   flux; at saturation it equals consumed capacity.
7. Pointwise local ledger patches over branch loci (O-3 stalk); overlap
   compatibility of capacity lengths when loci agree.

**What does not fall out.**
- O-2 (structural): boosts / Unruh `T` — only ℤ/2. Deepest Einstein gap.
- O-3 (tractable open work): sheaf of local ledgers — stalks exist; glue
  programme filed in `docs/RESIDUE.md`.
- R-1 (structural obstruction + tractable budget): ultrametric ≠ space;
  recombination counting is Lean-attackable.
- O-4 / O-5: continuum Lorentzian limit; matter from the framework.
- Continuum `G_{μν} = 8π T_{μν}`: refused. Skeleton occupies the EoS slot.

No temperature, no Boltzmann, no continuum metric, no `sorry`.
-/

namespace Bridge.EinsteinSkeleton

open Obs.StochasticUnlock
open Obs.Budget (Saturated)
open Bridge.Forman

/-! ## Discrete curvature deficit (= unpaid flatness) -/

/-- Unpaid flatness on an edge: faces still needed to leave Forman
    negativity. Lean `Nat` subtraction saturates at 0. -/
def unpaidFlatness (degU degV faces : Nat) : Nat :=
  (degU + degV) - (4 + faces)

/-- Forman–Ricci quantity reading: `Ric_F ~ (4+faces) − (degU+degV)`.
    We track the signed deficit as `unpaidFlatness` (nonnegative). -/
def formanRicciProxy (degU degV faces : Nat) : Int :=
  ((4 + faces : Nat) : Int) - ((degU + degV : Nat) : Int)

theorem unpaid_of_neg {dU dV faces : Nat}
    (h : StrictlyNegativeFaced dU dV faces) :
    0 < unpaidFlatness dU dV faces := by
  -- h : 4 + faces < dU + dV
  exact Nat.sub_pos_of_lt h

theorem unpaid_zero_iff_not_neg (dU dV faces : Nat) :
    unpaidFlatness dU dV faces = 0 ↔
      ¬ StrictlyNegativeFaced dU dV faces := by
  constructor
  · intro hz hneg
    exact Nat.ne_of_gt (unpaid_of_neg hneg) hz
  · intro hnot
    -- ¬ (4+faces < dU+dV) ⇒ dU+dV ≤ 4+faces ⇒ Nat.sub = 0
    have hle : dU + dV ≤ 4 + faces := Nat.le_of_not_gt hnot
    exact Nat.sub_eq_zero_of_le hle

/-- Each registered face pays exactly one unit of unpaid flatness
    (while faces remain below the flatness threshold). -/
theorem face_pays_one (dU dV faces : Nat)
    (hle : 4 + faces + 1 ≤ dU + dV) :
    unpaidFlatness dU dV faces =
      unpaidFlatness dU dV (faces + 1) + 1 := by
  unfold unpaidFlatness
  -- (dU+dV)-(4+faces) = (dU+dV)-(4+faces+1)+1
  have h1 : 4 + (faces + 1) = 4 + faces + 1 := by rw [Nat.add_assoc]
  rw [h1]
  -- Let a = dU+dV, b = 4+faces; need a - b = a - (b+1) + 1
  have hb : 4 + faces ≤ dU + dV := Nat.le_trans (Nat.le_succ _) hle
  -- a - (b+1) + 1 = a - b  when b+1 ≤ a, via cancelling the +1 against sub
  have hcancel : (dU + dV) - (4 + faces + 1) + 1 = (dU + dV) - (4 + faces) := by
    -- rewrite 4+faces+1 as succ (4+faces)
    change (dU + dV) - Nat.succ (4 + faces) + 1 = (dU + dV) - (4 + faces)
    rw [Nat.sub_succ]
    -- pred (a - b) + 1 = a - b when a - b ≠ 0, i.e. b < a
    have hpos : 0 < (dU + dV) - (4 + faces) := Nat.sub_pos_of_lt (Nat.lt_of_succ_le hle)
    exact Nat.succ_pred_eq_of_pos hpos
  exact hcancel.symm

/-! ## Discrete Einstein caricature: G ~ T on tree edges -/

/-- Binary internal edge: unpaid flatness starts at 2; two faces buy the
    Forman zero-line. Curvature relief costs records. -/
theorem curvature_relief_costs_records :
    unpaidFlatness 3 3 0 = 2 ∧
    unpaidFlatness 3 3 1 = 1 ∧
    unpaidFlatness 3 3 2 = 0 ∧
    ¬ StrictlyNegativeFaced 3 3 2 ∧
    StrictlyNegativeFaced 3 3 0 ∧
    StrictlyNegativeFaced 3 3 1 := by
  refine ⟨rfl, rfl, rfl, ?_, ?_, ?_⟩
  · exact Bridge.Forman.internal_not_neg_at_two_faces
  · exact Bridge.Forman.internal_edge_forman_neg
  · exact Bridge.Forman.internal_still_neg_at_one_face

/-- At Kmin, every internal tree edge needs exactly `Kmin` registered
    faces to leave Forman negativity — the discrete `G ~ T` threshold. -/
theorem Kmin_flatness_threshold :
    unpaidFlatness
      (internalDeg Bridge.Alphabet.Kmin)
      (internalDeg Bridge.Alphabet.Kmin) 0 =
      Bridge.Alphabet.Kmin ∧
    unpaidFlatness
      (internalDeg Bridge.Alphabet.Kmin)
      (internalDeg Bridge.Alphabet.Kmin) Bridge.Alphabet.Kmin = 0 := by
  rw [Bridge.Forman.Kmin_internal_deg, Bridge.Alphabet.Kmin_eq]
  exact ⟨rfl, rfl⟩

/-! ## Stress-energy proxy = record flux -/

/-- Local stress-energy proxy: realized merge multiplicity (fiber size). -/
def stressProxy (fiberLen : Nat) : Nat := fiberLen

/-- Capacity / "area" proxy consumed this tick. -/
def capacityProxy (alphLen : Nat) : Nat := alphLen

/-- At saturation, stress-energy proxy equals capacity consumed
    (local energy balance / Einstein EoS face). -/
theorem stress_eq_capacity_at_saturation
    {X E S E' : Type} [DecidableEq E']
    (G : X × E → S × E')
    (hinj : ∀ a b : X × E, G a = G b → a = b)
    (e0 : E) (s : S) (xs : List X) (hd : Distinct xs)
    (hsys : ∀ x, x ∈ xs → (G (x, e0)).1 = s)
    (Es : List E') (hEs : Distinct Es)
    (halph : ∀ x, x ∈ xs → (G (x, e0)).2 ∈ Es)
    (hsat : Saturated G e0 xs Es) :
    stressProxy xs.length = capacityProxy Es.length := by
  change xs.length = Es.length
  exact (Bridge.Saturation.saturation_iff_tick_equality
    G hinj e0 s xs hd hsys Es hEs halph).mpr hsat

/-! ## Local ledger patches (O-3 stalks) -/

/-- A local ledger patch at a branch locus. Pointwise Jacobson needs one
    balance law per locus; a sheaf would glue them (O-3, open). -/
structure LocalLedgerPatch (X E S E' : Type) where
  locus : Nat
  G : X × E → S × E'
  e0 : E
  s : S
  fiber : List X
  alphabet : List E'

/-- Crude overlap: equal loci agree on capacity length. Not a sheaf. -/
def OverlapCompatible {X E S E' : Type}
    (p q : LocalLedgerPatch X E S E') : Prop :=
  p.locus = q.locus → p.alphabet.length = q.alphabet.length

theorem overlap_refl {X E S E' : Type}
    (p : LocalLedgerPatch X E S E') : OverlapCompatible p p :=
  fun _ => rfl

theorem overlap_symm {X E S E' : Type}
    (p q : LocalLedgerPatch X E S E')
    (h : OverlapCompatible p q) : OverlapCompatible q p := by
  intro heq
  exact (h heq.symm).symm

/-- Pointwise saturation balance on a patch (local Einstein EoS stalk). -/
theorem patch_saturation_balance
    {X E S E' : Type} [DecidableEq E']
    (p : LocalLedgerPatch X E S E')
    (hinj : ∀ a b : X × E, p.G a = p.G b → a = b)
    (hd : Distinct p.fiber)
    (hsys : ∀ x, x ∈ p.fiber → (p.G (x, p.e0)).1 = p.s)
    (hEs : Distinct p.alphabet)
    (halph : ∀ x, x ∈ p.fiber → (p.G (x, p.e0)).2 ∈ p.alphabet) :
    p.fiber.length = p.alphabet.length ↔
      Saturated p.G p.e0 p.fiber p.alphabet :=
  Bridge.Saturation.saturation_iff_tick_equality
    p.G hinj p.e0 p.s p.fiber hd hsys p.alphabet hEs halph

/-- Every branch node has ≥2 children — the discrete "local frame" width
    that would host independent local ledgers if O-3 were solved. -/
theorem local_frame_width (k : Nat)
    (f : Ladder.Level k → Ladder.Level k → Bool) :
    ∃ e₁ e₂ : Branch.Predicate k,
      Branch.IsEscape k f e₁ ∧ Branch.IsEscape k f e₂ ∧
        ∃ x, e₁ x ≠ e₂ x :=
  Bridge.Measurement.two_children k f

/-! ## Seal = local horizon (Jacobson quantifier) -/

/-- Seal-per-reading: every self-reading misses its dodge; observers are
    forced at every ladder level. Local horizon through every reading. -/
theorem local_horizon_seal (k : Nat) :
    (¬ Diagonal.PointSurjective (Ladder.rep k)) ∧
    (∀ a : Ladder.Level k,
      Ladder.rep (k + 1) none (some a) = !(Ladder.rep k a a)) ∧
    Bridge.Alphabet.Kmin = 2 :=
  ⟨(Observer.observers_forced k).2.1,
   (Observer.observers_forced k).1,
   Bridge.Alphabet.Kmin_eq⟩

/-! ## Open gaps (enumerated; none discharged) -/

/-- Residues blocking continuum Einstein. Enumerated for the audit. -/
inductive OpenGap where
  | O2_noBoostUnruh
  | O3_noLedgerSheaf
  | O4_noContinuumLimit
  | O5_noMatterDynamics
  | R1_noSpatialMetric
  deriving DecidableEq, Repr

def openGaps : List OpenGap :=
  [.O2_noBoostUnruh, .O3_noLedgerSheaf, .O4_noContinuumLimit,
   .O5_noMatterDynamics, .R1_noSpatialMetric]

theorem openGaps_complete :
    openGaps.length = 5 ∧
    OpenGap.O2_noBoostUnruh ∈ openGaps ∧
    OpenGap.O3_noLedgerSheaf ∈ openGaps := by
  decide

/-! ## Jacobson input package (discharged skeletons) -/

/-- J1–J5: every Jacobson ingredient that DAG currently discharges. -/
theorem jacobson_inputs_discharged :
    -- J1 entropy/capacity bound
    (∀ T, Bridge.Capacity.caps T = 2 ^ (T + 2)) ∧
    (∀ T, 2 ^ T ≤ Bridge.Capacity.caps T) ∧
    -- J2 Clausius/Landauer
    (∀ {S E : Type} {U : S × E → S × E},
      Geom.Registration.Inj U →
      Geom.Registration.Merges U →
      Geom.Registration.Registers U) ∧
    -- J3 local horizon (seal)
    (∀ k, ¬ Diagonal.PointSurjective (Ladder.rep k)) ∧
    -- J4 saturation EoS
    (∀ (K : Nat) (prof : Geom.Profile.DepthProfile) (T : Nat),
      Geom.Profile.Alive K prof T ↔
        K ^ T ≤ Geom.Profile.capacityOf K prof T) ∧
    -- J5 Forman curvature accounting
    StrictlyNegative (internalDeg 2) (internalDeg 2) ∧
    (∀ faces, quantity faces < quantity (faces + 1)) ∧
    Bridge.Alphabet.Kmin = 2 :=
  ⟨Bridge.Capacity.caps_eq,
   Bridge.Capacity.alive_arith,
   fun hU hm => Bridge.SecondLaw.landauer hU hm,
   fun k => (Observer.observers_forced k).2.1,
   Bridge.Saturation.alive_iff_records_le_caps,
   Bridge.Forman.internal_edge_forman_neg,
   Bridge.Forman.recombination_raises_quantity,
   Bridge.Alphabet.Kmin_eq⟩

/-! ## T-16 top-level package -/

/-- **T-16. Discrete Einstein / Jacobson skeleton.**

Discharged: Jacobson inputs (capacity, Landauer, seal-horizon, saturation
EoS, Forman accounting); discrete `G ~ T` caricature (unpaid flatness
paid by registered faces; stress = capacity at saturation); local ledger
stalks with overlap compatibility.

Open: O-2…O-5, R-1 (see `openGaps`). Continuum field equations refused.
The skeleton occupies the logical slot of Einstein-as-equation-of-state
without deriving `G_{μν} = 8π T_{μν}`. -/
theorem T16_discrete_einstein_skeleton :
    -- discrete G ~ T on Kmin internal edges
    (unpaidFlatness 3 3 0 = 2 ∧
      unpaidFlatness 3 3 2 = 0 ∧
      ¬ StrictlyNegativeFaced 3 3 2) ∧
    -- Jacobson inputs
    (∀ T, Bridge.Capacity.caps T = 2 ^ (T + 2)) ∧
    (∀ {S E : Type} {U : S × E → S × E},
      Geom.Registration.Inj U →
      Geom.Registration.Merges U →
      Geom.Registration.Registers U) ∧
    (∀ k, ¬ Diagonal.PointSurjective (Ladder.rep k)) ∧
    (∀ (K : Nat) (prof : Geom.Profile.DepthProfile) (T : Nat),
      Geom.Profile.Alive K prof T ↔
        K ^ T ≤ Geom.Profile.capacityOf K prof T) ∧
    -- order remains 1-d (curvature precluded only on the line)
    (∀ tTurn, Obs.Dimension.OrderDimEq tTurn
      (Obs.CausalOrder.fwdPrecedes tTurn) 1) ∧
    -- gaps still open
    (openGaps.length = 5) ∧
    Bridge.Alphabet.Kmin = 2 :=
  ⟨⟨rfl, rfl, Bridge.Forman.internal_not_neg_at_two_faces⟩,
   Bridge.Capacity.caps_eq,
   fun hU hm => Bridge.SecondLaw.landauer hU hm,
   fun k => (Observer.observers_forced k).2.1,
   Bridge.Saturation.alive_iff_records_le_caps,
   Bridge.Forman.curvature_precluded_only_on_the_line,
   rfl,
   Bridge.Alphabet.Kmin_eq⟩

#print axioms unpaid_zero_iff_not_neg
#print axioms face_pays_one
#print axioms curvature_relief_costs_records
#print axioms Kmin_flatness_threshold
#print axioms stress_eq_capacity_at_saturation
#print axioms local_horizon_seal
#print axioms jacobson_inputs_discharged
#print axioms T16_discrete_einstein_skeleton
#print axioms openGaps_complete

end Bridge.EinsteinSkeleton
