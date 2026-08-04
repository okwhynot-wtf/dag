import Alphabet
import Capacity
import OneZ2
import RegistrationSpine
import TickSimulation
import Environment
import Dil
import RegistrationFactor
import ArchiveMustSpeak
import PageShape
import SecondLaw
import Measurement
import BranchMeasure
import Expansion
import Forman
import Saturation
import EinsteinSkeleton
import EffectiveMatter
import FluxPattern
import LedgerSheaf
import RecombinationBudget
import PhaseEToys
import Period2KMS
import ModularCut
import LorentzianDict
import TwoBounce
import Geom.Registration
import Geom.Profile
import Density
import Canon
import Orbit
import Cause
import Tower
import Ladder
import Branch
import Diagonal
import Limit
import Revision

/-!
# Bridge arc — milestone weld
-/

namespace Bridge.Arc

theorem milestone_M1 :
    Bridge.Alphabet.Kmin = 2 ∧
    (∀ f : Bridge.OneZ2.Face, ∀ b : Bridge.OneZ2.Z2,
      Bridge.OneZ2.project f (Bridge.OneZ2.project f b) = b) ∧
    (∀ T, Bridge.Capacity.caps T = 2 ^ (T + 2)) :=
  ⟨Bridge.Alphabet.Kmin_eq,
   Bridge.OneZ2.project_involution,
   Bridge.Capacity.caps_eq⟩

theorem milestone_M2 :
    (∀ {S E : Type} {U : S × E → S × E},
      Geom.Registration.Inj U →
      Geom.Registration.Merges U →
      Geom.Registration.Registers U) ∧
    (∀ {α : Type} (act : α → α),
      Canon.IsFundamental act → Orbit.Lossless act) ∧
    (∀ k : Nat, Tower.NamingExtension
      (Ladder.rep k) (Ladder.rep (k + 1)) some (Ladder.dodgeEscape k)) ∧
    (∃ (act : Bool → Bool) (f f' : Bool → Bool → Bool) (a : Bool),
      Orbit.Erasing act ∧ f a a ≠ f' a a ∧
      Cause.effectOf act f a = Cause.effectOf act f' a) :=
  Bridge.RegistrationSpine.registration_on_spine

theorem milestone_M4 :
    (∀ T, Bridge.Capacity.caps T = 2 ^ (T + 2)) ∧
    (∀ T, Geom.Profile.Alive 2 Geom.Profile.expand T) ∧
    (∀ T, 2 ^ T ≤ Bridge.Capacity.caps T) ∧
    (∀ T, Geom.Profile.capacityOf 2 Geom.Profile.expand (T + 1) =
      2 * Geom.Profile.capacityOf 2 Geom.Profile.expand T) ∧
    (∀ T, Bridge.Capacity.caps (T + 1) = 2 * Bridge.Capacity.caps T) ∧
    (∀ k, Tower.NamingExtension
      (Ladder.rep k) (Ladder.rep (k + 1)) some (Ladder.dodgeEscape k)) ∧
    (∀ k, ∃ b : Ladder.Level (k + 1),
      ∀ a : Ladder.Level k, (some a : Ladder.Level (k + 1)) ≠ b) ∧
    (¬ Geom.Registration.Merges Geom.Registration.oscStep) ∧
    (Geom.Registration.Registers Geom.Registration.swapStep) :=
  Bridge.TickSimulation.tick_simulation

theorem milestone_M5 :
    (∀ {S E : Type} {U : S × E → S × E},
      Geom.Registration.Inj U →
      ∀ w : Bridge.Environment.TwoMerge S E U,
        ∀ i j, Bridge.Environment.recordLabel w i =
          Bridge.Environment.recordLabel w j → i = j) ∧
    (Geom.Registration.Inj Geom.Registration.swapStep ∧
      Geom.Registration.Merges Geom.Registration.swapStep ∧
      Geom.Registration.Registers Geom.Registration.swapStep) ∧
    (∀ T, Bridge.Environment.capCount T = 2 ^ (T + 2)) ∧
    (∀ T, Nonempty (Bridge.Environment.E T)) ∧
    (∀ k, ∃ b : Bridge.Environment.E (k + 1),
      ∀ a : Bridge.Environment.E k,
        (some a : Bridge.Environment.E (k + 1)) ≠ b) ∧
    Bridge.Alphabet.Kmin = 2 :=
  Bridge.Environment.environment_universality

/-- Keystone Dil sprint: free archive initial; capacity law; minimal schedule. -/
theorem milestone_keystone_dil :
    (∀ {S : Type} {u : S → S} (A : Bridge.Dil.Archive S u),
      (∃ _h : Bridge.Dil.Hom (Bridge.Dil.free S u) A, True) ∧
      (∀ h₁ h₂ : Bridge.Dil.Hom (Bridge.Dil.free S u) A, h₁ = h₂)) ∧
    Bridge.Dil.MinimalSchedule 2 Bridge.Capacity.caps ∧
    (∀ T, Bridge.Capacity.caps T = 2 ^ (T + 2)) ∧
    Bridge.Alphabet.Kmin = 2 :=
  ⟨fun A => (Bridge.Dil.keystone_dil_sprint).1 A,
   Bridge.Dil.keystone_dil_sprint.2.2.2.1,
   Bridge.Dil.keystone_dil_sprint.2.2.2.2.1,
   Bridge.Dil.keystone_dil_sprint.2.2.2.2.2⟩

/-- Hom existence via unique factorization (Dil rigidity progress). -/
theorem milestone_dil_hom_exists :
    (∀ {S : Type} {u : S → S} (A : Bridge.Dil.Archive S u),
      ∃ _h : Bridge.Dil.Hom (Bridge.Dil.free S u) A, True) ∧
    (∃ _fa : Bridge.Dil.UniqueFactorization
      (Bridge.Dil.free Bool not), True) ∧
    Bridge.Alphabet.Kmin = 2 :=
  ⟨fun A => Bridge.Dil.free_hom_exists_via_UF A,
   Bridge.Dil.free_always_factors Bool not,
   Bridge.Alphabet.Kmin_eq⟩

/-- Packaged UF↔UF rigidity iso (via free as intermediary). -/
theorem milestone_dil_rigidity_iso :
    (∃ _i : Bridge.Dil.ArchiveIso
      (Bridge.Dil.free Bool not) (Bridge.Dil.free Bool not), True) ∧
    Bridge.Alphabet.Kmin = 2 :=
  ⟨Bridge.Dil.free_rigidity_self Bool not, Bridge.Alphabet.Kmin_eq⟩

/-- Graded terminality among UF + pointed archives. -/
theorem milestone_dil_graded_terminality :
    (∀ {S : Type} {u : S → S} {A B : Bridge.Dil.Archive S u}
      (fa : Bridge.Dil.UniqueFactorization A)
      (fb : Bridge.Dil.UniqueFactorization B)
      (ha : Bridge.Dil.PointedSingleton A)
      (hb : Bridge.Dil.PointedSingleton B),
      (∃ _h : Bridge.Dil.Hom A B, True) ∧
      (∀ h₁ h₂ : Bridge.Dil.Hom A B, h₁ = h₂)) ∧
    Bridge.Alphabet.Kmin = 2 :=
  ⟨fun fa fb ha hb => Bridge.Dil.graded_terminality_of_UF fa fb ha hb,
   Bridge.Alphabet.Kmin_eq⟩

/-- I-2 Bool caps Fin record-map fragment (non-singleton base). -/
theorem milestone_i2_caps_record_map :
    (¬ Bridge.Dil.PointedSingleton (Bridge.Dil.boolCapsArchive not)) ∧
    Bridge.Dil.MinimalSchedule 2 Bridge.Dil.capCard ∧
    (∀ T, Bridge.Dil.capCard T = 2 ^ (T + 2)) ∧
    Bridge.Alphabet.Kmin = 2 :=
  ⟨(Bridge.Dil.i2_caps_record_map_fragment not).2.1,
   (Bridge.Dil.i2_caps_record_map_fragment not).2.2.1,
   (Bridge.Dil.i2_caps_record_map_fragment not).2.2.2.2.1,
   Bridge.Alphabet.Kmin_eq⟩

/-- I-2 Fin closed: alphabet-UF + base-relative rigidity on caps archive. -/
theorem milestone_i2_fin_closed :
    (∃ _fa : Bridge.Dil.UniqueFactorization
      (Bridge.Dil.boolCapsArchive not), True) ∧
    (∃ _i : Bridge.Dil.ArchiveIso
      (Bridge.Dil.boolCapsArchive not)
      (Bridge.Dil.boolCapsArchive not), True) ∧
    Bridge.Alphabet.Kmin = 2 :=
  ⟨(Bridge.Dil.i2_fin_closed not).1,
   (Bridge.Dil.i2_fin_closed not).2.2.2.2.2.1,
   Bridge.Alphabet.Kmin_eq⟩

/-- Ladder-predicate addressing witness + address-uniform idx fragment. -/
theorem milestone_ladder_predicate_addressing :
    (∀ T, Density.predicateCount T = Bridge.Capacity.caps T) ∧
    (∀ T, Bridge.Dil.capCard T = Bridge.Capacity.caps T) ∧
    (∃ _au : Bridge.Dil.AddressUniform
      (Bridge.Dil.boolCapsArchive not) id, True) ∧
    Bridge.Alphabet.Kmin = 2 :=
  ⟨(Bridge.Dil.ladder_predicate_addressing_witness).2.1,
   (Bridge.Dil.ladder_predicate_addressing_witness).2.2.2.1,
   ⟨Bridge.Dil.boolCaps_addressUniform not, True.intro⟩,
   Bridge.Alphabet.Kmin_eq⟩

/-- T-2 tick identification licensed remnant (committed path + label factor). -/
theorem milestone_T2_tick_id_licensed :
    (∀ T, Bridge.Capacity.caps T = 2 ^ (T + 2)) ∧
    (∀ T, Geom.Profile.Alive 2 Geom.Profile.expand T) ∧
    (Geom.Registration.Inj Geom.Registration.swapStep ∧
      Geom.Registration.Merges Geom.Registration.swapStep ∧
      Geom.Registration.Registers Geom.Registration.swapStep) ∧
    (∀ T, 1 ≤ T → Density.levelCard 0 < Density.levelCard T) ∧
    Bridge.Alphabet.Kmin = 2 :=
  ⟨Bridge.TickSimulation.tick_simulation.1,
   Bridge.TickSimulation.tick_simulation.2.1,
   ⟨Geom.Registration.swap_inj,
     Geom.Registration.swap_registers.2.1,
     Geom.Registration.swap_registers.2.2⟩,
   fun T hT =>
     (Bridge.RegistrationFactor.registration_vs_naming_obstruction).2.2.2 T hT,
   Bridge.Alphabet.Kmin_eq⟩

/-- T-2 straightening + skeleton ingredients (not unconditional tick ID). -/
theorem milestone_T2_straighten :
    (∀ {S : Type} {u : S → S} {A : Bridge.Dil.Archive S u}
      (_fa : Bridge.Dil.UniqueFactorization A),
      ∃ _i : Bridge.Dil.ArchiveIso A
        (Bridge.Dil.freeOnBase S u (A.E 0) A.z0), True) ∧
    (¬ Geom.Registration.Merges Geom.Registration.oscStep) ∧
    Bridge.Alphabet.Kmin = 2 :=
  ⟨fun fa => Bridge.Dil.uf_straightens_mod_base fa,
   Bridge.TickSimulation.oscillator_silent.1,
   Bridge.Alphabet.Kmin_eq⟩

/-- T-2 tick identification (classified): Fund exempt + swap necessity + UF append. -/
theorem milestone_T2_tick_id :
    Bridge.TickSimulation.FundExempt ∧
    Bridge.TickSimulation.BoundedReuseRegisters ∧
    Bridge.TickSimulation.NamingCarrierClimbs ∧
    (∀ {S : Type} {u : S → S} {A : Bridge.Dil.Archive S u}
      (_fa : Bridge.Dil.UniqueFactorization A),
      ∃ _i : Bridge.Dil.ArchiveIso A
        (Bridge.Dil.freeOnBase S u (A.E 0) A.z0), True) ∧
    Bridge.Alphabet.Kmin = 2 :=
  ⟨Bridge.TickSimulation.tick_identification.1,
   Bridge.TickSimulation.tick_identification.2.1,
   Bridge.TickSimulation.tick_identification.2.2.1,
   fun fa => (Bridge.TickSimulation.tick_identification.2.2.2.1 fa).1,
   Bridge.Alphabet.Kmin_eq⟩

/-- Backward-compatible alias. -/
def milestone_T2_tick_id_classified := milestone_T2_tick_id

/-- T-2 factorisation: namer-shaped positive + carrier obstruction. -/
theorem milestone_M4b :
    (∀ {S E : Type} {U : S × E → S × E},
      Geom.Registration.Inj U →
      ∀ w : Bridge.Environment.TwoMerge S E U,
        Bridge.RegistrationFactor.outsideSingleton
          (Bridge.Environment.recordLabel w false)
          (Bridge.Environment.recordLabel w true)) ∧
    (Geom.Registration.Inj Geom.Registration.swapStep ∧
      Geom.Registration.Merges Geom.Registration.swapStep ∧
      Geom.Registration.Registers Geom.Registration.swapStep) ∧
    (∀ T, 1 ≤ T → Density.levelCard 0 < Density.levelCard T) ∧
    (¬ Geom.Registration.Merges Geom.Registration.oscStep) :=
  Bridge.RegistrationFactor.registration_naming_factorisation

theorem milestone_T10 :
    (∀ {K : Nat}, 2 ≤ K → ∀ tTurn,
      Geom.Profile.IsExhaustionTick K (Geom.Profile.bounce tTurn) tTurn) ∧
    Bridge.Alphabet.Kmin = 2 :=
  ⟨fun hK tTurn => Bridge.ArchiveMustSpeak.page_time_is_exhaustion hK tTurn,
   Bridge.Alphabet.Kmin_eq⟩

theorem milestone_T10_shape :
    (∀ C t, t ≤ C → Bridge.PageShape.streamInfo C t = 0) ∧
    (∀ C t, C ≤ t → Bridge.PageShape.streamInfo C t = t - C) ∧
    (∀ C, Bridge.PageShape.streamInfo C C = 0 ∧
      Bridge.PageShape.streamInfo C (C + 1) = 1) ∧
    Bridge.Alphabet.Kmin = 2 :=
  ⟨Bridge.PageShape.T10_page_flux_shape.1,
   Bridge.PageShape.T10_page_flux_shape.2.1,
   Bridge.PageShape.T10_page_flux_shape.2.2.1,
   Bridge.Alphabet.Kmin_eq⟩

theorem milestone_T11 :
    (∀ {S E : Type} {U : S × E → S × E},
      Geom.Registration.Inj U →
      Geom.Registration.Merges U →
      Geom.Registration.Registers U) ∧
    (∀ k : Nat, ¬ ∃ (f : Ladder.Level (k + 1) → Ladder.Level k),
      ∀ x y, f x = f y → x = y) ∧
    Bridge.Alphabet.Kmin = 2 :=
  ⟨fun hU hm => Bridge.SecondLaw.landauer hU hm,
   Bridge.SecondLaw.archive_irreversible,
   Bridge.Alphabet.Kmin_eq⟩

theorem milestone_T12 :
    (∀ k (f : Ladder.Level k → Ladder.Level k → Bool),
      ∃ e₁ e₂ : Branch.Predicate k,
        Branch.IsEscape k f e₁ ∧ Branch.IsEscape k f e₂ ∧
          ∃ x, e₁ x ≠ e₂ x) ∧
    Bridge.Alphabet.Kmin = 2 :=
  ⟨Bridge.Measurement.two_children, Bridge.Alphabet.Kmin_eq⟩

theorem milestone_T12_measure :
    (∀ k f, ∃ e₁ e₂ : Branch.Predicate k,
      Branch.IsEscape k f e₁ ∧ Branch.IsEscape k f e₂ ∧
        (∃ x, e₁ x ≠ e₂ x) ∧
        Bridge.BranchMeasure.escapeWeight e₁ +
          Bridge.BranchMeasure.escapeWeight e₂ =
            Bridge.Alphabet.Kmin) ∧
    Bridge.Alphabet.Kmin = 2 :=
  ⟨Bridge.BranchMeasure.T12_measure_fragment.1, Bridge.Alphabet.Kmin_eq⟩

/-- Born no-go: multiplicity + branch structure cannot yield Born weights. -/
theorem milestone_born_nogo :
    (∀ (W : Bridge.BranchMeasure.MultiplicityOnlyWeight) k e₁ e₂,
      W.w k e₁ = W.w k e₂) ∧
    Bridge.BranchMeasure.gleason_domain_absent = True.intro ∧
    Bridge.Alphabet.Kmin = 2 :=
  ⟨fun W k e₁ e₂ =>
     Bridge.BranchMeasure.multiplicity_forces_symmetry W k e₁ e₂,
   rfl, Bridge.Alphabet.Kmin_eq⟩

/-- Finite Ollivier-style trial (counting transport; continuum refused). -/
theorem milestone_ollivier_trial :
    Bridge.Forman.StrictlyNegative
      (Bridge.Forman.internalDeg Bridge.Alphabet.Kmin)
      (Bridge.Forman.internalDeg Bridge.Alphabet.Kmin) ∧
    Bridge.BranchMeasure.continuum_ollivier_refused = True.intro ∧
    Bridge.Alphabet.Kmin = 2 :=
  ⟨Bridge.BranchMeasure.uniform_mass_preserves_forman_neg,
   rfl, Bridge.Alphabet.Kmin_eq⟩

theorem milestone_T13 :
    (∀ T, Bridge.Expansion.countedVolume 2 (T + 1) =
      2 * Bridge.Expansion.countedVolume 2 T) ∧
    (∀ T, Bridge.Expansion.countedVolume Bridge.Alphabet.Kmin T = 2 ^ T) ∧
    Bridge.Expansion.NumberEqualsVolume ∧
    Bridge.Alphabet.Kmin = 2 :=
  ⟨Bridge.Expansion.discrete_Hubble_one_bit_per_tick
      Bridge.Expansion.numberEqualsVolume,
   Bridge.Expansion.counted_deSitter_volume
      Bridge.Expansion.numberEqualsVolume,
   Bridge.Expansion.number_equals_volume_flagged,
   Bridge.Alphabet.Kmin_eq⟩

theorem milestone_T14 :
    Bridge.Forman.StrictlyNegative
      (Bridge.Forman.internalDeg 2) (Bridge.Forman.internalDeg 2) ∧
    (∀ faces, Bridge.Forman.quantity faces <
      Bridge.Forman.quantity (faces + 1)) ∧
    ¬ Bridge.Forman.StrictlyNegativeFaced 3 3 2 ∧
    Bridge.Alphabet.Kmin = 2 :=
  ⟨Bridge.Forman.internal_edge_forman_neg,
   Bridge.Forman.recombination_raises_quantity,
   Bridge.Forman.internal_not_neg_at_two_faces,
   Bridge.Alphabet.Kmin_eq⟩

theorem milestone_T15 :
    (∀ (K : Nat) (prof : Geom.Profile.DepthProfile) (T : Nat),
      Geom.Profile.Alive K prof T ↔
        K ^ T ≤ Geom.Profile.capacityOf K prof T) ∧
    Bridge.Alphabet.Kmin = 2 :=
  ⟨Bridge.Saturation.alive_iff_records_le_caps, Bridge.Alphabet.Kmin_eq⟩

theorem milestone_T16 :
    (Bridge.EinsteinSkeleton.unpaidFlatness 3 3 0 = 2) ∧
    (Bridge.EinsteinSkeleton.unpaidFlatness 3 3 2 = 0) ∧
    Bridge.EinsteinSkeleton.openGaps.length = 5 ∧
    Bridge.Alphabet.Kmin = 2 :=
  ⟨rfl, rfl, rfl, Bridge.Alphabet.Kmin_eq⟩

theorem milestone_effective_matter_sprint :
    Bridge.EffectiveMatter.VacuumDynamics Geom.Registration.oscStep ∧
    (∀ T, Bridge.EffectiveMatter.recombinationsNeeded
      (Bridge.Forman.internalDeg Bridge.Alphabet.Kmin)
      (Bridge.Forman.internalDeg Bridge.Alphabet.Kmin) ≤
        Bridge.EffectiveMatter.alivenessBudget T) ∧
    Bridge.Alphabet.Kmin = 2 :=
  ⟨Bridge.EffectiveMatter.osc_is_vacuum,
   Bridge.EffectiveMatter.kmin_flatness_within_caps_budget,
   Bridge.Alphabet.Kmin_eq⟩

theorem milestone_phase_D :
    (∃ c₀ c₁ : Bridge.FluxPattern.FluxComponent Bool,
      c₀.witness ≠ c₁.witness) ∧
    Bridge.Alphabet.Kmin = 2 ∧
    Bridge.EffectiveMatter.VacuumDynamics Geom.Registration.oscStep :=
  ⟨⟨Bridge.FluxPattern.boolComponentFalse,
    Bridge.FluxPattern.boolComponentTrue,
    Bridge.FluxPattern.bool_components_nondegenerate⟩,
   Bridge.Alphabet.Kmin_eq,
   Bridge.EffectiveMatter.osc_is_vacuum⟩

theorem milestone_o3_glue :
    (∀ {X E S E' : Type}
      {p q : Bridge.EinsteinSkeleton.LocalLedgerPatch X E S E'},
      Bridge.EinsteinSkeleton.OverlapCompatible p q →
      p.locus = q.locus → p.alphabet.length = q.alphabet.length) ∧
    Bridge.Alphabet.Kmin = 2 :=
  ⟨Bridge.LedgerSheaf.glue_capacity_on_locus, Bridge.Alphabet.Kmin_eq⟩

theorem milestone_o3_restrict :
    (∀ {X E S E' : Type}
      (p : Bridge.EinsteinSkeleton.LocalLedgerPatch X E S E') ℓ,
      (Bridge.LedgerSheaf.restrictTo p ℓ).alphabet.length =
        p.alphabet.length) ∧
    Bridge.Alphabet.Kmin = 2 :=
  ⟨fun p ℓ => Bridge.LedgerSheaf.restrict_preserves_capacity p ℓ,
   Bridge.Alphabet.Kmin_eq⟩

/-- O-3 dynamics-section fragment: balanced patches restrict/glue Fin-combinatorially. -/
theorem milestone_o3_dynamics :
    (∀ {X E S E' : Type}
      (σ : Bridge.LedgerSheaf.DynamicsSection X E S E') ℓ,
      (σ.restrict ℓ).patch.alphabet.length = σ.patch.alphabet.length) ∧
    (∀ {X E S E' : Type}
      (σ τ : Bridge.LedgerSheaf.DynamicsSection X E S E'),
      Bridge.EinsteinSkeleton.OverlapCompatible σ.patch τ.patch →
      σ.patch.locus = τ.patch.locus →
        Bridge.EffectiveMatter.effectiveMatter σ.patch =
          Bridge.EffectiveMatter.effectiveMatter τ.patch) ∧
    Bridge.Alphabet.Kmin = 2 :=
  ⟨fun σ ℓ => Bridge.LedgerSheaf.dynamicsSection_restrict_capacity σ ℓ,
   fun σ τ hov hl => Bridge.LedgerSheaf.dynamicsSection_glue_matter σ τ hov hl,
   Bridge.Alphabet.Kmin_eq⟩

theorem milestone_r1_budget :
    (∀ d, 1 ≤ d →
      Bridge.RecombinationBudget.facesToFlatten d ≤
        Bridge.Capacity.caps d) ∧
    (¬ Bridge.RecombinationBudget.facesToFlatten 1 ≤
      Geom.Profile.capacityOf 2 Geom.Profile.expand 1) ∧
    Bridge.Alphabet.Kmin = 2 :=
  ⟨Bridge.RecombinationBudget.r1_faces_within_caps,
   Bridge.RecombinationBudget.r1_faces_exceed_expand_at_one,
   Bridge.Alphabet.Kmin_eq⟩

/-- Area-as-caps Bekenstein-shaped sharpening. -/
theorem milestone_area_as_caps :
    (∀ T, Bridge.Capacity.caps T = 2 ^ Bridge.Capacity.areaBits T) ∧
    (∀ T, 2 ^ T ≤ Bridge.Capacity.caps T) ∧
    (∀ T, Bridge.Capacity.areaBits (T + 1) =
      Bridge.Capacity.areaBits T + 1) ∧
    Bridge.Alphabet.Kmin = 2 :=
  ⟨Bridge.Capacity.areaBits_eq_log_caps, Bridge.Capacity.alive_arith,
   Bridge.Capacity.areaBits_succ, Bridge.Alphabet.Kmin_eq⟩

/-- Period-2 / KMS↔involution discrete caricature (not Unruh / continuum KMS). -/
theorem milestone_period2_kms :
    (∀ s, Revision.LiarRevision s → ∀ n, s (n + 2) = s n) ∧
    (∀ f b, Bridge.OneZ2.project f (Bridge.OneZ2.project f b) = b) ∧
    (∀ T, Bridge.PhaseEToys.combinatorialTemp T = 1) ∧
    Bridge.Alphabet.Kmin = 2 :=
  ⟨Bridge.Period2KMS.period2_orbit_under_swap,
   Bridge.Period2KMS.face_project_is_involution,
   fun _ => rfl,
   Bridge.Alphabet.Kmin_eq⟩

/-- Time–dissipation: Fund exempt ⇒ no naming ticks; arrow iff registration. -/
theorem milestone_time_dissipation :
    Bridge.TickSimulation.FundExempt ∧
    Bridge.EffectiveMatter.VacuumDynamics Geom.Registration.oscStep ∧
    Bridge.Alphabet.Kmin = 2 :=
  ⟨Bridge.TickSimulation.time_dissipation_one_property.1,
   Bridge.TickSimulation.time_dissipation_one_property.2.1,
   Bridge.Alphabet.Kmin_eq⟩

/-- O-2 cut-shift attempt: documented dead end (T_c blind to cut). -/
theorem milestone_o2_cut_shift :
    (∀ T, ∃ _c : Bridge.ModularCut.SaturatedCut T, True) ∧
    (∀ T (_c : Bridge.ModularCut.SaturatedCut T),
      Bridge.PhaseEToys.combinatorialTemp T = 1) ∧
    Bridge.Alphabet.Kmin = 2 :=
  ⟨Bridge.ModularCut.o2_cut_shift_dead_end.1,
   Bridge.ModularCut.o2_cut_shift_dead_end.2.2.1,
   Bridge.Alphabet.Kmin_eq⟩

/-- O-2 forced blindness: period global; one ℤ/2 ⇒ one flow; T_c cut-blind. -/
theorem milestone_o2_forced_blindness :
    (∀ T (_c : Bridge.ModularCut.SaturatedCut T),
      Bridge.PhaseEToys.combinatorialTemp T = 1) ∧
    Bridge.ModularCut.betaPeriod = 2 ∧
    Bridge.Alphabet.Kmin = 2 :=
  ⟨Bridge.ModularCut.o2_forced_blindness.1,
   Bridge.ModularCut.o2_forced_blindness.2.2.1,
   Bridge.Alphabet.Kmin_eq⟩

/-- Partial Lorentzian dictionary (order dim-1 + caps growth; no Lorentz group). -/
theorem milestone_partial_lorentzian :
    (∀ tTurn, Obs.Dimension.OrderDimEq tTurn
      (Obs.CausalOrder.fwdPrecedes tTurn) 1) ∧
    Bridge.Expansion.NumberEqualsVolume ∧
    Bridge.LorentzianDict.continuum_lorentzian_refused = True.intro ∧
    Bridge.Alphabet.Kmin = 2 :=
  ⟨Bridge.LorentzianDict.order_dim_one,
   Bridge.Expansion.number_equals_volume_flagged,
   rfl, Bridge.Alphabet.Kmin_eq⟩

theorem milestone_phase_E :
    (∀ T, Bridge.PhaseEToys.deltaS T = 1) ∧
    (∀ T, Bridge.PhaseEToys.heatQuantum T =
      Bridge.PhaseEToys.combinatorialTemp T * Bridge.PhaseEToys.deltaS T) ∧
    (∀ {K : Nat}, 2 ≤ K → ∀ tTurn,
      Geom.Profile.IsExhaustionTick K (Geom.Profile.bounce tTurn) tTurn) ∧
    (∀ T, Bridge.Capacity.caps (T + 1) = 2 * Bridge.Capacity.caps T) ∧
    Bridge.Alphabet.Kmin = 2 :=
  ⟨Bridge.PhaseEToys.deltaS_eq_one,
   Bridge.PhaseEToys.clausius_form,
   fun hK tTurn => Bridge.ArchiveMustSpeak.page_time_is_exhaustion hK tTurn,
   Bridge.PhaseEToys.caps_double,
   Bridge.Alphabet.Kmin_eq⟩

theorem bridge_arc :
    Bridge.Alphabet.Kmin = 2 ∧
    (∀ T, Bridge.Capacity.caps T = 2 ^ (T + 2)) ∧
    (∀ {S E : Type} {U : S × E → S × E},
      Geom.Registration.Inj U →
      Geom.Registration.Merges U →
      Geom.Registration.Registers U) ∧
    (∀ f : Bridge.OneZ2.Face, ∀ b : Bridge.OneZ2.Z2,
      Bridge.OneZ2.project f (Bridge.OneZ2.project f b) = b) ∧
    (∀ {S E : Type} {U : S × E → S × E},
      Geom.Registration.Inj U →
      ∀ w : Bridge.Environment.TwoMerge S E U,
        Bridge.RegistrationFactor.outsideSingleton
          (Bridge.Environment.recordLabel w false)
          (Bridge.Environment.recordLabel w true)) ∧
    (∀ T, 1 ≤ T → Density.levelCard 0 < Density.levelCard T) ∧
    (∀ {K : Nat}, 2 ≤ K → ∀ tTurn,
      Geom.Profile.IsExhaustionTick K (Geom.Profile.bounce tTurn) tTurn) ∧
    (∀ k : Nat, ¬ ∃ (f : Ladder.Level (k + 1) → Ladder.Level k),
      ∀ x y, f x = f y → x = y) ∧
    (∀ k (f : Ladder.Level k → Ladder.Level k → Bool),
      ∃ e₁ e₂ : Branch.Predicate k,
        Branch.IsEscape k f e₁ ∧ Branch.IsEscape k f e₂ ∧
          ∃ x, e₁ x ≠ e₂ x) ∧
    (∀ T, Bridge.Expansion.countedVolume 2 (T + 1) =
      2 * Bridge.Expansion.countedVolume 2 T) ∧
    Bridge.Forman.StrictlyNegative
      (Bridge.Forman.internalDeg 2) (Bridge.Forman.internalDeg 2) :=
  ⟨Bridge.Alphabet.Kmin_eq,
   Bridge.Capacity.caps_eq,
   fun hU hm => Bridge.RegistrationSpine.ag_merge_registers hU hm,
   Bridge.OneZ2.project_involution,
   fun hU w => (Bridge.RegistrationFactor.registers_admits_namer hU w).1,
   fun T hT =>
     (Bridge.RegistrationFactor.registration_vs_naming_obstruction).2.2.2 T hT,
   fun hK tTurn => Bridge.ArchiveMustSpeak.page_time_is_exhaustion hK tTurn,
   Bridge.SecondLaw.archive_irreversible,
   Bridge.Measurement.two_children,
   Bridge.Expansion.discrete_Hubble_one_bit_per_tick
     Bridge.Expansion.numberEqualsVolume,
   Bridge.Forman.internal_edge_forman_neg⟩

#print axioms milestone_M1
#print axioms milestone_M5
#print axioms milestone_keystone_dil
#print axioms milestone_dil_hom_exists
#print axioms milestone_dil_rigidity_iso
#print axioms milestone_dil_graded_terminality
#print axioms milestone_i2_caps_record_map
#print axioms milestone_i2_fin_closed
#print axioms milestone_ladder_predicate_addressing
#print axioms milestone_T2_tick_id_licensed
#print axioms milestone_T2_straighten
#print axioms milestone_T2_tick_id
#print axioms milestone_T2_tick_id_classified
#print axioms milestone_M4b
#print axioms milestone_T10
#print axioms milestone_T10_shape
#print axioms milestone_T11
#print axioms milestone_T12
#print axioms milestone_T12_measure
#print axioms milestone_born_nogo
#print axioms milestone_ollivier_trial
#print axioms milestone_T13
#print axioms milestone_T14
#print axioms milestone_T15
#print axioms milestone_T16
#print axioms milestone_effective_matter_sprint
#print axioms milestone_phase_D
#print axioms milestone_o3_glue
#print axioms milestone_o3_restrict
#print axioms milestone_o3_dynamics
#print axioms milestone_r1_budget
#print axioms milestone_phase_E
#print axioms milestone_area_as_caps
#print axioms milestone_period2_kms
#print axioms milestone_time_dissipation
#print axioms milestone_o2_cut_shift
#print axioms milestone_o2_forced_blindness
/-- I-1 two-bounce fragment (alias). Spine ¬erase; two-bounce ⇒ Inj;
    existence on involutions / Bool / swapStep / Fin n. Canonicity open. -/
theorem milestone_i1_two_bounce :
    (∀ {α : Type} (U : α → α) (_f : Bridge.TwoBounce.TwoBounceFactor U),
      Orbit.Lossless U) ∧
    (∀ {S E : Type} (U : S × E → S × E)
      (_f : Bridge.TwoBounce.TwoBounceFactor U), Geom.Registration.Inj U) ∧
    (∀ {α : Type} (U : α → α), Bridge.TwoBounce.IsInvolution U →
      Nonempty (Bridge.TwoBounce.TwoBounceFactor U)) ∧
    (∀ U : Bool → Bool, Bridge.TwoBounce.EndoInj U →
      Nonempty (Bridge.TwoBounce.TwoBounceFactor U)) ∧
    Nonempty (Bridge.TwoBounce.TwoBounceFactor Geom.Registration.swapStep) ∧
    (∀ {α : Type} (act : α → α), Orbit.SymmetricStep act → ¬ Orbit.Erasing act) ∧
    (∀ {n : Nat} (U : Fin n → Fin n), Bridge.TwoBounce.EndoInj U →
      Nonempty (Bridge.TwoBounce.TwoBounceFactor U)) :=
  Bridge.TwoBounce.i1_two_bounce_fragment

#print axioms milestone_partial_lorentzian
#print axioms milestone_i1_two_bounce
#print axioms bridge_arc

end Bridge.Arc
