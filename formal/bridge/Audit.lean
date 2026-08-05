import Alphabet
import Capacity
import OneZ2
import KernelAdmit
import RegistrationSpine
import TickSimulation
import Environment
import Dil
import RegistrationFactor
import ArchiveMustSpeak
import PageShape
import ArchiveMonotone
import BranchNondeterminism
import BranchMeasure
import LadderGrowth
import Forman
import Saturation
import FlatnessDebt
import FiberFlux
import FluxPattern
import LedgerPatchGlue
import RecombinationBudget
import PhaseEToys
import PeriodTwoOrbits
import CutShift
import OrderDimGrowth
import TwoBounce
import BridgeArc

/-!
# Audit — axiom footprint for `formal/bridge/`

Generated. Do not edit by hand:

```bash
python3 formal/tools/gen_audit.py
```

28 modules, 464 results. Source for `formal/AXIOMS.md`.
-/

-- Alphabet (7)
#print axioms Bridge.Alphabet.Kmin_eq
#print axioms Bridge.Alphabet.fundamental_forces_two
#print axioms Bridge.Alphabet.no_fundamental_above_two
#print axioms Bridge.Alphabet.fundamentals_only_at_two
#print axioms Bridge.Alphabet.alphabet_minimal
#print axioms Bridge.Alphabet.nonminimal_admissible
#print axioms Bridge.Alphabet.ag_poles_at_Kmin

-- Capacity (13)
#print axioms Bridge.Capacity.caps_eq
#print axioms Bridge.Capacity.levelCard_eq
#print axioms Bridge.Capacity.committed_is_expand
#print axioms Bridge.Capacity.alive_arith
#print axioms Bridge.Capacity.committed_alive_vs_caps
#print axioms Bridge.Capacity.expand_alive
#print axioms Bridge.Capacity.expand_capacity_two
#print axioms Bridge.Capacity.capacity_dictionary
#print axioms Bridge.Capacity.ancestry_survives
#print axioms Bridge.Capacity.areaBits_eq_log_caps
#print axioms Bridge.Capacity.demand_le_area
#print axioms Bridge.Capacity.areaBits_succ
#print axioms Bridge.Capacity.area_as_caps_sharpening

-- OneZ2 (12)
#print axioms Bridge.OneZ2.addressBit_roundtrip
#print axioms Bridge.OneZ2.bitAddress_roundtrip
#print axioms Bridge.OneZ2.address_two
#print axioms Bridge.OneZ2.channelBit_roundtrip
#print axioms Bridge.OneZ2.pole_swap_involution
#print axioms Bridge.OneZ2.address_swap_involution
#print axioms Bridge.OneZ2.channel_swap_involution
#print axioms Bridge.OneZ2.project_involution
#print axioms Bridge.OneZ2.dm_two_readings
#print axioms Bridge.OneZ2.one_Z2_three_faces
#print axioms Bridge.OneZ2.channel_swap_is_reversal
#print axioms Bridge.OneZ2.face_choice_is_packaging

-- KernelAdmit (6)
#print axioms Bridge.KernelAdmit.bool_admitted
#print axioms Bridge.KernelAdmit.boolCert_faceSwap_eq_swap
#print axioms Bridge.KernelAdmit.bool_admitted_faceSwap
#print axioms Bridge.KernelAdmit.bool_cert_face_equivariant
#print axioms Bridge.KernelAdmit.live_involution_cert
#print axioms Bridge.KernelAdmit.empty_mode_is_void_exclusion

-- RegistrationSpine (8)
#print axioms Bridge.RegistrationSpine.ag_merge_registers
#print axioms Bridge.RegistrationSpine.erasure_persists
#print axioms Bridge.RegistrationSpine.erasure_breaks
#print axioms Bridge.RegistrationSpine.fundamental_lossless
#print axioms Bridge.RegistrationSpine.ladder_names_compensation
#print axioms Bridge.RegistrationSpine.namer_outside_prior
#print axioms Bridge.RegistrationSpine.merge_forces_record_or_ascent
#print axioms Bridge.RegistrationSpine.registration_on_spine

-- TickSimulation (21)
#print axioms Bridge.TickSimulation.blank2_length
#print axioms Bridge.TickSimulation.naming_supplies_caps
#print axioms Bridge.TickSimulation.expand_eternally_alive
#print axioms Bridge.TickSimulation.demand_le_naming_caps
#print axioms Bridge.TickSimulation.committed_yields_mute
#print axioms Bridge.TickSimulation.expand_doubles
#print axioms Bridge.TickSimulation.caps_double
#print axioms Bridge.TickSimulation.naming_tick_new_slot
#print axioms Bridge.TickSimulation.naming_tick_extension
#print axioms Bridge.TickSimulation.committed_roundtrip_depth
#print axioms Bridge.TickSimulation.rate_weld
#print axioms Bridge.TickSimulation.oscillator_silent
#print axioms Bridge.TickSimulation.swap_writes
#print axioms Bridge.TickSimulation.tick_simulation
#print axioms Bridge.TickSimulation.tick_simulation_fragment
#print axioms Bridge.TickSimulation.tick_identification_licensed
#print axioms Bridge.TickSimulation.tick_identification_ingredients
#print axioms Bridge.TickSimulation.tick_identification_step
#print axioms Bridge.TickSimulation.tick_identification_dichotomy
#print axioms Bridge.TickSimulation.tick_identification
#print axioms Bridge.TickSimulation.time_dissipation_one_property

-- Environment (15)
#print axioms Bridge.Environment.capCount_eq
#print axioms Bridge.Environment.env_card
#print axioms Bridge.Environment.env_ge_Kmin
#print axioms Bridge.Environment.env_exists
#print axioms Bridge.Environment.recordLabel_injective
#print axioms Bridge.Environment.boolCoord_inj
#print axioms Bridge.Environment.boolCoord_surj
#print axioms Bridge.Environment.two_carrier_reads_as_bool
#print axioms Bridge.Environment.merges_yields_twoMerge
#print axioms Bridge.Environment.swap_is_completion
#print axioms Bridge.Environment.minimal_alphabet_is_Kmin
#print axioms Bridge.Environment.alphabet_ge_two
#print axioms Bridge.Environment.ladder_strict_growth
#print axioms Bridge.Environment.environment_universality
#print axioms Bridge.Environment.environment_universality_fragment

-- Dil (74)
#print axioms Bridge.Dil.Word.prepend_eq
#print axioms Bridge.Dil.interpret_nil
#print axioms Bridge.Dil.interpret_cons
#print axioms Bridge.Dil.freeHom_unique
#print axioms Bridge.Dil.free_initial
#print axioms Bridge.Dil.record_inj_on_fiber
#print axioms Bridge.Dil.record_images_disjoint
#print axioms Bridge.Dil.recordImage_length
#print axioms Bridge.Dil.recordImage_distinct
#print axioms Bridge.Dil.capacity_step
#print axioms Bridge.Dil.capacity_law
#print axioms Bridge.Dil.registration
#print axioms Bridge.Dil.archive_registers
#print axioms Bridge.Dil.minimal_schedule_closed_form
#print axioms Bridge.Dil.predicate_minimal_schedule
#print axioms Bridge.Dil.caps_realise_minimal_schedule
#print axioms Bridge.Dil.distinct_subset_eq_length_covers
#print axioms Bridge.Dil.minimal_step_covers
#print axioms Bridge.Dil.minimal_block_size
#print axioms Bridge.Dil.rigidity_partition_fragment
#print axioms Bridge.Dil.free_reachable
#print axioms Bridge.Dil.hom_unique_on_reachable
#print axioms Bridge.Dil.hom_unique_reduced
#print axioms Bridge.Dil.free_hom_unique_by_z0
#print axioms Bridge.Dil.inductive_carrier_reachable
#print axioms Bridge.Dil.at_most_one_hom_recordGenerated
#print axioms Bridge.Dil.recordGenerated_of_minimal_cover
#print axioms Bridge.Dil.mapFromUF_nat
#print axioms Bridge.Dil.history_section
#print axioms Bridge.Dil.historyWord_step
#print axioms Bridge.Dil.hom_exists_of_UF
#print axioms Bridge.Dil.free_always_factors
#print axioms Bridge.Dil.free_is_pointed_singleton
#print axioms Bridge.Dil.free_hom_exists_via_UF
#print axioms Bridge.Dil.history_retract
#print axioms Bridge.Dil.rigidity_iso_of_UF
#print axioms Bridge.Dil.free_rigidity_self
#print axioms Bridge.Dil.uf_pointed_carrier_reachable
#print axioms Bridge.Dil.at_most_one_hom_of_UF
#print axioms Bridge.Dil.Hom.ext
#print axioms Bridge.Dil.graded_terminality_of_UF
#print axioms Bridge.Dil.free_terminal_among_UF
#print axioms Bridge.Dil.joint_inj_of_addressUniform
#print axioms Bridge.Dil.capCard_succ
#print axioms Bridge.Dil.capCard_pos
#print axioms Bridge.Dil.capRecord_val_false
#print axioms Bridge.Dil.capRecord_val_true
#print axioms Bridge.Dil.capRecord_inj
#print axioms Bridge.Dil.cap_high_tail_lt
#print axioms Bridge.Dil.capFactor_of_lt
#print axioms Bridge.Dil.capFactor_of_ge
#print axioms Bridge.Dil.capFactor_reconstruct
#print axioms Bridge.Dil.capFactor_unique
#print axioms Bridge.Dil.boolCaps_not_pointedSingleton
#print axioms Bridge.Dil.boolCaps_card_eq_caps
#print axioms Bridge.Dil.boolCaps_registers
#print axioms Bridge.Dil.hom_unique_of_UF
#print axioms Bridge.Dil.mapFromUF_left_inv
#print axioms Bridge.Dil.graded_terminality_of_base
#print axioms Bridge.Dil.freeOnBase_append_step
#print axioms Bridge.Dil.freeOnBase_factor_cons
#print axioms Bridge.Dil.factorHistory_step
#print axioms Bridge.Dil.factorHistory_section
#print axioms Bridge.Dil.factorHistory_retract
#print axioms Bridge.Dil.uf_straightens_mod_base
#print axioms Bridge.Dil.uf_pointed_straightens_to_free
#print axioms Bridge.Dil.record_gauge_is_base_bijection
#print axioms Bridge.Dil.boolCaps_straightens_mod_base
#print axioms Bridge.Dil.straighten_fragment
#print axioms Bridge.Dil.i2_fin_closed
#print axioms Bridge.Dil.i2_caps_record_map_fragment
#print axioms Bridge.Dil.boolCaps_joint_inj_via_addressUniform
#print axioms Bridge.Dil.ladder_predicate_addressing_witness
#print axioms Bridge.Dil.keystone_dil_sprint

-- RegistrationFactor (11)
#print axioms Bridge.RegistrationFactor.outsideSingleton_iff
#print axioms Bridge.RegistrationFactor.registers_admits_namer
#print axioms Bridge.RegistrationFactor.registers_namer_is_new
#print axioms Bridge.RegistrationFactor.swap_factors_as_namer
#print axioms Bridge.RegistrationFactor.oscillator_no_namer_demand
#print axioms Bridge.RegistrationFactor.swap_registers_every_tick
#print axioms Bridge.RegistrationFactor.naming_carrier_card
#print axioms Bridge.RegistrationFactor.naming_card_strict
#print axioms Bridge.RegistrationFactor.swap_env_card_fixed
#print axioms Bridge.RegistrationFactor.registration_vs_naming_obstruction
#print axioms Bridge.RegistrationFactor.registration_naming_factorisation

-- ArchiveMustSpeak (5)
#print axioms Bridge.ArchiveMustSpeak.archive_must_speak
#print axioms Bridge.ArchiveMustSpeak.page_time_is_exhaustion
#print axioms Bridge.ArchiveMustSpeak.thermal_window_then_speech
#print axioms Bridge.ArchiveMustSpeak.eternal_mute_needs_unbounded
#print axioms Bridge.ArchiveMustSpeak.T10_archive_must_speak

-- PageShape (11)
#print axioms Bridge.PageShape.stream_mute_before
#print axioms Bridge.PageShape.stream_tracks_after
#print axioms Bridge.PageShape.occupancy_fill
#print axioms Bridge.PageShape.occupancy_plateau
#print axioms Bridge.PageShape.succ_sub_self
#print axioms Bridge.PageShape.exhaustion_predicted
#print axioms Bridge.PageShape.first_speech_bound
#print axioms Bridge.PageShape.pageTent_peak
#print axioms Bridge.PageShape.expand_never_exhausts
#print axioms Bridge.PageShape.bounce_page_time
#print axioms Bridge.PageShape.T10_page_flux_shape

-- ArchiveMonotone (5)
#print axioms Bridge.ArchiveMonotone.merge_must_register
#print axioms Bridge.ArchiveMonotone.records_embed
#print axioms Bridge.ArchiveMonotone.archive_irreversible
#print axioms Bridge.ArchiveMonotone.erasure_priced
#print axioms Bridge.ArchiveMonotone.T11_archive_monotonicity

-- BranchNondeterminism (5)
#print axioms Bridge.BranchNondeterminism.two_children
#print axioms Bridge.BranchNondeterminism.ascent_free
#print axioms Bridge.BranchNondeterminism.histories_diverge
#print axioms Bridge.BranchNondeterminism.no_selection_mechanism
#print axioms Bridge.BranchNondeterminism.T12_branch_nondeterminism

-- BranchMeasure (14)
#print axioms Bridge.BranchMeasure.uniform_total_is_Kmin
#print axioms Bridge.BranchMeasure.uniform_weights_equal
#print axioms Bridge.BranchMeasure.no_unique_law_selector
#print axioms Bridge.BranchMeasure.caps_blind_to_escape
#print axioms Bridge.BranchMeasure.T12_measure_fragment
#print axioms Bridge.BranchMeasure.multiplicity_forces_symmetry
#print axioms Bridge.BranchMeasure.pathWeight_symmetric
#print axioms Bridge.BranchMeasure.born_asymmetry_unavailable
#print axioms Bridge.BranchMeasure.born_from_multiplicity_nogo
#print axioms Bridge.BranchMeasure.sibling_transport_cost_pos
#print axioms Bridge.BranchMeasure.sibling_transport_ge_edge
#print axioms Bridge.BranchMeasure.uniform_mass_preserves_forman_neg
#print axioms Bridge.BranchMeasure.transport_children
#print axioms Bridge.BranchMeasure.transport_trial_fragment

-- LadderGrowth (14)
#print axioms Bridge.LadderGrowth.E1_namer_always_new
#print axioms Bridge.LadderGrowth.E1_no_retraction
#print axioms Bridge.LadderGrowth.E1_lift_injective
#print axioms Bridge.LadderGrowth.E1_monotone_structure
#print axioms Bridge.LadderGrowth.E2_rate_law
#print axioms Bridge.LadderGrowth.E2_liveness_forces_expansion
#print axioms Bridge.LadderGrowth.E2_expand_eternally_alive
#print axioms Bridge.LadderGrowth.E2_exponential_capacity
#print axioms Bridge.LadderGrowth.ascent_order_dim_one
#print axioms Bridge.LadderGrowth.omega_flatline_ancestry_continues
#print axioms Bridge.LadderGrowth.number_equals_volume_flagged
#print axioms Bridge.LadderGrowth.doubling_per_tick_at_Kmin
#print axioms Bridge.LadderGrowth.counted_capacity_at_Kmin
#print axioms Bridge.LadderGrowth.T13_counted_growth

-- Forman (21)
#print axioms Bridge.Forman.Kmin_internal_deg
#print axioms Bridge.Forman.four_lt_five
#print axioms Bridge.Forman.four_lt_six
#print axioms Bridge.Forman.root_edge_forman_neg
#print axioms Bridge.Forman.internal_edge_forman_neg
#print axioms Bridge.Forman.Kmin_tree_edges_forman_neg
#print axioms Bridge.Forman.faced_zero_iff
#print axioms Bridge.Forman.recombination_raises_quantity
#print axioms Bridge.Forman.recombination_weakens_negativity
#print axioms Bridge.Forman.five_lt_six
#print axioms Bridge.Forman.internal_still_neg_at_one_face
#print axioms Bridge.Forman.internal_not_neg_at_two_faces
#print axioms Bridge.Forman.internal_flat_budget
#print axioms Bridge.Forman.toy_line_not_neg
#print axioms Bridge.Forman.toy_tree_neg
#print axioms Bridge.Forman.toy_filled_not_neg
#print axioms Bridge.Forman.toy_fill_costs_two
#print axioms Bridge.Forman.worked_recombination_complex
#print axioms Bridge.Forman.live_forbids_flat_profile
#print axioms Bridge.Forman.curvature_precluded_only_on_the_line
#print axioms Bridge.Forman.T14_forman_tree_curvature

-- Saturation (5)
#print axioms Bridge.Saturation.alive_iff_records_le_caps
#print axioms Bridge.Saturation.saturation_iff_tick_equality
#print axioms Bridge.Saturation.saturated_flux_fixed_by_capacity
#print axioms Bridge.Saturation.capacity_schedule_unique
#print axioms Bridge.Saturation.T15_saturation_balance

-- FlatnessDebt (14)
#print axioms Bridge.FlatnessDebt.unpaid_of_neg
#print axioms Bridge.FlatnessDebt.unpaid_zero_iff_not_neg
#print axioms Bridge.FlatnessDebt.face_pays_one
#print axioms Bridge.FlatnessDebt.curvature_relief_costs_records
#print axioms Bridge.FlatnessDebt.Kmin_flatness_threshold
#print axioms Bridge.FlatnessDebt.flux_eq_capacity_at_saturation
#print axioms Bridge.FlatnessDebt.overlap_refl
#print axioms Bridge.FlatnessDebt.overlap_symm
#print axioms Bridge.FlatnessDebt.patch_saturation_balance
#print axioms Bridge.FlatnessDebt.local_frame_width
#print axioms Bridge.FlatnessDebt.local_seal
#print axioms Bridge.FlatnessDebt.openGaps_complete
#print axioms Bridge.FlatnessDebt.balance_inputs_discharged
#print axioms Bridge.FlatnessDebt.T16_flatness_debt_package

-- FiberFlux (15)
#print axioms Bridge.FiberFlux.fiberFlux_eq_fiber
#print axioms Bridge.FiberFlux.fiberFlux_eq_capacity_at_saturation
#print axioms Bridge.FiberFlux.osc_is_silent
#print axioms Bridge.FiberFlux.silent_no_merges
#print axioms Bridge.FiberFlux.silent_no_registers
#print axioms Bridge.FiberFlux.silent_mute
#print axioms Bridge.FiberFlux.fluxBearing_has_flux
#print axioms Bridge.FiberFlux.fluxBearing_eq_capacity
#print axioms Bridge.FiberFlux.swap_admits_flux_channel
#print axioms Bridge.FiberFlux.silent_vs_flux_channel_separable
#print axioms Bridge.FiberFlux.slack_below_saturation
#print axioms Bridge.FiberFlux.recombinationsNeeded_kmin_internal
#print axioms Bridge.FiberFlux.kmin_flatness_within_caps_budget
#print axioms Bridge.FiberFlux.kmin_flatness_within_expand_budget
#print axioms Bridge.FiberFlux.fiber_flux_sprint

-- FluxPattern (10)
#print axioms Bridge.FluxPattern.bool_components_nondegenerate
#print axioms Bridge.FluxPattern.two_nondegenerate_flux_components
#print axioms Bridge.FluxPattern.channels_index_distinct_components
#print axioms Bridge.FluxPattern.channel_multiplicity
#print axioms Bridge.FluxPattern.branch_species_width
#print axioms Bridge.FluxPattern.component_multiplicity_from_underdetermination
#print axioms Bridge.FluxPattern.silent_onset_skeleton
#print axioms Bridge.FluxPattern.flux_onset_registration
#print axioms Bridge.FluxPattern.silent_vs_flux_onset
#print axioms Bridge.FluxPattern.phase_D_flux_patterns

-- LedgerPatchGlue (19)
#print axioms Bridge.LedgerPatchGlue.cover_compatible_refl
#print axioms Bridge.LedgerPatchGlue.glue_capacity_on_locus
#print axioms Bridge.LedgerPatchGlue.cover_glue_capacity
#print axioms Bridge.LedgerPatchGlue.glue_fiberFlux_at_saturation_length
#print axioms Bridge.LedgerPatchGlue.two_patch_cover_compatible
#print axioms Bridge.LedgerPatchGlue.restrict_preserves_capacity
#print axioms Bridge.LedgerPatchGlue.restrict_preserves_fiber
#print axioms Bridge.LedgerPatchGlue.restrict_preserves_effectiveMatter
#print axioms Bridge.LedgerPatchGlue.restrict_idempotent_data
#print axioms Bridge.LedgerPatchGlue.restrict_overlap_of_cap
#print axioms Bridge.LedgerPatchGlue.restrict_preserves_balance
#print axioms Bridge.LedgerPatchGlue.o3_stalk_glue_fragment
#print axioms Bridge.LedgerPatchGlue.o3_restriction_fragment
#print axioms Bridge.LedgerPatchGlue.dynamicsSection_restrict_capacity
#print axioms Bridge.LedgerPatchGlue.dynamicsSection_restrict_matter
#print axioms Bridge.LedgerPatchGlue.dynamicsSection_glue_capacity
#print axioms Bridge.LedgerPatchGlue.dynamicsSection_glue_matter
#print axioms Bridge.LedgerPatchGlue.dynamicsSection_cover_compatible
#print axioms Bridge.LedgerPatchGlue.o3_dynamics_section_fragment

-- RecombinationBudget (7)
#print axioms Bridge.RecombinationBudget.perEdgeCost_eq_two
#print axioms Bridge.RecombinationBudget.faces_closed_form
#print axioms Bridge.RecombinationBudget.r1_faces_within_caps
#print axioms Bridge.RecombinationBudget.r1_faces_exceed_expand_at_one
#print axioms Bridge.RecombinationBudget.per_edge_within_aliveness
#print axioms Bridge.RecombinationBudget.r1_census_depth_one
#print axioms Bridge.RecombinationBudget.r1_recombination_budget_fragment

-- PhaseEToys (14)
#print axioms Bridge.PhaseEToys.entropyBits_eq_log_caps
#print axioms Bridge.PhaseEToys.deltaS_eq_one
#print axioms Bridge.PhaseEToys.clausius_caricature
#print axioms Bridge.PhaseEToys.clausius_form
#print axioms Bridge.PhaseEToys.page_radiation_horizon
#print axioms Bridge.PhaseEToys.page_radiation_thermal_then_speech
#print axioms Bridge.PhaseEToys.radiation_is_matter_channel
#print axioms Bridge.PhaseEToys.finite_page_radiation
#print axioms Bridge.PhaseEToys.deltaScale_eq_one
#print axioms Bridge.PhaseEToys.hubble_disc_eq_one
#print axioms Bridge.PhaseEToys.caps_double
#print axioms Bridge.PhaseEToys.volume_double
#print axioms Bridge.PhaseEToys.friedmann_shaped_capacity_update
#print axioms Bridge.PhaseEToys.phase_E_continuum_toys

-- PeriodTwoOrbits (7)
#print axioms Bridge.PeriodTwoOrbits.period2_orbit_under_swap
#print axioms Bridge.PeriodTwoOrbits.face_project_is_involution
#print axioms Bridge.PeriodTwoOrbits.observe_flips_under_involution
#print axioms Bridge.PeriodTwoOrbits.swapStep_involution
#print axioms Bridge.PeriodTwoOrbits.temp_constant_by_definition
#print axioms Bridge.PeriodTwoOrbits.heat_balance_by_definition
#print axioms Bridge.PeriodTwoOrbits.period_two_package

-- CutShift (8)
#print axioms Bridge.CutShift.correlator_period2_stationary
#print axioms Bridge.CutShift.cut_period_stationarity
#print axioms Bridge.CutShift.cut_temp_independent
#print axioms Bridge.CutShift.cut_shift_temp_independent
#print axioms Bridge.CutShift.area_blind_to_cut
#print axioms Bridge.CutShift.no_unruh_from_cut
#print axioms Bridge.CutShift.o2_forced_blindness
#print axioms Bridge.CutShift.o2_cut_shift_dead_end

-- OrderDimGrowth (5)
#print axioms Bridge.OrderDimGrowth.order_dim_one
#print axioms Bridge.OrderDimGrowth.counted_volume_growth
#print axioms Bridge.OrderDimGrowth.only_Z2_underdetermination
#print axioms Bridge.OrderDimGrowth.omega_shape_echo
#print axioms Bridge.OrderDimGrowth.order_dim_growth_package

-- TwoBounce (77)
#print axioms Bridge.TwoBounce.involution_of_symmetric
#print axioms Bridge.TwoBounce.symmetric_of_involution
#print axioms Bridge.TwoBounce.involution_injective
#print axioms Bridge.TwoBounce.involution_not_erasing
#print axioms Bridge.TwoBounce.symmetric_excludes_erase
#print axioms Bridge.TwoBounce.lossless_of_two_bounce
#print axioms Bridge.TwoBounce.inj_of_two_bounce
#print axioms Bridge.TwoBounce.bool_inj_involution
#print axioms Bridge.TwoBounce.swapStep_involution
#print axioms Bridge.TwoBounce.nat_sub_self_add
#print axioms Bridge.TwoBounce.nat_add_sub_cancel_left
#print axioms Bridge.TwoBounce.nat_add_one_right
#print axioms Bridge.TwoBounce.nat_sub_one_right
#print axioms Bridge.TwoBounce.nat_sub_add_cancel
#print axioms Bridge.TwoBounce.nat_add_sub_of_le
#print axioms Bridge.TwoBounce.nat_sub_pos_of_lt
#print axioms Bridge.TwoBounce.nat_sub_sub
#print axioms Bridge.TwoBounce.nat_sub_sub_self
#print axioms Bridge.TwoBounce.nat_sub_le_sub_left
#print axioms Bridge.TwoBounce.nat_sub_add_comm
#print axioms Bridge.TwoBounce.firstBelow_some
#print axioms Bridge.TwoBounce.firstBelow_none
#print axioms Bridge.TwoBounce.firstBelow_least
#print axioms Bridge.TwoBounce.pairFind_some
#print axioms Bridge.TwoBounce.pairFind_none
#print axioms Bridge.TwoBounce.fin_collides_bounded
#print axioms Bridge.TwoBounce.fin_collides
#print axioms Bridge.TwoBounce.fin_returns
#print axioms Bridge.TwoBounce.fin_returns_le
#print axioms Bridge.TwoBounce.minPeriod_spec
#print axioms Bridge.TwoBounce.minPeriod_pos
#print axioms Bridge.TwoBounce.minPeriod_return
#print axioms Bridge.TwoBounce.minPeriod_least
#print axioms Bridge.TwoBounce.exists_min_period
#print axioms Bridge.TwoBounce.iter_reduce
#print axioms Bridge.TwoBounce.orbit_distinct
#print axioms Bridge.TwoBounce.minPeriod_iter
#print axioms Bridge.TwoBounce.iter_mul_period
#print axioms Bridge.TwoBounce.iter_mod_period
#print axioms Bridge.TwoBounce.exists_argmin
#print axioms Bridge.TwoBounce.argminBelow_lt
#print axioms Bridge.TwoBounce.argminBelow_min
#print axioms Bridge.TwoBounce.exists_orbit_base
#print axioms Bridge.TwoBounce.orbitBase_mem
#print axioms Bridge.TwoBounce.orbitBase_min
#print axioms Bridge.TwoBounce.cycle_add_id
#print axioms Bridge.TwoBounce.cycle_reach
#print axioms Bridge.TwoBounce.orbitBase_iter
#print axioms Bridge.TwoBounce.orbitBase_idem
#print axioms Bridge.TwoBounce.exists_index
#print axioms Bridge.TwoBounce.indexOf_spec
#print axioms Bridge.TwoBounce.indexOf_lt
#print axioms Bridge.TwoBounce.indexOf_iter
#print axioms Bridge.TwoBounce.reflect_idx
#print axioms Bridge.TwoBounce.reflect_idx_involutive
#print axioms Bridge.TwoBounce.succ_pred_idx
#print axioms Bridge.TwoBounce.orbitBase_of_bounceφ
#print axioms Bridge.TwoBounce.indexOf_bounceφ
#print axioms Bridge.TwoBounce.bounceφ_involution
#print axioms Bridge.TwoBounce.bounceσ_eq_iter
#print axioms Bridge.TwoBounce.bounceσ_involution
#print axioms Bridge.TwoBounce.not_involution
#print axioms Bridge.TwoBounce.not_endoInj
#print axioms Bridge.TwoBounce.involutive_factor_reorder
#print axioms Bridge.TwoBounce.canonicity_fails
#print axioms Bridge.TwoBounce.left_inv_of_factor
#print axioms Bridge.TwoBounce.right_inv_of_factor
#print axioms Bridge.TwoBounce.channel_swap_is_reversal
#print axioms Bridge.TwoBounce.reverseOf_eq_of_involution
#print axioms Bridge.TwoBounce.cycle3_inj
#print axioms Bridge.TwoBounce.reflect0_involution
#print axioms Bridge.TwoBounce.reflect1_involution
#print axioms Bridge.TwoBounce.cycle3_reflect0_involution
#print axioms Bridge.TwoBounce.cycle3_reflect1_involution
#print axioms Bridge.TwoBounce.factorization_gauge_exceeds_swap
#print axioms Bridge.TwoBounce.i1_canonicity_package
#print axioms Bridge.TwoBounce.i1_two_bounce_fragment

-- BridgeArc (41)
#print axioms Bridge.Arc.milestone_M1
#print axioms Bridge.Arc.milestone_M2
#print axioms Bridge.Arc.milestone_M4
#print axioms Bridge.Arc.milestone_M5
#print axioms Bridge.Arc.milestone_keystone_dil
#print axioms Bridge.Arc.milestone_dil_hom_exists
#print axioms Bridge.Arc.milestone_dil_rigidity_iso
#print axioms Bridge.Arc.milestone_dil_graded_terminality
#print axioms Bridge.Arc.milestone_i2_caps_record_map
#print axioms Bridge.Arc.milestone_i2_fin_closed
#print axioms Bridge.Arc.milestone_ladder_predicate_addressing
#print axioms Bridge.Arc.milestone_T2_tick_id_licensed
#print axioms Bridge.Arc.milestone_T2_straighten
#print axioms Bridge.Arc.milestone_T2_tick_id
#print axioms Bridge.Arc.milestone_M4b
#print axioms Bridge.Arc.milestone_T10
#print axioms Bridge.Arc.milestone_T10_shape
#print axioms Bridge.Arc.milestone_T11
#print axioms Bridge.Arc.milestone_T12
#print axioms Bridge.Arc.milestone_T12_measure
#print axioms Bridge.Arc.milestone_born_nogo
#print axioms Bridge.Arc.milestone_transport_trial
#print axioms Bridge.Arc.milestone_T13
#print axioms Bridge.Arc.milestone_T14
#print axioms Bridge.Arc.milestone_T15
#print axioms Bridge.Arc.milestone_T16
#print axioms Bridge.Arc.milestone_fiber_flux_sprint
#print axioms Bridge.Arc.milestone_phase_D
#print axioms Bridge.Arc.milestone_o3_glue
#print axioms Bridge.Arc.milestone_o3_restrict
#print axioms Bridge.Arc.milestone_o3_dynamics
#print axioms Bridge.Arc.milestone_r1_budget
#print axioms Bridge.Arc.milestone_area_as_caps
#print axioms Bridge.Arc.milestone_period_two
#print axioms Bridge.Arc.milestone_time_dissipation
#print axioms Bridge.Arc.milestone_o2_cut_shift
#print axioms Bridge.Arc.milestone_o2_forced_blindness
#print axioms Bridge.Arc.milestone_order_dim_growth
#print axioms Bridge.Arc.milestone_phase_E
#print axioms Bridge.Arc.bridge_arc
#print axioms Bridge.Arc.milestone_i1_two_bounce
