import Geom.Core
import Geom.Registration
import Geom.Ledger
import Geom.Exhaustion
import Geom.Provision
import Geom.Bounce
import Geom.Profile
import Geom.Gradient
import Geom.Totality
import Geom.Freshness
import Geom.Arc
import Obs.AbstractMemory
import Obs.MergeMonotone
import Obs.EffectiveDynamics
import Obs.Unlock
import Obs.UnlockCompleteness
import Obs.UnlockPricing
import Obs.Recovery
import Obs.CausalOrder
import Obs.Dimension
import Obs.Selection
import Obs.StochasticUnlock
import Obs.TotalVariationDPI
import Obs.StochasticDivergence
import Obs.Budget
import Obs.ContinuumUnlock
import Obs.EmbeddedObserver

/-!
# Audit — axiom footprint for `formal/ledger/`

Generated. Do not edit by hand:

```bash
python3 formal/tools/gen_audit.py
```

27 modules, 454 results. Source for `formal/AXIOMS.md`.
-/

-- Geom.Core (3)
#print axioms Geom.Core.stage_ge_charter
#print axioms Geom.Core.stage_is_v1
#print axioms Geom.Core.version_major_one

-- Geom.Registration (20)
#print axioms Geom.Registration.pair_ext
#print axioms Geom.Registration.merge_registers
#print axioms Geom.Registration.no_write_no_merge
#print axioms Geom.Registration.merge_pair_registers
#print axioms Geom.Registration.osc_inj
#print axioms Geom.Registration.osc_never_registers
#print axioms Geom.Registration.swap_inj
#print axioms Geom.Registration.swap_registers
#print axioms Geom.Registration.registration_independent
#print axioms Geom.Registration.mem_head
#print axioms Geom.Registration.mem_tail
#print axioms Geom.Registration.length_remove_of_mem
#print axioms Geom.Registration.mem_remove
#print axioms Geom.Registration.findEq_some
#print axioms Geom.Registration.findEq_none
#print axioms Geom.Registration.pigeonhole_list
#print axioms Geom.Registration.upto_lt
#print axioms Geom.Registration.upto_distinct
#print axioms Geom.Registration.upto_length
#print axioms Geom.Registration.finite_carrier_collision

-- Geom.Ledger (13)
#print axioms Geom.Ledger.mem_head
#print axioms Geom.Ledger.mem_tail
#print axioms Geom.Ledger.length_remove_of_mem
#print axioms Geom.Ledger.mem_remove
#print axioms Geom.Ledger.length_le_of_distinct_mem
#print axioms Geom.Ledger.exists_of_mem_map
#print axioms Geom.Ledger.length_map_eq
#print axioms Geom.Ledger.pair_ext
#print axioms Geom.Ledger.env_records_distinct
#print axioms Geom.Ledger.env_records_distinct_list
#print axioms Geom.Ledger.alphabet_ge_indegree
#print axioms Geom.Ledger.alphabet_ge_indegree_exhaustive
#print axioms Geom.Ledger.merge_registers_is_ledger_pair

-- Geom.Exhaustion (37)
#print axioms Geom.Exhaustion.mem_head
#print axioms Geom.Exhaustion.mem_tail
#print axioms Geom.Exhaustion.length_remove_of_mem
#print axioms Geom.Exhaustion.mem_remove
#print axioms Geom.Exhaustion.length_le_of_distinct_mem
#print axioms Geom.Exhaustion.exists_of_mem_map
#print axioms Geom.Exhaustion.length_map_eq
#print axioms Geom.Exhaustion.mem_append_left
#print axioms Geom.Exhaustion.mem_append_right
#print axioms Geom.Exhaustion.mem_append_elim
#print axioms Geom.Exhaustion.length_append
#print axioms Geom.Exhaustion.distinct_append
#print axioms Geom.Exhaustion.distinct_map_of_inj
#print axioms Geom.Exhaustion.mem_joinMap
#print axioms Geom.Exhaustion.distinct_joinMap
#print axioms Geom.Exhaustion.length_joinMap_ge
#print axioms Geom.Exhaustion.snoc_inj
#print axioms Geom.Exhaustion.succ_add_eq
#print axioms Geom.Exhaustion.pow_mono
#print axioms Geom.Exhaustion.exists_lt_not_of_not_forall
#print axioms Geom.Exhaustion.exists_mem_not_of_not_ball
#print axioms Geom.Exhaustion.triple_ext
#print axioms Geom.Exhaustion.buffer_absorbs
#print axioms Geom.Exhaustion.buffer_records_distinct
#print axioms Geom.Exhaustion.buffer_capacity_bound
#print axioms Geom.Exhaustion.freshVecs_zero_mem
#print axioms Geom.Exhaustion.freshVecs_length_mem
#print axioms Geom.Exhaustion.evolve_snoc
#print axioms Geom.Exhaustion.evolve_confined
#print axioms Geom.Exhaustion.evolve_inj
#print axioms Geom.Exhaustion.freshVecs_distinct
#print axioms Geom.Exhaustion.freshVecs_length_ge
#print axioms Geom.Exhaustion.exhaustion
#print axioms Geom.Exhaustion.freshness_fails
#print axioms Geom.Exhaustion.exhaustion_const
#print axioms Geom.Exhaustion.alive_downclosed
#print axioms Geom.Exhaustion.exhaustion_tick_antitone

-- Geom.Provision (25)
#print axioms Geom.Provision.append_nil
#print axioms Geom.Provision.append_assoc
#print axioms Geom.Provision.mem_map_intro
#print axioms Geom.Provision.mem_joinMap_intro
#print axioms Geom.Provision.length_joinMap_eq
#print axioms Geom.Provision.freshVecs_length_eq
#print axioms Geom.Provision.two_pow_pos
#print axioms Geom.Provision.lt_two_pow
#print axioms Geom.Provision.two_pow_le_pow
#print axioms Geom.Provision.capacity_lt_pow
#print axioms Geom.Provision.expand_inj
#print axioms Geom.Provision.expand_merges_at
#print axioms Geom.Provision.expand_fresh_at
#print axioms Geom.Provision.expand_confined
#print axioms Geom.Provision.capacity_production
#print axioms Geom.Provision.expand_capacity
#print axioms Geom.Provision.alive_everywhere
#print axioms Geom.Provision.provision
#print axioms Geom.Provision.evolve_expand_append
#print axioms Geom.Provision.archive_is_transcript
#print axioms Geom.Provision.archive_length
#print axioms Geom.Provision.eternal_aliveness_needs_expansion
#print axioms Geom.Provision.no_static_eternal_aliveness
#print axioms Geom.Provision.expandTick_inj
#print axioms Geom.Provision.expandRecords_length

-- Geom.Bounce (17)
#print axioms Geom.Bounce.bounceDepth_asc
#print axioms Geom.Bounce.bounceDepth_turn
#print axioms Geom.Bounce.bounceDepth_past
#print axioms Geom.Bounce.bounceDepth_desc
#print axioms Geom.Bounce.lt_of_not_le
#print axioms Geom.Bounce.pow_lt_succ
#print axioms Geom.Bounce.pow_le_pow_of_le
#print axioms Geom.Bounce.pow_lt_pow_of_lt
#print axioms Geom.Bounce.pow_le_pow_iff_le
#print axioms Geom.Bounce.alive_iff_le_depth
#print axioms Geom.Bounce.alive_upto_turn
#print axioms Geom.Bounce.two_mul_eq_add
#print axioms Geom.Bounce.add_sub_of_le
#print axioms Geom.Bounce.desc_le_implies_le_turn
#print axioms Geom.Bounce.not_alive_past_turn
#print axioms Geom.Bounce.exhaustion_tick_eq_turnaround
#print axioms Geom.Bounce.turnaround_alive

-- Geom.Profile (7)
#print axioms Geom.Profile.flat_const
#print axioms Geom.Profile.expand_diag
#print axioms Geom.Profile.bounce_eq
#print axioms Geom.Profile.bounce_alive_iff
#print axioms Geom.Profile.expand_capacity_weld
#print axioms Geom.Profile.exhaustion_tick_unique
#print axioms Geom.Profile.bounce_exhaustion_tick

-- Geom.Gradient (12)
#print axioms Geom.Gradient.add_sub_self
#print axioms Geom.Gradient.add_sub_self_left
#print axioms Geom.Gradient.sub_add_self
#print axioms Geom.Gradient.le_cancel_left
#print axioms Geom.Gradient.add_cancel_right
#print axioms Geom.Gradient.eternal_aliveness_needs_gradient
#print axioms Geom.Gradient.succ_add_succ
#print axioms Geom.Gradient.bounce_symm
#print axioms Geom.Gradient.rev_depth_eq
#print axioms Geom.Gradient.readings_share_window
#print axioms Geom.Gradient.ascending_is_provision
#print axioms Geom.Gradient.orientation_free

-- Geom.Totality (13)
#print axioms Geom.Totality.get?_mem
#print axioms Geom.Totality.pair_ext
#print axioms Geom.Totality.rel_merge_registers
#print axioms Geom.Totality.get?_graph_zero
#print axioms Geom.Totality.get?_graph_one
#print axioms Geom.Totality.mem_map_of_mem
#print axioms Geom.Totality.mem_graphTotality
#print axioms Geom.Totality.relStep_graph
#print axioms Geom.Totality.stepInj_graph
#print axioms Geom.Totality.relMerges_graph
#print axioms Geom.Totality.graph_rel_merge_registers
#print axioms Geom.Totality.injOn_of_inj
#print axioms Geom.Totality.becoming_from_marginals

-- Geom.Freshness (19)
#print axioms Geom.Freshness.slice_oneTick
#print axioms Geom.Freshness.productFresh_oneTick
#print axioms Geom.Freshness.muteU_slice
#print axioms Geom.Freshness.muteU_stream_mute
#print axioms Geom.Freshness.mem_tt
#print axioms Geom.Freshness.mem_ff
#print axioms Geom.Freshness.not_mem_tf
#print axioms Geom.Freshness.correlated_not_product
#print axioms Geom.Freshness.stream_mute_not_imply_product
#print axioms Geom.Freshness.revealU_slice
#print axioms Geom.Freshness.mem_full
#print axioms Geom.Freshness.full_is_product
#print axioms Geom.Freshness.false_mem_es
#print axioms Geom.Freshness.true_mem_es
#print axioms Geom.Freshness.false_mem_caps
#print axioms Geom.Freshness.revealU_not_stream_mute
#print axioms Geom.Freshness.product_not_imply_stream_mute
#print axioms Geom.Freshness.expand_bridge_stream_mute
#print axioms Geom.Freshness.freshness_hygiene

-- Geom.Arc (8)
#print axioms Geom.Arc.registration_is_ledger_pair
#print axioms Geom.Arc.provision_meets_exhaustion
#print axioms Geom.Arc.profile_bounce_is_bounce
#print axioms Geom.Arc.orientation_free_weld
#print axioms Geom.Arc.totality_is_registration
#print axioms Geom.Arc.scaffolding_change
#print axioms Geom.Arc.freshness_predicates_independent
#print axioms Geom.Arc.stage1_geometry

-- Obs.AbstractMemory (1)
#print axioms Obs.AbstractMemory.book_ne_of_ne

-- Obs.MergeMonotone (10)
#print axioms Obs.MergeMonotone.noninjective_of_booking_selfblind
#print axioms Obs.MergeMonotone.noninjective_of_causal_record
#print axioms Obs.MergeMonotone.read_step_congruence
#print axioms Obs.MergeMonotone.reference_support_nonempty
#print axioms Obs.MergeMonotone.no_demon_of_selfblind
#print axioms Obs.MergeMonotone.no_demon_of_causal_record
#print axioms Obs.MergeMonotone.length_eraseDups_le
#print axioms Obs.MergeMonotone.listImage_length_le
#print axioms Obs.MergeMonotone.image_size_monotone_step
#print axioms Obs.MergeMonotone.causal_record_image_monotone

-- Obs.EffectiveDynamics (15)
#print axioms Obs.EffectiveDynamics.readClosed_of_readClosure
#print axioms Obs.EffectiveDynamics.step_factors_read_of_factors
#print axioms Obs.EffectiveDynamics.readClosed_of_factors
#print axioms Obs.EffectiveDynamics.protocol_noninjective
#print axioms Obs.EffectiveDynamics.noninjective_of_booking_factors
#print axioms Obs.EffectiveDynamics.observable_merge_of_write_unread_readClosed
#print axioms Obs.EffectiveDynamics.booked_states_ne
#print axioms Obs.EffectiveDynamics.readClosed_of_induced
#print axioms Obs.EffectiveDynamics.readClosed_iff_induced
#print axioms Obs.EffectiveDynamics.read_iterate_eq
#print axioms Obs.EffectiveDynamics.historical_image_monotone_of_induced
#print axioms Obs.EffectiveDynamics.historical_reads_stable
#print axioms Obs.EffectiveDynamics.historical_read_of_book
#print axioms Obs.EffectiveDynamics.stochasticReadClosed_of_readClosed
#print axioms Obs.EffectiveDynamics.stochasticReadClosed_of_inducedSupports

-- Obs.Unlock (6)
#print axioms Obs.Unlock.unlocks_at_imprint_of_refinement
#print axioms Obs.Unlock.not_write_unread_unlocked
#print axioms Obs.Unlock.not_both_closed
#print axioms Obs.Unlock.historical_stability_requires_closure
#print axioms Obs.Unlock.locked_still_merged_of_displaced
#print axioms Obs.Unlock.unlocked_separates_post_of_displaced

-- Obs.UnlockCompleteness (13)
#print axioms Obs.Unlock.cut_replacement_is_displaced_at_zero
#print axioms Obs.Unlock.merged_forever_of_readClosed
#print axioms Obs.Unlock.crossing_of_merge_break
#print axioms Obs.Unlock.unlock_trichotomy
#print axioms Obs.Unlock.labels_exclusive_time
#print axioms Obs.Unlock.labels_exclusive_broken_displaced
#print axioms Obs.Unlock.jointCut_refines_locked
#print axioms Obs.Unlock.jointCut_separates
#print axioms Obs.Unlock.coarsens_refl
#print axioms Obs.Unlock.coarsens_trans
#print axioms Obs.Unlock.locked_coarsens_jointCut
#print axioms Obs.Unlock.probe_coarsens_jointCut
#print axioms Obs.Unlock.unlock_refinement_normal_form

-- Obs.UnlockPricing (6)
#print axioms Obs.Unlock.no_postprocessing_of_separating
#print axioms Obs.Unlock.separating_probe_not_coarsening
#print axioms Obs.Unlock.refinement_pays_access
#print axioms Obs.Unlock.displacement_pays_access
#print axioms Obs.Unlock.broken_closure_pays_autonomy
#print axioms Obs.Unlock.access_or_autonomy

-- Obs.Recovery (21)
#print axioms Obs.Recovery.elapsed_forward
#print axioms Obs.Recovery.elapsed_reverse_at_turn
#print axioms Obs.Recovery.onAscent_forward_iff
#print axioms Obs.Recovery.forward_ascent_is_provision
#print axioms Obs.Recovery.reverse_ascent_is_provision
#print axioms Obs.Recovery.address_ascent_is_provision
#print axioms Obs.Recovery.readings_share_profile
#print axioms Obs.Recovery.shared_exhaustion
#print axioms Obs.Recovery.local_rph_on_ascent
#print axioms Obs.Recovery.address_epistemic_past_is_ascent
#print axioms Obs.Recovery.swap_out_is_prior
#print axioms Obs.Recovery.swap_sys_is_in
#print axioms Obs.Recovery.swap_involution
#print axioms Obs.Recovery.osc_out_silent
#print axioms Obs.Recovery.swap_archive_recovers_prior
#print axioms Obs.Recovery.swap_archive_path_recovers
#print axioms Obs.Recovery.swap_archive_length
#print axioms Obs.Recovery.swap_archive_head
#print axioms Obs.Recovery.osc_archive_silent
#print axioms Obs.Recovery.recovery_on_bounce
#print axioms Obs.Recovery.recovery_arc_weld

-- Obs.CausalOrder (24)
#print axioms Obs.CausalOrder.rev_is_opposite_fwd
#print axioms Obs.CausalOrder.address_reversal_opposes
#print axioms Obs.CausalOrder.fwd_irrefl
#print axioms Obs.CausalOrder.rev_irrefl
#print axioms Obs.CausalOrder.fwd_trans
#print axioms Obs.CausalOrder.rev_trans
#print axioms Obs.CausalOrder.fwd_rev_exclusive
#print axioms Obs.CausalOrder.ascent_depth
#print axioms Obs.CausalOrder.interval_matches_depth
#print axioms Obs.CausalOrder.capacity_on_ascent
#print axioms Obs.CausalOrder.pow_mul_gap
#print axioms Obs.CausalOrder.capacity_along_interval
#print axioms Obs.CausalOrder.swap_archive_is_path
#print axioms Obs.CausalOrder.lt_iff_le_pred
#print axioms Obs.CausalOrder.archive_preceeds_iff_fwd
#print axioms Obs.CausalOrder.fwd_adjacent
#print axioms Obs.CausalOrder.rev_adjacent
#print axioms Obs.CausalOrder.monotone_of_adjacent
#print axioms Obs.CausalOrder.antitone_of_adjacent
#print axioms Obs.CausalOrder.direction_dichotomy
#print axioms Obs.CausalOrder.unique_up_to_reversal
#print axioms Obs.CausalOrder.unique_up_to_reversal_fwd
#print axioms Obs.CausalOrder.unique_up_to_reversal_rev
#print axioms Obs.CausalOrder.causal_order_reconstruction

-- Obs.Dimension (15)
#print axioms Obs.Dimension.interval_linear
#print axioms Obs.Dimension.depth_gap_eq_separation
#print axioms Obs.Dimension.ascent_total
#print axioms Obs.Dimension.ascent_comparable
#print axioms Obs.Dimension.fwd_strict_linear
#print axioms Obs.Dimension.ascent_order_dim_le_one
#print axioms Obs.Dimension.ascent_order_dim_not_zero
#print axioms Obs.Dimension.ascent_order_dim_eq_one
#print axioms Obs.Dimension.order_dimension_one
#print axioms Obs.Dimension.capacity_step_growth
#print axioms Obs.Dimension.capacity_is_pow
#print axioms Obs.Dimension.step_growth_eq_pow
#print axioms Obs.Dimension.capacity_unique_step_growth
#print axioms Obs.Dimension.capacity_growth_over_interval
#print axioms Obs.Dimension.dimension_from_growth

-- Obs.Selection (69)
#print axioms Obs.Selection.le_dest
#print axioms Obs.Selection.add_sub_cancel_left
#print axioms Obs.Selection.add_sub_cancel_right
#print axioms Obs.Selection.add_sub_of_le
#print axioms Obs.Selection.mod_eq_of_lt
#print axioms Obs.Selection.add_self_two
#print axioms Obs.Selection.gap_split
#print axioms Obs.Selection.gap_split_pred
#print axioms Obs.Selection.length_append
#print axioms Obs.Selection.length_replicate
#print axioms Obs.Selection.append_nil
#print axioms Obs.Selection.mem_append_left
#print axioms Obs.Selection.mem_append_right
#print axioms Obs.Selection.mem_or_of_mem_append
#print axioms Obs.Selection.mem_map_of_mem
#print axioms Obs.Selection.distinct_append
#print axioms Obs.Selection.distinct_map
#print axioms Obs.Selection.replicate_blank_cons
#print axioms Obs.Selection.replicate_append_blank
#print axioms Obs.Selection.replicate_cancel
#print axioms Obs.Selection.take_replicate_le
#print axioms Obs.Selection.take_replicate_append
#print axioms Obs.Selection.allBits_eq_cons
#print axioms Obs.Selection.allBits_length
#print axioms Obs.Selection.freeTails_length_succ
#print axioms Obs.Selection.freeTails_length
#print axioms Obs.Selection.allBits_distinct
#print axioms Obs.Selection.freeTails_distinct
#print axioms Obs.Selection.blank_not_mem_freeTails
#print axioms Obs.Selection.mem_allBits
#print axioms Obs.Selection.mem_freeTails_iff
#print axioms Obs.Selection.getCell_nil
#print axioms Obs.Selection.setCell_nil
#print axioms Obs.Selection.getCell_replicate_false
#print axioms Obs.Selection.setCell_replicate_false
#print axioms Obs.Selection.forwardFrom_zero
#print axioms Obs.Selection.forwardFrom_succ
#print axioms Obs.Selection.propagated_aux
#print axioms Obs.Selection.propagated_state
#print axioms Obs.Selection.synState_inj
#print axioms Obs.Selection.synState_inj_tail
#print axioms Obs.Selection.mem_branch_iff
#print axioms Obs.Selection.branch_distinct
#print axioms Obs.Selection.propList_eq
#print axioms Obs.Selection.imprint_eq_synState
#print axioms Obs.Selection.mem_propList_iff
#print axioms Obs.Selection.stock_synState
#print axioms Obs.Selection.stock_imprint
#print axioms Obs.Selection.propList_length
#print axioms Obs.Selection.synList_length
#print axioms Obs.Selection.confList_length_add
#print axioms Obs.Selection.confList_length
#print axioms Obs.Selection.propList_distinct
#print axioms Obs.Selection.synList_distinct
#print axioms Obs.Selection.confList_distinct
#print axioms Obs.Selection.mem_synList_iff
#print axioms Obs.Selection.prop_sublist_syn
#print axioms Obs.Selection.mem_confList_iff
#print axioms Obs.Selection.syn_eq_prop_at_max
#print axioms Obs.Selection.conf_empty_at_max
#print axioms Obs.Selection.confList_length_at_max
#print axioms Obs.Selection.propCard_eq_length
#print axioms Obs.Selection.synCard_eq_length
#print axioms Obs.Selection.confCard_eq_length
#print axioms Obs.Selection.prop_times_free_eq_syn
#print axioms Obs.Selection.synCard_eq_propCard_at_max
#print axioms Obs.Selection.confCard_zero_at_max
#print axioms Obs.Selection.selection_ratio_nat
#print axioms Obs.Selection.selection_closed_forms

-- Obs.StochasticUnlock (54)
#print axioms Obs.StochasticUnlock.mem_head
#print axioms Obs.StochasticUnlock.mem_tail
#print axioms Obs.StochasticUnlock.lsum_congr
#print axioms Obs.StochasticUnlock.exists_mem_not_of_not_ball
#print axioms Obs.StochasticUnlock.garble_congr
#print axioms Obs.StochasticUnlock.access_price
#print axioms Obs.StochasticUnlock.autonomy_price
#print axioms Obs.StochasticUnlock.marginal_autonomy_price
#print axioms Obs.StochasticUnlock.merged_forever
#print axioms Obs.StochasticUnlock.crossing
#print axioms Obs.StochasticUnlock.unlock_trichotomy
#print axioms Obs.StochasticUnlock.labels_exclusive
#print axioms Obs.StochasticUnlock.access_or_autonomy
#print axioms Obs.StochasticUnlock.garbling_refines_merging
#print axioms Obs.StochasticUnlock.ensemble_access_price
#print axioms Obs.StochasticUnlock.pair_ext
#print axioms Obs.StochasticUnlock.env_records_distinct
#print axioms Obs.StochasticUnlock.countClasses_le_of_imp
#print axioms Obs.StochasticUnlock.countClasses_lt_head_witness
#print axioms Obs.StochasticUnlock.countClasses_lt_of_strict_merge
#print axioms Obs.StochasticUnlock.antitone_of_step
#print axioms Obs.StochasticUnlock.law_agree_step
#print axioms Obs.StochasticUnlock.second_law_arrow
#print axioms Obs.StochasticUnlock.second_law_strict
#print axioms Obs.StochasticUnlock.length_remove_of_mem
#print axioms Obs.StochasticUnlock.mem_remove
#print axioms Obs.StochasticUnlock.length_le_of_distinct_mem
#print axioms Obs.StochasticUnlock.exists_of_mem_map
#print axioms Obs.StochasticUnlock.length_map_eq
#print axioms Obs.StochasticUnlock.env_records_distinct_list
#print axioms Obs.StochasticUnlock.env_alphabet_ge_indegree
#print axioms Obs.StochasticUnlock.one_mul'
#print axioms Obs.StochasticUnlock.add_add_add_comm'
#print axioms Obs.StochasticUnlock.mul_mul_mul_comm'
#print axioms Obs.StochasticUnlock.lsum_add_eor
#print axioms Obs.StochasticUnlock.lsum_zero_eor
#print axioms Obs.StochasticUnlock.mul_lsum
#print axioms Obs.StochasticUnlock.lsum_mul
#print axioms Obs.StochasticUnlock.lsum_swap_eor
#print axioms Obs.StochasticUnlock.lsum_le_lsum_eor
#print axioms Obs.StochasticUnlock.lsum_nonneg_eor
#print axioms Obs.StochasticUnlock.lsum_mul_lsum
#print axioms Obs.StochasticUnlock.mulnn
#print axioms Obs.StochasticUnlock.rowOverlap_nonneg
#print axioms Obs.StochasticUnlock.rowOverlap_row
#print axioms Obs.StochasticUnlock.rowOverlap_col
#print axioms Obs.StochasticUnlock.purity_garble_le
#print axioms Obs.StochasticUnlock.antitone_of_step_le
#print axioms Obs.StochasticUnlock.second_law_purity
#print axioms Obs.StochasticUnlock.second_law_tsallis
#print axioms Obs.StochasticUnlock.nat_add_mul
#print axioms Obs.StochasticUnlock.nat_mul_assoc
#print axioms Obs.StochasticUnlock.nat_amgm2_of_le
#print axioms Obs.StochasticUnlock.natEOR

-- Obs.TotalVariationDPI (14)
#print axioms Obs.StochasticUnlock.lsum_zero
#print axioms Obs.StochasticUnlock.add_add_add_comm
#print axioms Obs.StochasticUnlock.lsum_add
#print axioms Obs.StochasticUnlock.lsum_sub
#print axioms Obs.StochasticUnlock.lsum_swap
#print axioms Obs.StochasticUnlock.lsum_mul_left
#print axioms Obs.StochasticUnlock.lsum_le_lsum
#print axioms Obs.StochasticUnlock.abs_lsum_le
#print axioms Obs.StochasticUnlock.dtv_zero_of_eqOn
#print axioms Obs.StochasticUnlock.tv_data_processing
#print axioms Obs.StochasticUnlock.le_antitone_of_step
#print axioms Obs.StochasticUnlock.tv_arrow
#print axioms Obs.StochasticUnlock.lyapunov_arrow
#print axioms Obs.StochasticUnlock.merged_at_distance_zero

-- Obs.StochasticDivergence (8)
#print axioms Obs.StochasticUnlock.lsum_nonneg
#print axioms Obs.StochasticUnlock.law_nonneg_forever
#print axioms Obs.StochasticUnlock.F_lsum_le
#print axioms Obs.StochasticUnlock.f_data_processing
#print axioms Obs.StochasticUnlock.f_arrow
#print axioms Obs.StochasticUnlock.f_lyapunov
#print axioms Obs.StochasticUnlock.f_nonneg
#print axioms Obs.StochasticUnlock.fdiv_abs_eq_dtv

-- Obs.Budget (10)
#print axioms Obs.Budget.budget_tick
#print axioms Obs.Budget.prodBelow_mono
#print axioms Obs.Budget.prodBelow_congr
#print axioms Obs.Budget.budget_run
#print axioms Obs.Budget.mem_map_of_mem
#print axioms Obs.Budget.mem_of_distinct_incl_length_le
#print axioms Obs.Budget.budget_tick_eq_iff
#print axioms Obs.Budget.budget_run_eq_of_saturated
#print axioms Obs.Budget.dirac_autonomous
#print axioms Obs.Budget.iter_classes_antitone

-- Obs.ContinuumUnlock (5)
#print axioms Obs.ContinuumUnlock.continuum_refinement_unlocks
#print axioms Obs.ContinuumUnlock.continuum_not_write_unread_unlocked
#print axioms Obs.ContinuumUnlock.continuum_displaced_locked_merged
#print axioms Obs.ContinuumUnlock.continuum_historical_stability_requires_closure
#print axioms Obs.ContinuumUnlock.continuum_not_both_closed

-- Obs.EmbeddedObserver (9)
#print axioms Obs.EmbeddedObserver.kernelEq_refl
#print axioms Obs.EmbeddedObserver.kernelEq_symm
#print axioms Obs.EmbeddedObserver.kernelEq_trans
#print axioms Obs.EmbeddedObserver.stable_preserves_kernel
#print axioms Obs.EmbeddedObserver.own_readout_invisible
#print axioms Obs.EmbeddedObserver.product_verdict_stable
#print axioms Obs.EmbeddedObserver.product_hidden_readClosed
#print axioms Obs.EmbeddedObserver.product_hidden_step_not_factors
#print axioms Obs.EmbeddedObserver.exists_stable_internal_observer_not_factors
