import Orbit
import TwoCycle
import Facticity
import Ambient
import Diagonal
import Tower
import Ladder
import Cause
import Branch
import Limit
import Revision
import SEM
import Interior
import Monism
import Apophasis
import Canon
import Information
import Observer
import NoExterior
import Faces
import Density
import NonCommencement
import OmegaDuration
import SelfReference
import SelfArticulation

/-!
# Audit — axiom footprint for `formal/spine/`

Generated. Do not edit by hand:

```bash
python3 formal/tools/gen_audit.py
```

25 modules, 353 results. Source for `formal/AXIOMS.md`.
-/

-- Orbit (23)
#print axioms Orbit.symmetricStep_iff_involutive
#print axioms Orbit.arrow_of_not_involutive
#print axioms Orbit.trichotomy
#print axioms Orbit.rest_is_stagnation
#print axioms Orbit.two_cycle_at
#print axioms Orbit.classification_at
#print axioms Orbit.classification_exclusive
#print axioms Orbit.erased_pair_forever
#print axioms Orbit.erasing_forever
#print axioms Orbit.nat_embedding_of_no_collision
#print axioms Orbit.iter_lt_of_no_collision
#print axioms Orbit.iter_succ_of_no_collision
#print axioms Orbit.no_collision_forces_arrow
#print axioms Orbit.iter_lossless
#print axioms Orbit.iter_add
#print axioms Orbit.reaches_iff_le_of_no_collision
#print axioms Orbit.collision_returns
#print axioms Orbit.two_cycle
#print axioms Orbit.symmetric_live_collides
#print axioms Orbit.symmetric_lossless
#print axioms Orbit.void_is_excluded_fixed_point
#print axioms Orbit.fixed_point_refutes_liveness
#print axioms Orbit.classification

-- TwoCycle (13)
#print axioms TwoCycle.reading_equivariant
#print axioms TwoCycle.act_reads_as_not
#print axioms TwoCycle.reading_injective
#print axioms TwoCycle.reading_surjective
#print axioms TwoCycle.reading_unique
#print axioms TwoCycle.two_readings
#print axioms TwoCycle.pole_swap_automorphism
#print axioms TwoCycle.poles_indiscernible
#print axioms TwoCycle.bool_live_is_not
#print axioms TwoCycle.bool_fundamental
#print axioms TwoCycle.coproduct_fundamental
#print axioms TwoCycle.witnessed_fundamental
#print axioms TwoCycle.fundamental_package

-- Facticity (10)
#print axioms Facticity.orbit_of_symmetric
#print axioms Facticity.nondegenerate_two_cycle
#print axioms Facticity.nondegenerate_live_on_orbit
#print axioms Facticity.degenerate_not_live_on_orbit
#print axioms Facticity.liveOnOrbit_iff_nondegenerate
#print axioms Facticity.live_implies_liveOnOrbit
#print axioms Facticity.nondegenerate_generated_live
#print axioms Facticity.NondegeneratePointedAct.liveOnOrbit
#print axioms Facticity.exists_nondegenerate_pointed_act_model
#print axioms Facticity.facticity_package

-- Ambient (20)
#print axioms Ambient.powerId_two_iff_symmetric
#print axioms Ambient.powerId_one_is_rest
#print axioms Ambient.constantEquation_erasing
#print axioms Ambient.constantEquation_bool_erasing
#print axioms Ambient.idempotentErase_ambient
#print axioms Ambient.idempotentErase_erasing
#print axioms Ambient.idempotentErase_not_lossless
#print axioms Ambient.eqAmbient_pos_need_not_lossless
#print axioms Ambient.cycle3_powerId
#print axioms Ambient.cycle3_asymmetric
#print axioms Ambient.powerId_ge_three_need_not_symmetric
#print axioms Ambient.cycle3_lossless
#print axioms Ambient.cycleM_powerId
#print axioms Ambient.exists_asymmetric_m_cycle
#print axioms Ambient.powerId_two_excludes_erase
#print axioms Ambient.powerId_two_excludes_arrow
#print axioms Ambient.powerId_one_is_degenerate
#print axioms Ambient.ambient_uniqueness_equational
#print axioms Ambient.injectivity_of_powerId_two
#print axioms Ambient.ambient_adequacy_package

-- Diagonal (12)
#print axioms Diagonal.lawvere
#print axioms Diagonal.no_point_surjection
#print axioms Diagonal.seal_on_fundamental
#print axioms Diagonal.dodgeWith_unrepresented
#print axioms Diagonal.cantor_fundamental
#print axioms Diagonal.not_restless
#print axioms Diagonal.seal_bool
#print axioms Diagonal.dodge_unrepresented
#print axioms Diagonal.cantor
#print axioms Diagonal.resting_law_permits_fixed_point
#print axioms Diagonal.resting_law_dodge_realised
#print axioms Diagonal.diagonal_package

-- Tower (25)
#print axioms Tower.of_dodge
#print axioms Tower.namer_is_new
#print axioms Tower.strict_growth
#print axioms Tower.no_self_extension
#print axioms Tower.arrow_placement
#print axioms Tower.no_settling
#print axioms Tower.not_inj
#print axioms Tower.underdetermined_core
#print axioms Tower.underdetermined_at_fundamental
#print axioms Tower.ext2_at_p
#print axioms Tower.ext2_at_q
#print axioms Tower.ext2_off
#print axioms Tower.underdetermined_at_two
#print axioms Tower.ext2v_at_p
#print axioms Tower.ext2v_at_q
#print axioms Tower.ext2v_off
#print axioms Tower.underdetermined_at_two_valued
#print axioms Tower.underdetermination_needs_two_points
#print axioms Tower.dodge_f₀_is_not
#print axioms Tower.first_emanation_of
#print axioms Tower.first_emanation
#print axioms Tower.first_emanation_grows
#print axioms Tower.first_emanations_differ
#print axioms Tower.first_step_underdetermined
#print axioms Tower.tower_package

-- Ladder (10)
#print axioms Ladder.ladder_step
#print axioms Ladder.ladder_grows
#print axioms Ladder.none_is_new
#print axioms Ladder.ladder_never_settles
#print axioms Ladder.lift_injective
#print axioms Ladder.lift_conservative
#print axioms Ladder.ladder_ascends
#print axioms Ladder.pts_ne
#print axioms Ladder.underdetermined_at_level
#print axioms Ladder.ladder_package

-- Cause (28)
#print axioms Cause.same_cause_same_effect
#print axioms Cause.difference_transmitted
#print axioms Cause.transmission_exact
#print axioms Cause.fundamental_faithful
#print axioms Cause.erasure_breaks_transmission
#print axioms Cause.causal_asymmetry
#print axioms Cause.stepEsc_naming
#print axioms Cause.step_naming
#print axioms Cause.ladder_is_iterated_step
#print axioms Cause.intervention_changes_effect
#print axioms Cause.intervention_changes_dodge
#print axioms Cause.intervention_preserves_past
#print axioms Cause.dodgePolicy_wf
#print axioms Cause.repP_step
#print axioms Cause.ladder_is_default
#print axioms Cause.policies_really_differ
#print axioms Cause.named_policy_independent
#print axioms Cause.freedom_becomes_cause
#print axioms Cause.escapeAt_ne
#print axioms Cause.escapeAt_lt
#print axioms Cause.escapeAt_eq
#print axioms Cause.escapeAt_rep_le
#print axioms Cause.escapeAt_wf
#print axioms Cause.escapes_differ_at
#print axioms Cause.escape_policy_changes_history
#print axioms Cause.escapes_really_differ
#print axioms Cause.escape_policies_from_underdetermination
#print axioms Cause.cause_package

-- Branch (15)
#print axioms Branch.escapeSet_two
#print axioms Branch.branch_nonempty
#print axioms Branch.Path.step
#print axioms Branch.committed_is_path
#print axioms Branch.committed_rep
#print axioms Branch.seal_along_every_path
#print axioms Branch.nec_seal
#print axioms Branch.escape_choice_possible
#print axioms Branch.escape_not_necessary
#print axioms Branch.poss_without_nec
#print axioms Branch.ascent_necessary_direction_free
#print axioms Branch.paths_diverge
#print axioms Branch.paths_diverge_no_past_agree
#print axioms Branch.paths_from_underdetermination
#print axioms Branch.branch_package

-- Limit (21)
#print axioms Limit.base_inj
#print axioms Limit.stage_inj
#print axioms Limit.embed_appears
#print axioms Limit.embed_ne_stage
#print axioms Limit.embed_injective
#print axioms Limit.realize_succ_of_embed
#print axioms Limit.realize_embed
#print axioms Limit.realize_succ_of_appears
#print axioms Limit.rep_realize_stable
#print axioms Limit.limit_conservative
#print axioms Limit.nat_max_le
#print axioms Limit.nat_le_max_left
#print axioms Limit.nat_le_max_right
#print axioms Limit.limit_reading_conservative
#print axioms Limit.limit_sealed
#print axioms Limit.omega_plus_one_step
#print axioms Limit.omega_plus_one_grows
#print axioms Limit.repTail_step
#print axioms Limit.no_ordinal_settling
#print axioms Limit.tail_sealed
#print axioms Limit.limit_package

-- Revision (8)
#print axioms Revision.orbitOf_revision
#print axioms Revision.liar_revision_is_orbit
#print axioms Revision.revision_iff_orbit
#print axioms Revision.revision_period_two
#print axioms Revision.two_cycle_is_revision
#print axioms Revision.tick_is_revision_step
#print axioms Revision.settled_values_persist
#print axioms Revision.revision_package

-- SEM (5)
#print axioms SEM.acyclic
#print axioms SEM.intervention_commutes
#print axioms SEM.do_changes_on_diagonal
#print axioms SEM.asymmetry_is_acyclicity
#print axioms SEM.sem_package

-- Interior (9)
#print axioms Interior.self_opacity
#print axioms Interior.residue_definite
#print axioms Interior.outdated_portrait
#print axioms Interior.xor_eq_true_iff
#print axioms Interior.descent
#print axioms Interior.self_modeling_forces_restless
#print axioms Interior.constant_ascription_not_self_modeling
#print axioms Interior.restless_refuses_stable_flag
#print axioms Interior.interior_package

-- Monism (3)
#print axioms Monism.diagonal_monism
#print axioms Monism.reading_inherits_the_chain
#print axioms Monism.retorsion

-- Apophasis (11)
#print axioms Apophasis.draws_forces_live
#print axioms Apophasis.no_static_fundamental
#print axioms Apophasis.no_constant_fills
#print axioms Apophasis.live_iff_no_rest
#print axioms Apophasis.symmetric_refuses_arrow
#print axioms Apophasis.generated_refuses_remainder
#print axioms Apophasis.ApophaticReading.live
#print axioms Apophasis.apophatic_inherits_the_chain
#print axioms Apophasis.apophatic_chain
#print axioms Apophasis.essence_exceeds_inventory
#print axioms Apophasis.apophasis_package

-- Canon (24)
#print axioms Canon.canon_initial
#print axioms Canon.generated_of_initial_surj
#print axioms Canon.draws_of_initial_inj
#print axioms Canon.IsFundamental.exhaustive
#print axioms Canon.IsFundamental.sustains
#print axioms Canon.IsFundamental.live
#print axioms Canon.IsFundamental.lossless
#print axioms Canon.IsFundamental.involutive
#print axioms Canon.IsFundamental.iso_everywhere
#print axioms Canon.isFundamental_iff_clauses
#print axioms Canon.elimination
#print axioms Canon.canon_is_fundamental
#print axioms Canon.fundamental_correspondence
#print axioms Canon.every_fundamental_reads_as_canon
#print axioms Canon.fundamental_map_unique
#print axioms Canon.theFundamental_is_fundamental
#print axioms Canon.ofReading
#print axioms Canon.diagonal_monism_of_fundamental
#print axioms Canon.coord_reading
#print axioms Canon.coord_of_reading
#print axioms Canon.underdetermined_of_fundamental
#print axioms Canon.master_of_fundamental
#print axioms Canon.modal_of_fundamental
#print axioms Canon.fundamental_characterized

-- Information (7)
#print axioms Information.fundamental_is_one_bit
#print axioms Information.conservation
#print axioms Information.fundamental_conserves
#print axioms Information.erasure_destroys
#print axioms Information.capacity_deficit
#print axioms Information.information_grows
#print axioms Information.information_package

-- Observer (8)
#print axioms Observer.namer_represents_the_past
#print axioms Observer.observer_sealed
#print axioms Observer.observer_interior
#print axioms Observer.observer_outrun
#print axioms Observer.observer_signature
#print axioms Observer.rich_inherits
#print axioms Observer.rich_inherits_at_level
#print axioms Observer.observers_forced

-- NoExterior (8)
#print axioms NoExterior.presentation_forces_live
#print axioms NoExterior.presentation_retracts
#print axioms NoExterior.standpoint_embeds_canon
#print axioms NoExterior.presentation_unique
#print axioms NoExterior.coequivariant_of_witness
#print axioms NoExterior.presentation_of_witness
#print axioms NoExterior.witness_is_observer
#print axioms NoExterior.no_exterior_standpoint

-- Faces (6)
#print axioms Faces.neti_neti
#print axioms Faces.dao_untold
#print axioms Faces.self_liberation
#print axioms Faces.three_faces_one_diagonal
#print axioms Faces.creatio_ex_nihilo
#print axioms Faces.four_faces_one_diagonal

-- Density (31)
#print axioms Density.boolEndo_complete
#print axioms Density.bool_isFundamental_of_eq_not
#print axioms Density.bool_fundamental_iff_not
#print axioms Density.boolEndo_fundamental_iff
#print axioms Density.boolEndo_excluded_rests
#print axioms Density.boolEndo_apply_ext
#print axioms Density.fundamental_density
#print axioms Density.fundamental_two_elements
#print axioms Density.fin_val_ne
#print axioms Density.no_fundamental_fin_ge_three
#print axioms Density.fin_one_eq
#print axioms Density.fundamentals_only_at_two
#print axioms Density.live_count_formula
#print axioms Density.live_count_at_fundamental
#print axioms Density.liveCount_matches_bool_enum
#print axioms Density.live_count_package
#print axioms Density.live_density_at_fundamental
#print axioms Density.live_density_package
#print axioms Density.levelCard_eq
#print axioms Density.levelToNat_lt
#print axioms Density.levelToNat_natToLevel
#print axioms Density.levelToNat_inj
#print axioms Density.find_target_or_miss
#print axioms Density.no_distinct_large
#print axioms Density.no_retraction
#print axioms Density.predicateCount_eq
#print axioms Density.two_three_pow
#print axioms Density.artic_add_helper
#print axioms Density.articulation_mass
#print axioms Density.articulation_partial_sum
#print axioms Density.three_constants

-- NonCommencement (11)
#print axioms NonCommencement.mod2_even
#print axioms NonCommencement.mod2_odd
#print axioms NonCommencement.iter_even
#print axioms NonCommencement.iter_odd
#print axioms NonCommencement.iterate_parity
#print axioms NonCommencement.fundamental_forgets_count
#print axioms NonCommencement.no_live_act_on_inhabited_subsingleton
#print axioms NonCommencement.no_fundamental_below_two
#print axioms NonCommencement.fundamental_is_least
#print axioms NonCommencement.ladder_index_recoverable
#print axioms NonCommencement.non_commencement_package

-- OmegaDuration (13)
#print axioms OmegaDuration.optionNat_left_inv
#print axioms OmegaDuration.optionNat_right_inv
#print axioms OmegaDuration.optionNat_bijective
#print axioms OmegaDuration.optionOmega_left_inv
#print axioms OmegaDuration.optionOmega_right_inv
#print axioms OmegaDuration.optionLevelOmega_bijective
#print axioms OmegaDuration.stage_tag_injective
#print axioms OmegaDuration.appearsBy_stage
#print axioms OmegaDuration.appearsBy_recovers_stage
#print axioms OmegaDuration.namer_new_at_omega
#print axioms OmegaDuration.omega_not_a_rung
#print axioms OmegaDuration.omega_duration_package
#print axioms OmegaDuration.omega_duration_not_a_rung_package

-- SelfReference (31)
#print axioms SelfReference.seal_self
#print axioms SelfReference.incompleteness_unconditional
#print axioms SelfReference.ladder_rep_incomplete
#print axioms SelfReference.pow2_succ
#print axioms SelfReference.n_lt_pow2
#print axioms SelfReference.t_le_pow2
#print axioms SelfReference.two_mul_add3_le_pow
#print axioms SelfReference.quad_lt_pow
#print axioms SelfReference.names_eq
#print axioms SelfReference.predicates_eq
#print axioms SelfReference.deficit_strict
#print axioms SelfReference.unsayable_pos
#print axioms SelfReference.deficit_count
#print axioms SelfReference.mul_level_lt_pred
#print axioms SelfReference.deficit_vanishes
#print axioms SelfReference.completeness_in_limit_is_policy
#print axioms SelfReference.eventually_sayable
#print axioms SelfReference.sayability_asymmetry
#print axioms SelfReference.minimal_reaches_bound
#print axioms SelfReference.levelCard_add
#print axioms SelfReference.articulation_capacity
#print axioms SelfReference.nameSlot_fresh
#print axioms SelfReference.nameSlot_inj
#print axioms SelfReference.nameSlot_in_range
#print axioms SelfReference.eventual_sayability_has_names
#print axioms SelfReference.lag_at_bound
#print axioms SelfReference.lag_theorem
#print axioms SelfReference.lag_recedes
#print axioms SelfReference.dodge_gauge_covariant
#print axioms SelfReference.corpus_not_universal
#print axioms SelfReference.meta_triad_quantitative

-- SelfArticulation (1)
#print axioms SelfArticulation.self_articulation
