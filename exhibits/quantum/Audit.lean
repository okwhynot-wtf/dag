import SpineFacts
import Ortho
import Orthoset
import Classical
import Target
import Axiom
import Witness

/-!
# Audit — axiom footprint for `formal/quantum/`

Generated. Do not edit by hand:

```bash
python3 formal/tools/gen_audit.py
```

7 modules, 65 results. Source for `formal/AXIOMS.md`.
-/

-- SpineFacts (12)
#print axioms Quantum.SpineFacts.rep_zero_is_first_projection
#print axioms Quantum.SpineFacts.rep_not_symmetric
#print axioms Quantum.SpineFacts.rep_not_symmetric_at
#print axioms Quantum.SpineFacts.no_sqrt_on_fundamental
#print axioms Quantum.SpineFacts.sqrt_fourth_power_is_id
#print axioms Quantum.SpineFacts.no_sqrt_of_generated
#print axioms Quantum.SpineFacts.sqrt_model_exists
#print axioms Quantum.SpineFacts.sqrt_is_live
#print axioms Quantum.SpineFacts.omega_stage_injective
#print axioms Quantum.SpineFacts.level_card_succ
#print axioms Quantum.SpineFacts.reading_is_total_two_valued
#print axioms Quantum.SpineFacts.starting_position

-- Ortho (9)
#print axioms Quantum.Ortho.bit_distributive
#print axioms Quantum.Ortho.bit_orthomodular
#print axioms Quantum.Ortho.bit_atom_left
#print axioms Quantum.Ortho.bit_atom_right
#print axioms Quantum.Ortho.bit_atoms_are_two
#print axioms Quantum.Ortho.bit_atomistic
#print axioms Quantum.Ortho.bit_covering_law
#print axioms Quantum.Ortho.bit_no_superposition
#print axioms Quantum.Ortho.superposition_is_independent

-- Orthoset (15)
#print axioms Quantum.Orthoset.orthogonal_partner_unique
#print axioms Quantum.Orthoset.act_orthoset_has_no_triple
#print axioms Quantum.Orthoset.no_triple_without_generation
#print axioms Quantum.Orthoset.subset_polar_polar
#print axioms Quantum.Orthoset.polar_antitone
#print axioms Quantum.Orthoset.polar_polar_polar
#print axioms Quantum.Orthoset.polar_closed
#print axioms Quantum.Orthoset.sameSize_refl
#print axioms Quantum.Orthoset.normed_gives_orthogonal
#print axioms Quantum.Orthoset.act_has_no_normed_sequence
#print axioms Quantum.Orthoset.triangle_has_rank3
#print axioms Quantum.Orthoset.discrete_closure_trivial
#print axioms Quantum.Orthoset.discrete_rank_of_injective
#print axioms Quantum.Orthoset.rank3_not_from_one_act
#print axioms Quantum.Orthoset.rank_obstruction

-- Classical (8)
#print axioms Quantum.Classical.fundamental_has_two_states
#print axioms Quantum.Classical.no_third_state
#print axioms Quantum.Classical.pred_takes_bit_values
#print axioms Quantum.Classical.bitOfPred_faithful
#print axioms Quantum.Classical.bitOfPred_surjective
#print axioms Quantum.Classical.levelCard_closed_form
#print axioms Quantum.Classical.omega_is_base_or_stage
#print axioms Quantum.Classical.spine_is_classical

-- Target (1)
#print axioms Quantum.Target.piron_soler

-- Axiom (10)
#print axioms Quantum.Axiom.rank_of_normed
#print axioms Quantum.Axiom.hilbert_of_orthoframe
#print axioms Quantum.Axiom.spine_is_not_orthoframe
#print axioms Quantum.Axiom.discrete_no_superposition
#print axioms Quantum.Axiom.discrete_is_not_orthoframe
#print axioms Quantum.Axiom.rank_of_ladder
#print axioms Quantum.Axiom.irreducible_of_superposed
#print axioms Quantum.Axiom.hilbert_of_superposed
#print axioms Quantum.Axiom.bit_is_not_superposed
#print axioms Quantum.Axiom.superposition_carries_the_content

-- Witness (10)
#print axioms Quantum.Witness.swap_left
#print axioms Quantum.Witness.swap_swap
#print axioms Quantum.Witness.swap_injective
#print axioms Quantum.Witness.swap_fixes
#print axioms Quantum.Witness.discrete_irredundant
#print axioms Quantum.Witness.discrete_orthomodular
#print axioms Quantum.Witness.discrete_normed
#print axioms Quantum.Witness.discrete_rank
#print axioms Quantum.Witness.discrete_not_orthoframe_by_superposition
#print axioms Quantum.Witness.superposition_independent_of_the_rest
