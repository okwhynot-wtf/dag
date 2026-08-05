import Overtones
import Frequencies
import WaveEquation
import CantorBoundary
import SpectrumSymmetry
import CouplingGauge

/-!
# Audit — axiom footprint for `formal/experimental/`

Generated. Do not edit by hand:

```bash
python3 formal/tools/gen_audit.py
```

6 modules, 101 results. Source for `formal/AXIOMS.md`.
-/

-- Overtones (13)
#print axioms Experimental.Overtones.refl3_involution
#print axioms Experimental.Overtones.refl3'_involution
#print axioms Experimental.Overtones.three_from_two_flips
#print axioms Experimental.Overtones.cyc3_period_three
#print axioms Experimental.Overtones.refl5_involution
#print axioms Experimental.Overtones.refl5'_involution
#print axioms Experimental.Overtones.five_from_two_flips
#print axioms Experimental.Overtones.cyc5_period_five
#print axioms Experimental.Overtones.cyc3_injective
#print axioms Experimental.Overtones.cyc5_injective
#print axioms Experimental.Overtones.rot_from_two_flips
#print axioms Experimental.Overtones.three_from_two_flips_general
#print axioms Experimental.Overtones.five_from_two_flips_general

-- Frequencies (4)
#print axioms Experimental.Frequencies.fifth_generates
#print axioms Experimental.Frequencies.order_eq_div_gcd_twelve
#print axioms Experimental.Frequencies.order_eq_div_gcd_twelve_general
#print axioms Experimental.Frequencies.circle_of_fifths_minimal

-- WaveEquation (21)
#print axioms Experimental.Wave.iterN_succ_out
#print axioms Experimental.Wave.fin_sub_one_add_one
#print axioms Experimental.Wave.fin_add_one_sub_one
#print axioms Experimental.Wave.ringX_rot_pointwise
#print axioms Experimental.Wave.ringX_rotInv_pointwise
#print axioms Experimental.Wave.step_rot_pointwise
#print axioms Experimental.Wave.step_rotInv_pointwise
#print axioms Experimental.Wave.step_ringX_congr
#print axioms Experimental.Wave.iterN_step_ringX_congr
#print axioms Experimental.Wave.iterN_step_rot_pointwise
#print axioms Experimental.Wave.iterN_step_rotInv_pointwise
#print axioms Experimental.Wave.return_rot_pointwise
#print axioms Experimental.Wave.return_rotInv_pointwise
#print axioms Experimental.Wave.return_of_rot_return
#print axioms Experimental.Wave.return_iff_rot_return
#print axioms Experimental.Wave.ring2_period_two
#print axioms Experimental.Wave.ring3_period_six
#print axioms Experimental.Wave.ring5_period_ten
#print axioms Experimental.Wave.ring6_period_six
#print axioms Experimental.Wave.dirichlet3_period_eight
#print axioms Experimental.Wave.dirichlet5_period_twelve

-- CantorBoundary (16)
#print axioms Experimental.CantorBoundary.boundary_unenumerable
#print axioms Experimental.CantorBoundary.encode_inj_pointwise
#print axioms Experimental.CantorBoundary.rungs_embed
#print axioms Experimental.CantorBoundary.fundamental_embeds
#print axioms Experimental.CantorBoundary.flip_flip_pointwise
#print axioms Experimental.CantorBoundary.flip_live
#print axioms Experimental.CantorBoundary.boundary_seals_itself
#print axioms Experimental.CantorBoundary.mask_mask_pointwise
#print axioms Experimental.CantorBoundary.mask_top_eq_flip
#print axioms Experimental.CantorBoundary.tail_erasing
#print axioms Experimental.CantorBoundary.tail_cons
#print axioms Experimental.CantorBoundary.encode_succ_none
#print axioms Experimental.CantorBoundary.encode_succ_some
#print axioms Experimental.CantorBoundary.tail_encode_some
#print axioms Experimental.CantorBoundary.encode_separates
#print axioms Experimental.CantorBoundary.encode_inj_of_separates

-- SpectrumSymmetry (12)
#print axioms Experimental.SpectrumSymmetry.sub_one_eq_shift
#print axioms Experimental.SpectrumSymmetry.rotF_eq_shift
#print axioms Experimental.SpectrumSymmetry.iterN_rotF_eq_iterN_shift
#print axioms Experimental.SpectrumSymmetry.gcd_succ_self
#print axioms Experimental.SpectrumSymmetry.predicted_order
#print axioms Experimental.SpectrumSymmetry.rotF_order_returns
#print axioms Experimental.SpectrumSymmetry.rotF_order_minimal
#print axioms Experimental.SpectrumSymmetry.iterN_rotS_components
#print axioms Experimental.SpectrumSymmetry.rotS_order_returns
#print axioms Experimental.SpectrumSymmetry.rotS_order_minimal
#print axioms Experimental.SpectrumSymmetry.returns_iff_rot_pow_returns
#print axioms Experimental.SpectrumSymmetry.symmetry_order_is_gcd_law

-- CouplingGauge (35)
#print axioms Experimental.CouplingGauge.xor_not_right
#print axioms Experimental.CouplingGauge.xor_right_comm
#print axioms Experimental.CouplingGauge.xor_pair_exchange
#print axioms Experimental.CouplingGauge.xor_not_exchange
#print axioms Experimental.CouplingGauge.cancel_of_xor_eq
#print axioms Experimental.CouplingGauge.true_of_not_false
#print axioms Experimental.CouplingGauge.flip_of_xor_true
#print axioms Experimental.CouplingGauge.flip_step_pointwise
#print axioms Experimental.CouplingGauge.maskS_involution_pointwise
#print axioms Experimental.CouplingGauge.ringX_mask_pointwise
#print axioms Experimental.CouplingGauge.mask_intertwines_pointwise
#print axioms Experimental.CouplingGauge.mask4_alternating
#print axioms Experimental.CouplingGauge.alternating_forces_four_dvd
#print axioms Experimental.CouplingGauge.alternating_mask_iff_four_dvd
#print axioms Experimental.CouplingGauge.ring_fixes_zero
#print axioms Experimental.CouplingGauge.flip_no_fixed_pointwise
#print axioms Experimental.CouplingGauge.flip_no_fixed_point
#print axioms Experimental.CouplingGauge.fixed_point_spectra_differ
#print axioms Experimental.CouplingGauge.flip_no_intertwiner_pointwise
#print axioms Experimental.CouplingGauge.flip_no_intertwiner
#print axioms Experimental.CouplingGauge.flip_not_conjugate
#print axioms Experimental.CouplingGauge.flip_conjugacy_of_four_dvd
#print axioms Experimental.CouplingGauge.coupling_flip_dichotomy
#print axioms Experimental.CouplingGauge.flip_conjugate_four
#print axioms Experimental.CouplingGauge.flip_no_intertwiner_two
#print axioms Experimental.CouplingGauge.flip_no_intertwiner_three
#print axioms Experimental.CouplingGauge.flip_no_intertwiner_five
#print axioms Experimental.CouplingGauge.flip_step_congr_pointwise
#print axioms Experimental.CouplingGauge.flip_step_dress_pointwise
#print axioms Experimental.CouplingGauge.flip_iter_dress_pointwise
#print axioms Experimental.CouplingGauge.flip_ring2_pulse_period_four
#print axioms Experimental.CouplingGauge.flip_ring3_pulse_period_twelve
#print axioms Experimental.CouplingGauge.flip_ring4_pulse_period_four
#print axioms Experimental.CouplingGauge.flip_ring5_pulse_period_twenty
#print axioms Experimental.CouplingGauge.mask4_alternating_four
