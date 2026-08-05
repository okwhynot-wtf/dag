import Overtones
import Frequencies
import WaveEquation
import CantorBoundary

/-!
# Audit — axiom footprint for `formal/experimental/`

Generated. Do not edit by hand:

```bash
python3 formal/tools/gen_audit.py
```

4 modules, 75 results. Source for `formal/AXIOMS.md`.
-/

-- Overtones (17)
#print axioms Experimental.Overtones.refl3_involution
#print axioms Experimental.Overtones.refl3'_involution
#print axioms Experimental.Overtones.three_from_two_flips
#print axioms Experimental.Overtones.cyc3_period_three
#print axioms Experimental.Overtones.refl5_involution
#print axioms Experimental.Overtones.refl5'_involution
#print axioms Experimental.Overtones.five_from_two_flips
#print axioms Experimental.Overtones.cyc5_period_five
#print axioms Experimental.Overtones.overtone_generation
#print axioms Experimental.Overtones.cyc3_injective
#print axioms Experimental.Overtones.cyc5_injective
#print axioms Experimental.Overtones.reflZero_involution
#print axioms Experimental.Overtones.reflAt_involution
#print axioms Experimental.Overtones.rot_eq_two_flips
#print axioms Experimental.Overtones.rot_from_two_flips
#print axioms Experimental.Overtones.three_from_two_flips_general
#print axioms Experimental.Overtones.five_from_two_flips_general

-- Frequencies (16)
#print axioms Experimental.Frequencies.interval_addition
#print axioms Experimental.Frequencies.harmonics_are_iterates
#print axioms Experimental.Frequencies.orders_twelve
#print axioms Experimental.Frequencies.circle_of_fifths
#print axioms Experimental.Frequencies.fifth_generates
#print axioms Experimental.Frequencies.order_eq_div_gcd_twelve
#print axioms Experimental.Frequencies.iterN_succ
#print axioms Experimental.Frequencies.shift_val
#print axioms Experimental.Frequencies.iterN_shift_val
#print axioms Experimental.Frequencies.iterN_shift_eq_self_iff
#print axioms Experimental.Frequencies.shift_order_pos
#print axioms Experimental.Frequencies.shift_order_returns
#print axioms Experimental.Frequencies.shift_order_minimal
#print axioms Experimental.Frequencies.order_eq_div_gcd
#print axioms Experimental.Frequencies.order_eq_div_gcd_twelve_general
#print axioms Experimental.Frequencies.circle_of_fifths_minimal

-- WaveEquation (31)
#print axioms Experimental.Wave.xor_cancel
#print axioms Experimental.Wave.swap_involution
#print axioms Experimental.Wave.shear_involution_pointwise
#print axioms Experimental.Wave.step_eq_two_bounce
#print axioms Experimental.Wave.reverse_is_swapped_pair
#print axioms Experimental.Wave.reverse_step_pointwise
#print axioms Experimental.Wave.reverse_step
#print axioms Experimental.Wave.step_lossless
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
#print axioms Experimental.Wave.ring4_period_four
#print axioms Experimental.Wave.dirichlet4_period_ten
#print axioms Experimental.Wave.ring2_period_two
#print axioms Experimental.Wave.ring3_period_six
#print axioms Experimental.Wave.ring5_period_ten
#print axioms Experimental.Wave.ring6_period_six
#print axioms Experimental.Wave.dirichlet3_period_eight
#print axioms Experimental.Wave.dirichlet5_period_twelve

-- CantorBoundary (11)
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
