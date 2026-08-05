import Certificate
import LCertificate
import Quintom.Kernel
import Quintom.Certificate
import Quintom.FixedPoint
import Quintom.Damping
import Quintom.Growth
import BitFlip
import Kramers
import Page
import QEC
import NoClone
import MetaProblem

/-!
# Audit — axiom footprint for `formal/dictionary/`

Generated. Do not edit by hand:

```bash
python3 formal/tools/gen_audit.py
```

13 modules, 107 results. Source for `formal/AXIOMS.md`.
-/

-- Certificate (8)
#print axioms Dictionary.Certificate.bool_admitted
#print axioms Dictionary.Certificate.bool_admitted_faceSwap
#print axioms Dictionary.Certificate.boolCert_faceSwap_eq_swap
#print axioms Dictionary.Certificate.bool_cert_face_equivariant
#print axioms Dictionary.Certificate.live_involution_cert
#print axioms Dictionary.Certificate.empty_mode_is_void_exclusion
#print axioms Dictionary.Certificate.oscillator_fits_silent
#print axioms Dictionary.Certificate.kernel_exports_swap_equivariant

-- LCertificate (2)
#print axioms Dictionary.LCertificate.registers_of_merge
#print axioms Dictionary.LCertificate.K_at_least_Kmin

-- Quintom.Kernel (8)
#print axioms Dictionary.Quintom.Kernel.swap_involutive
#print axioms Dictionary.Quintom.Kernel.toBool_ofBool
#print axioms Dictionary.Quintom.Kernel.ofBool_toBool
#print axioms Dictionary.Quintom.Kernel.swap_as_not
#print axioms Dictionary.Quintom.Kernel.frictionless_silent
#print axioms Dictionary.Quintom.Kernel.channelAct_eq_swap
#print axioms Dictionary.Quintom.Kernel.channelAct_fundamental_reading
#print axioms Dictionary.Quintom.Kernel.oscillator_triangle

-- Quintom.Certificate (8)
#print axioms Dictionary.Quintom.Certificate.observable_swap_as_not
#print axioms Dictionary.Quintom.Certificate.reSwap_involutive
#print axioms Dictionary.Quintom.Certificate.reSwap_fixes_divide
#print axioms Dictionary.Quintom.Certificate.reSwap_fixed_iff
#print axioms Dictionary.Quintom.Certificate.single_field_nogo
#print axioms Dictionary.Quintom.Certificate.divide_in_fixed
#print axioms Dictionary.Quintom.Certificate.nonempty_locus_witnessed
#print axioms Dictionary.Quintom.Certificate.quintom_filed

-- Quintom.FixedPoint (5)
#print axioms Dictionary.Quintom.FixedPoint.act_excludes_fixed
#print axioms Dictionary.Quintom.FixedPoint.fundamental_excludes_fixed
#print axioms Dictionary.Quintom.FixedPoint.swap_fixed_empty
#print axioms Dictionary.Quintom.FixedPoint.frictionless_no_fixed
#print axioms Dictionary.Quintom.FixedPoint.fixed_point_discipline

-- Quintom.Damping (3)
#print axioms Dictionary.Quintom.Damping.frictionless_silent_archive
#print axioms Dictionary.Quintom.Damping.merge_registers
#print axioms Dictionary.Quintom.Damping.damping_registration_skeleton

-- Quintom.Growth (10)
#print axioms Dictionary.Quintom.Growth.channel_is_two
#print axioms Dictionary.Quintom.Growth.channelCard_eq_Kmin
#print axioms Dictionary.Quintom.Growth.modeCount_eq
#print axioms Dictionary.Quintom.Growth.modeCount_eq_caps
#print axioms Dictionary.Quintom.Growth.modeCount_eq_predicateCount
#print axioms Dictionary.Quintom.Growth.modeCount_doubles
#print axioms Dictionary.Quintom.Growth.modeCount_doubles_Kmin
#print axioms Dictionary.Quintom.Growth.modeCount_minimal_schedule
#print axioms Dictionary.Quintom.Growth.growth_rate_weld
#print axioms Dictionary.Quintom.Growth.re_side_growth_law

-- BitFlip (10)
#print axioms Dictionary.BitFlip.flip_involutive
#print axioms Dictionary.BitFlip.bit_flip_as_not
#print axioms Dictionary.BitFlip.ofBit_bit
#print axioms Dictionary.BitFlip.bit_ofBit
#print axioms Dictionary.BitFlip.divide_empty
#print axioms Dictionary.BitFlip.single_cell_nogo
#print axioms Dictionary.BitFlip.memory_silent
#print axioms Dictionary.BitFlip.flip_reads_as_not
#print axioms Dictionary.BitFlip.bitFlip_admitted
#print axioms Dictionary.BitFlip.dictionary_extensible

-- Kramers (14)
#print axioms Dictionary.Kramers.T_sq
#print axioms Dictionary.Kramers.neg_sq
#print axioms Dictionary.Kramers.T_no_fixed
#print axioms Dictionary.Kramers.partner_ne
#print axioms Dictionary.Kramers.neg_ne_id
#print axioms Dictionary.Kramers.spin_T_as_not
#print axioms Dictionary.Kramers.forced_doublet
#print axioms Dictionary.Kramers.degeneracy_ge_two
#print axioms Dictionary.Kramers.degeneracy_eq_Kmin
#print axioms Dictionary.Kramers.singleton_not_TClosed
#print axioms Dictionary.Kramers.kramers_admitted
#print axioms Dictionary.Kramers.fixed_modes_exhaust
#print axioms Dictionary.Kramers.void_reading
#print axioms Dictionary.Kramers.clause_c_duality

-- Page (10)
#print axioms Dictionary.Page.page_inj
#print axioms Dictionary.Page.page_merges
#print axioms Dictionary.Page.page_registers
#print axioms Dictionary.Page.radiation_holds_distinctions
#print axioms Dictionary.Page.page_alive
#print axioms Dictionary.Page.page_exhaustion
#print axioms Dictionary.Page.page_curve
#print axioms Dictionary.Page.page_admitted
#print axioms Dictionary.Page.archive_must_speak_cited
#print axioms Dictionary.Page.ledger_entry_filed

-- QEC (7)
#print axioms Dictionary.QEC.qec_inj
#print axioms Dictionary.QEC.qec_syndrome_merge
#print axioms Dictionary.QEC.qec_syndrome_record
#print axioms Dictionary.QEC.syndrome_alphabet
#print axioms Dictionary.QEC.syndrome_is_registration
#print axioms Dictionary.QEC.qec_admitted
#print axioms Dictionary.QEC.two_L_domains

-- NoClone (11)
#print axioms Dictionary.NoClone.flip_involutive
#print axioms Dictionary.NoClone.observe_flip_as_neg
#print axioms Dictionary.NoClone.plus_fixed
#print axioms Dictionary.NoClone.basis_unfixed
#print axioms Dictionary.NoClone.off_diag_product
#print axioms Dictionary.NoClone.off_diag_not_bell
#print axioms Dictionary.NoClone.no_cloning
#print axioms Dictionary.NoClone.lossless_floor
#print axioms Dictionary.NoClone.no_injection_tone_to_unit
#print axioms Dictionary.NoClone.forced_ancilla
#print axioms Dictionary.NoClone.noClone_admitted

-- MetaProblem (11)
#print axioms Dictionary.MetaProblem.reports_opacity
#print axioms Dictionary.MetaProblem.reports_outdated
#print axioms Dictionary.MetaProblem.reports_restless
#print axioms Dictionary.MetaProblem.ineffability_shape
#print axioms Dictionary.MetaProblem.thin_observers_forced
#print axioms Dictionary.MetaProblem.meta_fixed_empty
#print axioms Dictionary.MetaProblem.no_stable_ascription
#print axioms Dictionary.MetaProblem.meta_admitted
#print axioms Dictionary.MetaProblem.reports_are_structural
#print axioms Dictionary.MetaProblem.meta_quantitative
#print axioms Dictionary.MetaProblem.corpus_incomplete
