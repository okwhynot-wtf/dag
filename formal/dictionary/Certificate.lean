import KernelAdmit
import Geom.Registration

/-!
# I-4 Dictionary admission certificates

Dictionary instantiations of the dynamics-layer admission interface
(`Bridge.KernelAdmit`). Face-swap equivariance is proved in the bridge;
this module re-states the companion declarations in the dictionary
namespace and adds dictionary filings (oscillator silent face, etc.).

Downstream dictionary modules should `import KernelAdmit` (or open
`Bridge.KernelAdmit`) for `KernelCert` / `FixedMode`.
-/

namespace Dictionary.Certificate

open Bridge.KernelAdmit

theorem bool_admitted : AdmittedBool boolCert :=
  Bridge.KernelAdmit.bool_admitted

theorem bool_admitted_faceSwap : AdmittedBool boolCert_faceSwap :=
  Bridge.KernelAdmit.bool_admitted_faceSwap

theorem boolCert_faceSwap_eq_swap (b : Bool) :
    boolCert_faceSwap.swap b = boolCert.swap b :=
  Bridge.KernelAdmit.boolCert_faceSwap_eq_swap b

/-- Companion declaration: face-swap equivariance (proved in bridge). -/
theorem bool_cert_face_equivariant :
    AdmittedBool boolCert ∧ AdmittedBool boolCert_faceSwap ∧
    (∀ b, boolCert_faceSwap.swap b = boolCert.swap b) :=
  Bridge.KernelAdmit.bool_cert_face_equivariant

theorem live_involution_cert (act : Bool → Bool)
    (hl : Orbit.Live act) :
    (∀ b, act b = !b) ∧ (∀ b, act b ≠ b) :=
  Bridge.KernelAdmit.live_involution_cert act hl

theorem empty_mode_is_void_exclusion :
    (∀ x : Bool, (!x) ≠ x) ∧
    Orbit.Live (not : Bool → Bool) :=
  Bridge.KernelAdmit.empty_mode_is_void_exclusion

/-- AG oscillator realises a silent, non-merging certificate face. -/
theorem oscillator_fits_silent :
    Geom.Registration.Inj Geom.Registration.oscStep ∧
    ¬ Geom.Registration.Merges Geom.Registration.oscStep :=
  ⟨Geom.Registration.osc_never_registers.1,
   Geom.Registration.osc_never_registers.2.1⟩

/-- Kernel exports used downstream are swap-equivariant on the Bool
    admission interface. -/
theorem kernel_exports_swap_equivariant :
    AdmittedBool boolCert ∧ AdmittedBool boolCert_faceSwap ∧
    (∀ b, boolCert_faceSwap.swap b = boolCert.swap b) ∧
    (∀ b, boolCert.swap (boolCert.swap b) = b) :=
  ⟨bool_admitted, bool_admitted_faceSwap, boolCert_faceSwap_eq_swap,
   fun b => by cases b <;> rfl⟩

#print axioms bool_admitted
#print axioms bool_admitted_faceSwap
#print axioms boolCert_faceSwap_eq_swap
#print axioms bool_cert_face_equivariant
#print axioms live_involution_cert
#print axioms empty_mode_is_void_exclusion
#print axioms oscillator_fits_silent
#print axioms kernel_exports_swap_equivariant

end Dictionary.Certificate
