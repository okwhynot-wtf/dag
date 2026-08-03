import Quintom.Kernel
import Geom.Registration

/-!
# T-6 Damping = registration (semi-formal)

Kernel skeleton: contraction is a merge; merge ⇒ record by T-4 / AG.
Identification of the register with Hubble friction `H` is a certificate
clause — dynamical content is the exhibit `exhibits/quintom/integrate.py`.
-/

namespace Dictionary.Quintom.Damping

/-- Frictionless ⇔ silent archive (kernel face). -/
theorem frictionless_silent_archive :
    Geom.Registration.Inj Dictionary.Quintom.Kernel.frictionlessStep ∧
    ¬ Geom.Registration.Merges Dictionary.Quintom.Kernel.frictionlessStep ∧
    ¬ Geom.Registration.Registers Dictionary.Quintom.Kernel.frictionlessStep :=
  Dictionary.Quintom.Kernel.frictionless_silent

/-- Merge forces record (AG / T-4 ingredient). -/
theorem merge_registers {S E : Type} {U : S × E → S × E}
    (hU : Geom.Registration.Inj U)
    (hm : Geom.Registration.Merges U) :
    Geom.Registration.Registers U :=
  Geom.Registration.merge_registers hU hm

/-- **T-6 kernel skeleton.** Silent archive at H = 0; registration law
    available for H > 0 models that merge. Full H ↔ register identification
    remains an exhibit/certificate clause. -/
theorem damping_registration_skeleton :
    (Geom.Registration.Inj Dictionary.Quintom.Kernel.frictionlessStep ∧
      ¬ Geom.Registration.Merges Dictionary.Quintom.Kernel.frictionlessStep ∧
      ¬ Geom.Registration.Registers Dictionary.Quintom.Kernel.frictionlessStep) ∧
    (∀ {S E : Type} {U : S × E → S × E},
      Geom.Registration.Inj U →
      Geom.Registration.Merges U →
      Geom.Registration.Registers U) :=
  ⟨frictionless_silent_archive, fun hU hm => merge_registers hU hm⟩

#print axioms damping_registration_skeleton
#print axioms frictionless_silent_archive

end Dictionary.Quintom.Damping
