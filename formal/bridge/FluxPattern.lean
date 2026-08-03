import Alphabet
import OneZ2
import Measurement
import EffectiveMatter
import SecondLaw
import Geom.Registration
import Branch
import Ladder

/-!
# Phase D — flux patterns without a second substance

Hypothesis H (matter = saturated record flux) does not need a unique
particle spectrum. It needs *pattern-in-flux*: distinguishable content
types carved from alphabet / channel / branch structure already present.

- **D1** `FluxComponent`: nonempty alphabet components; Bool has ≥2
- **D2** branch width / OneZ2 channels index distinct components (`Kmin = 2`)
- **D3** vacuum onset = oscillator (H=0 skeleton); matter onset = merge⇒record

Falsifier: if all saturated flux were patternless scalar pressure only.
Here we exhibit ≥2 nondegenerate components linked to channels.
-/

namespace Bridge.FluxPattern

open Bridge.EffectiveMatter
open Bridge.OneZ2

/-! ## D1 — flux components from alphabet partitions -/

/-- A flux component is a nonempty subset of the record alphabet,
    witnessed by a letter. No new ontology — only a cut of `E'`. -/
structure FluxComponent (E' : Type) where
  mem : E' → Prop
  witness : E'
  in_component : mem witness

def boolComponentFalse : FluxComponent Bool where
  mem := fun b => b = false
  witness := false
  in_component := rfl

def boolComponentTrue : FluxComponent Bool where
  mem := fun b => b = true
  witness := true
  in_component := rfl

theorem bool_components_nondegenerate :
    boolComponentFalse.witness ≠ boolComponentTrue.witness := by
  decide

/-- **D1.** At least two nondegenerate flux components exist on the
    fundamental alphabet `Bool` (no extra types). -/
theorem two_nondegenerate_flux_components :
    ∃ c₀ c₁ : FluxComponent Bool,
      c₀.witness ≠ c₁.witness ∧
      c₀.mem c₀.witness ∧ c₁.mem c₁.witness :=
  ⟨boolComponentFalse, boolComponentTrue,
   bool_components_nondegenerate,
   boolComponentFalse.in_component, boolComponentTrue.in_component⟩

/-- Channel-indexed components: φ / σ label distinct Bool letters. -/
def channelComponent : Channel → FluxComponent Bool
  | Channel.phi => boolComponentTrue
  | Channel.sigma => boolComponentFalse

theorem channels_index_distinct_components :
    (channelComponent Channel.phi).witness ≠
      (channelComponent Channel.sigma).witness := by
  decide

/-! ## D2 — branch width / ℤ/2 as species-like multiplicity -/

/-- Channels are exactly two (RE face of one ℤ/2). -/
theorem channel_multiplicity :
    ∃ c d : Channel, c ≠ d ∧ ∀ x : Channel, x = c ∨ x = d :=
  ⟨Channel.phi, Channel.sigma, by decide, fun x => by cases x <;> decide⟩

/-- Branch nodes have ≥2 escapes — local frame width = `Kmin`. -/
theorem branch_species_width (k : Nat)
    (f : Ladder.Level k → Ladder.Level k → Bool) :
    ∃ e₁ e₂ : Branch.Predicate k,
      Branch.IsEscape k f e₁ ∧ Branch.IsEscape k f e₂ ∧
        ∃ x, e₁ x ≠ e₂ x :=
  Bridge.Measurement.two_children k f

/-- **D2.** Species-like multiplicity from structure already present:
    `Kmin = 2` channels, ≥2 branch children, channels index distinct
    flux components. Not a forced unique pattern. -/
theorem species_multiplicity_from_underdetermination :
    Bridge.Alphabet.Kmin = 2 ∧
    (∃ c d : Channel, c ≠ d) ∧
    ((channelComponent Channel.phi).witness ≠
      (channelComponent Channel.sigma).witness) ∧
    (∀ k (f : Ladder.Level k → Ladder.Level k → Bool),
      ∃ e₁ e₂ : Branch.Predicate k,
        Branch.IsEscape k f e₁ ∧ Branch.IsEscape k f e₂ ∧
          ∃ x, e₁ x ≠ e₂ x) :=
  ⟨Bridge.Alphabet.Kmin_eq,
   ⟨Channel.phi, Channel.sigma, by decide⟩,
   channels_index_distinct_components,
   branch_species_width⟩

/-! ## D3 — vacuum / matter onset (H=0 / registration) -/

/-- **D3a.** Vacuum onset = oscillator class (frictionless / H=0 skeleton). -/
theorem vacuum_onset_H0_skeleton :
    VacuumDynamics Geom.Registration.oscStep :=
  osc_is_vacuum

/-- **D3b.** Matter onset = Landauer registration (merge ⇒ record).
    The H>0 / damping face in kernel dress. -/
theorem matter_onset_registration
    {S E : Type} {U : S × E → S × E}
    (hU : Geom.Registration.Inj U)
    (hm : Geom.Registration.Merges U) :
    Geom.Registration.Registers U :=
  Bridge.SecondLaw.landauer hU hm

/-- Swap is a matter-onset witness; oscillator is vacuum. -/
theorem vacuum_vs_matter_onset :
    VacuumDynamics Geom.Registration.oscStep ∧
    Geom.Registration.Merges Geom.Registration.swapStep ∧
    Geom.Registration.Registers Geom.Registration.swapStep ∧
    (∀ {S E : Type} {U : S × E → S × E},
      Geom.Registration.Inj U →
      Geom.Registration.Merges U →
      Geom.Registration.Registers U) :=
  ⟨vacuum_onset_H0_skeleton,
   Geom.Registration.swap_registers.2.1,
   Geom.Registration.swap_registers.2.2,
   fun hU hm => matter_onset_registration hU hm⟩

/-! ## Phase D package -/

/-- **Phase D.** Flux is patterned without a second substance:
    ≥2 Bool components; channels/branches supply multiplicity;
    vacuum vs matter onset = silent oscillator vs registration. -/
theorem phase_D_flux_patterns :
    (∃ c₀ c₁ : FluxComponent Bool, c₀.witness ≠ c₁.witness) ∧
    Bridge.Alphabet.Kmin = 2 ∧
    ((channelComponent Channel.phi).witness ≠
      (channelComponent Channel.sigma).witness) ∧
    VacuumDynamics Geom.Registration.oscStep ∧
    (∀ {S E : Type} {U : S × E → S × E},
      Geom.Registration.Inj U →
      Geom.Registration.Merges U →
      Geom.Registration.Registers U) :=
  ⟨⟨boolComponentFalse, boolComponentTrue, bool_components_nondegenerate⟩,
   Bridge.Alphabet.Kmin_eq,
   channels_index_distinct_components,
   vacuum_onset_H0_skeleton,
   fun hU hm => matter_onset_registration hU hm⟩

#print axioms two_nondegenerate_flux_components
#print axioms species_multiplicity_from_underdetermination
#print axioms vacuum_vs_matter_onset
#print axioms phase_D_flux_patterns

end Bridge.FluxPattern
