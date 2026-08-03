import Certificate
import Quintom.Kernel
import Quintom.FixedPoint
import Orbit
import Canon
import Geom.Registration

/-!
# Quintom dictionary entry — certificate filing (T-5, T-8)

RE / re-entrant engine as the first dictionary instantiation.
Dynamical (ODE) facts live under `exhibits/quintom/` and are refused as Lean.
-/

namespace Dictionary.Quintom.Certificate

open Dictionary.Certificate
open Dictionary.Quintom

/-- Observable on which swap acts as negation: the channel bit. -/
def involutionObservable (c : Kernel.Channel) : Bool :=
  Kernel.toBool c

theorem observable_swap_as_not (c : Kernel.Channel) :
    involutionObservable (Kernel.swap c) = !(involutionObservable c) :=
  Kernel.swap_as_not c

/-- Distinguished locus: the divide `w = −1`, kernel-side as would-be fixed. -/
def divide : Kernel.Channel → Prop := fun c => Kernel.swap c = c

theorem divide_empty (c : Kernel.Channel) : ¬ divide c :=
  FixedPoint.swap_fixed_empty c

/-- Single-field no-go: no live act on a subsingleton (forced +1). -/
theorem single_field_nogo :
    ¬ ∃ act : Unit → Unit, Orbit.Live act := by
  intro ⟨act, hl⟩
  exact hl () (Subsingleton.elim (act ()) ())

/-- Filed certificate linking (a)–(d) for the quintom kernel. -/
def quintomCert : KernelCert Kernel.Channel Bool where
  swap := Kernel.swap
  involutive := Kernel.swap_involutive
  observe := involutionObservable
  obsNeg := not
  swap_as_not := observable_swap_as_not
  Fixed := divide
  fixed_iff := fun _ => Iff.rfl
  noSoloCross := fun c h => (divide_empty c) h.1

/-- **M3 filing.** Kernel sides of T-5 and T-8 plus I-4 certificate. -/
theorem quintom_filed :
    (∀ c, Kernel.swap (Kernel.swap c) = c) ∧
    (∀ c, Kernel.toBool (Kernel.swap c) = !(Kernel.toBool c)) ∧
    (Geom.Registration.Inj Kernel.frictionlessStep ∧
      ¬ Geom.Registration.Merges Kernel.frictionlessStep ∧
      ¬ Geom.Registration.Registers Kernel.frictionlessStep) ∧
    Canon.IsFundamental (not : Bool → Bool) ∧
    (∀ c, Kernel.swap c ≠ c) ∧
    (∀ x : Bool, (!x) ≠ x) ∧
    (∀ c, quintomCert.swap (quintomCert.swap c) = c) ∧
    (∀ c, ¬ quintomCert.Fixed c) ∧
    (¬ ∃ act : Unit → Unit, Orbit.Live act) :=
  ⟨Kernel.swap_involutive, Kernel.swap_as_not, Kernel.frictionless_silent,
   Canon.canon_is_fundamental, FixedPoint.swap_fixed_empty,
   fun x => by cases x <;> decide,
   quintomCert.involutive, divide_empty, single_field_nogo⟩

#print axioms quintom_filed
#print axioms single_field_nogo
#print axioms observable_swap_as_not

end Dictionary.Quintom.Certificate
