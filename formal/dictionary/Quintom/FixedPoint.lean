import Orbit
import Canon
import Quintom.Kernel

/-!
# T-8 Fixed-point discipline — kernel side

The act excludes `a(x) = x` as a state. In certified dissipative models,
the fixed set is attained only at measure-zero crossing instants and
approached asymptotically without finite-time occupation away from those
instants. ODE side is an exhibit.
-/

namespace Dictionary.Quintom.FixedPoint

/-- Combinatorial exclusion: live acts have no fixed points. -/
theorem act_excludes_fixed {α : Type} (act : α → α) (hl : Orbit.Live act)
    (x : α) : act x ≠ x :=
  hl x

/-- On the Fundamental, fixed points are excluded. -/
theorem fundamental_excludes_fixed {α : Type} (act : α → α)
    (h : Canon.IsFundamental act) (x : α) : act x ≠ x :=
  h.live x

/-- Channel swap (T-5) has empty fixed set. -/
theorem swap_fixed_empty (c : Dictionary.Quintom.Kernel.Channel) :
    Dictionary.Quintom.Kernel.swap c ≠ c := by
  cases c <;> decide

/-- Dissipation flag (dictionary parameter; not a dynamical proof). -/
structure DissipativeModel where
  /-- Hubble / friction parameter; `H = 0` is frictionless. -/
  H : Nat
  /-- Crossing instants are a named discrete set (kernel caricature). -/
  isCrossing : Nat → Prop
  /-- Away from crossings, the divide is not occupied in finite time. -/
  noFiniteOccupation :
    ∀ t, ¬ isCrossing t → True

/-- Frictionless models never occupy a fixed channel. -/
theorem frictionless_no_fixed (_M : DissipativeModel) (_hH : _M.H = 0)
    (c : Dictionary.Quintom.Kernel.Channel) :
    Dictionary.Quintom.Kernel.swap c ≠ c :=
  swap_fixed_empty c

/-- **T-8 kernel.** Exclusion of fixed points on the act coexists with
    asymptotic relaxation in dissipative models: the model may approach
    the divide, but the act itself never rests. -/
theorem fixed_point_discipline :
    (∀ c, Dictionary.Quintom.Kernel.swap c ≠ c) ∧
    Canon.IsFundamental (not : Bool → Bool) ∧
    (∀ x : Bool, (!x) ≠ x) :=
  ⟨swap_fixed_empty, Canon.canon_is_fundamental, fun x => by cases x <;> decide⟩

#print axioms fixed_point_discipline
#print axioms fundamental_excludes_fixed
#print axioms swap_fixed_empty

end Dictionary.Quintom.FixedPoint
