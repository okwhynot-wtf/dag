import Geom.Bounce
import Geom.Provision

/-!
# Geom.Profile

Capacity profiles as undirected data: horizon index → depth. Constructors
include flat, expand, and bounce.
-/

namespace Geom.Profile

open Geom.Bounce

/-- Capacity depth profile: horizon index → exponent depth. -/
def DepthProfile : Type := Nat → Nat

/-- Flat profile of constant depth. -/
def flat (C : Nat) : DepthProfile := fun _ => C

/-- Expanding (diagonal) profile: depth = horizon. -/
def expand : DepthProfile := fun t => t

/-- Bounce profile via `Geom.Bounce.bounceDepth`. -/
def bounce (tTurn : Nat) : DepthProfile := bounceDepth tTurn

/-- Exponent reading: capacity size `K ^ depth` at horizon `T`. -/
def capacityOf (K : Nat) (prof : DepthProfile) (T : Nat) : Nat :=
  K ^ prof T

/-- Alive at `T` under exponent reading: demand fits capacity. -/
def Alive (K : Nat) (prof : DepthProfile) (T : Nat) : Prop :=
  K ^ T ≤ capacityOf K prof T

/-- Flat profiles are constant. -/
theorem flat_const (C T : Nat) : flat C T = C := rfl

/-- Expand profile is the diagonal. -/
theorem expand_diag (T : Nat) : expand T = T := rfl

/-- Bounce profile agrees with `bounceDepth`. -/
theorem bounce_eq (tTurn T : Nat) :
    bounce tTurn T = bounceDepth tTurn T := rfl

/-- For `K ≥ 2`, bounce-alive iff `T ≤ tTurn` (weld to Bounce). -/
theorem bounce_alive_iff {K : Nat} (hK : 2 ≤ K) (tTurn T : Nat) :
    Alive K (bounce tTurn) T ↔ T ≤ tTurn := by
  have h := Geom.Bounce.exhaustion_tick_eq_turnaround hK tTurn T
  simpa [Alive, bounce, capacityOf, Geom.Bounce.Alive] using h

/-- Expanding conveyor length equals `K ^ T` with `K = |A|` (weld). -/
theorem expand_capacity_weld {Eout : Type} (A : List Eout) (T : Nat) :
    (Geom.Provision.expandCaps (Eout := Eout) A T).length
      = capacityOf A.length expand T := by
  simpa [capacityOf, expand] using
    Geom.Provision.expand_capacity (Eout := Eout) (A := A) T

/-! ## The exhaustion tick

"Exhaustion tick" is used throughout the exposition. It is defined here, so
that "past the exhaustion tick, muteness fails" is a statement about a defined
notion rather than a reading of an `iff`. -/

/-- `T` is *the* exhaustion tick of `prof` at merge rate `K`: alive, and
nothing after it is alive. -/
def IsExhaustionTick (K : Nat) (prof : DepthProfile) (T : Nat) : Prop :=
  Alive K prof T ∧ ∀ U, T < U → ¬ Alive K prof U

/-- The exhaustion tick is unique when it exists. -/
theorem exhaustion_tick_unique {K : Nat} {prof : DepthProfile} {T T' : Nat}
    (h : IsExhaustionTick K prof T) (h' : IsExhaustionTick K prof T') :
    T = T' := by
  cases Nat.lt_trichotomy T T' with
  | inl hlt => exact absurd h'.1 (h.2 T' hlt)
  | inr hrest =>
    cases hrest with
    | inl heq => exact heq
    | inr hgt => exact absurd h.1 (h'.2 T hgt)

/-- **The bounce's exhaustion tick is its turnaround.** -/
theorem bounce_exhaustion_tick {K : Nat} (hK : 2 ≤ K) (tTurn : Nat) :
    IsExhaustionTick K (bounce tTurn) tTurn := by
  constructor
  · exact (bounce_alive_iff hK tTurn tTurn).mpr (Nat.le_refl tTurn)
  · intro U hU hA
    exact absurd ((bounce_alive_iff hK tTurn U).mp hA)
      (fun hle => absurd (Nat.lt_of_lt_of_le hU hle) (Nat.lt_irrefl tTurn))

end Geom.Profile

#print axioms Geom.Profile.flat_const
#print axioms Geom.Profile.expand_diag
#print axioms Geom.Profile.bounce_eq
#print axioms Geom.Profile.bounce_alive_iff
#print axioms Geom.Profile.expand_capacity_weld
#print axioms Geom.Profile.exhaustion_tick_unique
#print axioms Geom.Profile.bounce_exhaustion_tick
