import Geom.Bounce
import Geom.Provision
import Geom.Gradient
import Geom.Profile
import Geom.Registration
import Geom.Arc

/-!
# Obs.Recovery

Observer address on an undirected capacity profile. Local provision on
ascent; multi-tick swap archive recovers the system path; oscillator
archives are silent.
-/

namespace Obs.Recovery

/-- An observer address is a choice of reading of an undirected profile. -/
inductive Address where
  | forward
  | reverse
  deriving DecidableEq, Repr

/-- Elapsed horizon on a bounce of turnaround `tTurn` for an address. -/
def elapsed (tTurn : Nat) : Address → Nat → Nat
  | Address.forward, t => t
  | Address.reverse, t => 2 * tTurn - t

/-- Local ascent window for an address. -/
def onAscent (tTurn : Nat) : Address → Nat → Prop
  | Address.forward, t => t ≤ tTurn
  | Address.reverse, τ => τ ≤ tTurn

theorem elapsed_forward (tTurn t : Nat) :
    elapsed tTurn Address.forward t = t := rfl

theorem elapsed_reverse_at_turn (tTurn : Nat) :
    elapsed tTurn Address.reverse tTurn = tTurn := by
  show 2 * tTurn - tTurn = tTurn
  rw [Nat.two_mul, Nat.add_sub_cancel]

/-- Forward address: ascent iff elapsed coordinate ≤ turnaround. -/
theorem onAscent_forward_iff (tTurn t : Nat) :
    onAscent tTurn Address.forward t ↔ elapsed tTurn Address.forward t ≤ tTurn :=
  Iff.rfl

/-- **Forward ascent is provision.** -/
theorem forward_ascent_is_provision {Eout : Type} (A : List Eout)
    (tTurn t : Nat) (h : t ≤ tTurn) :
    (Geom.Provision.expandCaps (Eout := Eout) A t).length
      = A.length ^ Geom.Bounce.bounceDepth tTurn t :=
  Geom.Gradient.ascending_is_provision A tTurn t h

/-- **Reverse ascent is provision.** -/
theorem reverse_ascent_is_provision {Eout : Type} (A : List Eout)
    (tTurn τ : Nat) (h : τ ≤ tTurn) :
    (Geom.Provision.expandCaps (Eout := Eout) A τ).length
      = A.length ^ Geom.Bounce.bounceDepth tTurn τ :=
  Geom.Gradient.ascending_is_provision A tTurn τ h

/-- **Either address, on ascent, sees provision capacity.** -/
theorem address_ascent_is_provision {Eout : Type} (A : List Eout)
    (tTurn : Nat) (addr : Address) (t : Nat)
    (h : onAscent tTurn addr t) :
    (Geom.Provision.expandCaps (Eout := Eout) A t).length
      = A.length ^ Geom.Bounce.bounceDepth tTurn t := by
  cases addr with
  | forward => exact forward_ascent_is_provision A tTurn t h
  | reverse => exact reverse_ascent_is_provision A tTurn t h

/-- **Shared undirected profile.** -/
theorem readings_share_profile (tTurn τ : Nat) (h : τ ≤ 2 * tTurn) :
    Geom.Gradient.revDepth tTurn τ = Geom.Bounce.bounceDepth tTurn τ :=
  Geom.Gradient.rev_depth_eq tTurn τ h

/-- **Alive window is address-invariant.** -/
theorem shared_exhaustion {K : Nat} (hK : 2 ≤ K)
    (tTurn τ : Nat) (h : τ ≤ 2 * tTurn) :
    (K ^ τ ≤ K ^ Geom.Gradient.revDepth tTurn τ ↔ Geom.Bounce.Alive K tTurn τ)
    ∧ (Geom.Bounce.Alive K tTurn τ ↔ τ ≤ tTurn) :=
  Geom.Gradient.readings_share_window hK tTurn τ h

/-! ## Provision on ascent

On either address's ascent, capacity equals `|A| ^ t`. -/

/-- On ascent, capacity equals blank-adjunction `|A| ^ t`. -/
theorem local_rph_on_ascent {Eout : Type} (A : List Eout)
    (tTurn : Nat) (addr : Address) (t : Nat)
    (h : onAscent tTurn addr t) :
    (Geom.Provision.expandCaps (Eout := Eout) A t).length = A.length ^ t := by
  have hprov := address_ascent_is_provision A tTurn addr t h
  have hdepth : Geom.Bounce.bounceDepth tTurn t = t := by
    cases addr with
    | forward => exact Geom.Bounce.bounceDepth_asc h
    | reverse => exact Geom.Bounce.bounceDepth_asc h
  rw [hdepth] at hprov
  exact hprov

/-- On ascent the depth equals the elapsed coordinate and capacity matches
the expanding conveyor. -/
theorem address_epistemic_past_is_ascent {Eout : Type} (A : List Eout)
    (tTurn : Nat) (addr : Address) (t : Nat)
    (h : onAscent tTurn addr t) :
    (Geom.Provision.expandCaps (Eout := Eout) A t).length = A.length ^ t
    ∧ Geom.Bounce.bounceDepth tTurn t = t := by
  refine ⟨local_rph_on_ascent A tTurn addr t h, ?_⟩
  cases addr with
  | forward => exact Geom.Bounce.bounceDepth_asc h
  | reverse => exact Geom.Bounce.bounceDepth_asc h

/-!
# Obs.Recovery

Temporal orientation as an observer address on an undirected capacity
profile. Local provision on ascent; multi-tick swap archive recovers the
system path of prior system states; oscillator archives are silent.
-/

open Geom.Registration

/-- Swap: outgoing letter is the prior system bit. -/
theorem swap_out_is_prior (s e : Bool) :
    (swapStep (s, e)).2 = s := rfl

/-- Swap: system after the tick is the incoming environment bit. -/
theorem swap_sys_is_in (s e : Bool) :
    (swapStep (s, e)).1 = e := rfl

/-- Swap is an involution — forward and reverse dynamical branches coincide. -/
theorem swap_involution (s e : Bool) :
    swapStep (swapStep (s, e)) = (s, e) := rfl

/-- Oscillator: outgoing letter is constantly unit — archive silent. -/
theorem osc_out_silent (s : Bool) :
    (oscStep (s, ())).2 = () := rfl

/-- From a swap outgoing archive letter one recovers the prior system. -/
theorem swap_archive_recovers_prior (s e : Bool) :
    (swapStep (s, e)).2 = s :=
  swap_out_is_prior s e

/-- Multi-tick swap run: returns final system and outgoing archive. -/
def swapRun : Bool → List Bool → Bool × List Bool
  | s, [] => (s, [])
  | s, e :: es =>
      let p := swapStep (s, e)
      let q := swapRun p.1 es
      (q.1, p.2 :: q.2)

/-- System priors along a swap run (path of prior system states). -/
def swapPriors : Bool → List Bool → List Bool
  | _, [] => []
  | s, e :: es => s :: swapPriors e es

/-- Outgoing archive of a swap run equals the system path of priors. -/
theorem swap_archive_path_recovers (s : Bool) (es : List Bool) :
    (swapRun s es).2 = swapPriors s es := by
  induction es generalizing s with
  | nil => rfl
  | cons e es ih =>
    simp only [swapRun, swapPriors, swapStep]
    exact congrArg (fun outs => s :: outs) (ih e)

/-- Archive length equals horizon length. -/
theorem swap_archive_length (s : Bool) (es : List Bool) :
    (swapRun s es).2.length = es.length := by
  induction es generalizing s with
  | nil => rfl
  | cons e es ih =>
    simp only [swapRun, swapStep, List.length_cons]
    exact congrArg Nat.succ (ih e)

/-- Head of a nonempty swap archive recovers the initial system bit. -/
theorem swap_archive_head (s e : Bool) (es : List Bool) :
    ((swapRun s (e :: es)).2).head? = some s := by
  simp [swapRun, swapStep]

/-- Oscillator multi-tick archive is constantly silent. -/
def oscRun : Bool → List Unit → Bool × List Unit
  | s, [] => (s, [])
  | s, u :: us =>
      let p := oscStep (s, u)
      let q := oscRun p.1 us
      (q.1, p.2 :: q.2)

theorem osc_archive_silent (s : Bool) (us : List Unit) :
    (oscRun s us).2 = List.replicate us.length () := by
  induction us generalizing s with
  | nil => rfl
  | cons u us ih =>
    -- oscRun s (u :: us) = ((!s final), () :: (oscRun (!s) us).2)
    show (oscRun (!s) us).2.cons () = List.replicate (us.length + 1) ()
    have h : (oscRun (!s) us).2 = List.replicate us.length () := ih (!s)
    rw [h]
    rfl

/-- Recovery package: shared profile and exhaustion; provision on ascent;
swap archive recovers the path; oscillator archive is silent. -/
theorem recovery_on_bounce {Eout : Type} (A : List Eout) {K : Nat}
    (hK : 2 ≤ K) (tTurn τ t : Nat)
    (hτ : τ ≤ 2 * tTurn) (ht : t ≤ tTurn) :
    Geom.Gradient.revDepth tTurn τ = Geom.Bounce.bounceDepth tTurn τ
    ∧ (Geom.Bounce.Alive K tTurn τ ↔ τ ≤ tTurn)
    ∧ (Geom.Provision.expandCaps (Eout := Eout) A t).length = A.length ^ t
    ∧ (∀ prof : Nat → Nat, (∀ T : Nat, K ^ T ≤ K ^ prof T) →
        ∀ C : Nat, ¬ (∀ u : Nat, prof u = C))
    ∧ (∀ s : Bool, ∀ es : List Bool, (swapRun s es).2 = swapPriors s es)
    ∧ (∀ s : Bool, ∀ us : List Unit, (oscRun s us).2 = List.replicate us.length ())
    ∧ elapsed tTurn Address.forward t = t :=
  ⟨readings_share_profile tTurn τ hτ,
   (shared_exhaustion hK tTurn τ hτ).2,
   local_rph_on_ascent A tTurn Address.forward t ht,
   fun prof halive => Geom.Gradient.eternal_aliveness_needs_gradient hK prof halive,
   swap_archive_path_recovers,
   osc_archive_silent,
   elapsed_forward tTurn t⟩

/-- Recovery uses the orientation-free Gradient package as substrate. -/
theorem recovery_arc_weld {Eout : Type} (A : List Eout) {K : Nat}
    (hK : 2 ≤ K) (tTurn τ t : Nat) (hτ : τ ≤ 2 * tTurn) (ht : t ≤ tTurn) :
    (∀ prof : Nat → Nat, (∀ T : Nat, K ^ T ≤ K ^ prof T) →
        ∀ C : Nat, ¬ (∀ u : Nat, prof u = C))
    ∧ Geom.Gradient.revDepth tTurn τ = Geom.Bounce.bounceDepth tTurn τ
    ∧ (Geom.Bounce.Alive K tTurn τ ↔ τ ≤ tTurn)
    ∧ (Geom.Provision.expandCaps (Eout := Eout) A t).length
        = A.length ^ Geom.Bounce.bounceDepth tTurn t
    ∧ (Geom.Provision.expandCaps (Eout := Eout) A t).length = A.length ^ t
    ∧ (∀ s : Bool, ∀ es : List Bool, (swapRun s es).2 = swapPriors s es) :=
  let g := Geom.Arc.orientation_free_weld A hK tTurn τ t hτ ht
  ⟨g.1, g.2.1, g.2.2.1, g.2.2.2,
   local_rph_on_ascent A tTurn Address.forward t ht,
   swap_archive_path_recovers⟩

end Obs.Recovery

#print axioms Obs.Recovery.forward_ascent_is_provision
#print axioms Obs.Recovery.reverse_ascent_is_provision
#print axioms Obs.Recovery.address_ascent_is_provision
#print axioms Obs.Recovery.readings_share_profile
#print axioms Obs.Recovery.shared_exhaustion
#print axioms Obs.Recovery.local_rph_on_ascent
#print axioms Obs.Recovery.address_epistemic_past_is_ascent
#print axioms Obs.Recovery.swap_out_is_prior
#print axioms Obs.Recovery.swap_involution
#print axioms Obs.Recovery.swap_archive_path_recovers
#print axioms Obs.Recovery.osc_archive_silent
#print axioms Obs.Recovery.recovery_on_bounce
#print axioms Obs.Recovery.recovery_arc_weld
