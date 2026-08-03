import Geom.Core
import Geom.Registration
import Geom.Ledger
import Geom.Exhaustion
import Geom.Provision
import Geom.Profile
import Geom.Bounce
import Geom.Gradient
import Geom.Totality
import Geom.Freshness

/-!
# Geom.Arc

Bridges among geometry modules: registration↔ledger, provision↔exhaustion,
profile↔bounce, totality↔registration, freshness independence.
-/

namespace Geom.Arc

/-- Registration's pairwise merge-record fact is the ledger's pairwise clause
on a joint step `U : S×E → S×E` (environment not yet split). -/
theorem registration_is_ledger_pair {S E : Type}
    {U : S × E → S × E} (hU : Geom.Registration.Inj U)
    {a b : S × E} (hab : a ≠ b) (hm : (U a).1 = (U b).1) :
    (U a).2 ≠ (U b).2 :=
  Geom.Ledger.merge_registers_is_ledger_pair hU hab hm

/-- Provision's expanding conveyor meets Exhaustion's schedule hypotheses
at every tick (instance, schedule hypotheses). -/
theorem provision_meets_exhaustion {S Eout : Type}
    (g : S → S) (blank : Eout) (s0 : S) (A : List Eout) (t : Nat) :
    Geom.Exhaustion.MergesAt
      (Geom.Provision.expandStep g blank)
      (Geom.Provision.gIter g s0) (fun _ => A)
      (Geom.Provision.expandCaps A) t
    ∧ Geom.Exhaustion.FreshAt
      (Geom.Provision.expandStep g blank)
      (Geom.Provision.gIter g s0) (fun _ => A)
      (Geom.Provision.expandCaps A) t
    ∧ Geom.Exhaustion.Confined
      (Geom.Provision.expandStep g blank)
      (Geom.Provision.gIter g s0) (fun _ => A)
      (Geom.Provision.expandCaps A) t :=
  ⟨Geom.Provision.expand_merges_at g blank s0 A t,
   Geom.Provision.expand_fresh_at g blank s0 A t,
   Geom.Provision.expand_confined g blank s0 A t⟩

/-- Profile bounce constructor is Bounce's depth schedule. -/
theorem profile_bounce_is_bounce (tTurn T : Nat) :
    Geom.Profile.bounce tTurn T = Geom.Bounce.bounceDepth tTurn T :=
  Geom.Profile.bounce_eq tTurn T

/-- Gradient package is available as the orientation-free weld. -/
theorem orientation_free_weld {Eout : Type} (A : List Eout) {K : Nat}
    (hK : 2 ≤ K) (tTurn τ t : Nat) (hτ : τ ≤ 2 * tTurn) (ht : t ≤ tTurn) :
    (∀ prof : Nat → Nat, (∀ T : Nat, K ^ T ≤ K ^ prof T) →
        ∀ C : Nat, ¬ (∀ u : Nat, prof u = C))
    ∧ Geom.Gradient.revDepth tTurn τ = Geom.Bounce.bounceDepth tTurn τ
    ∧ (Geom.Bounce.Alive K tTurn τ ↔ τ ≤ tTurn)
    ∧ (Geom.Provision.expandCaps (Eout := Eout) A t).length
        = A.length ^ Geom.Bounce.bounceDepth tTurn t :=
  Geom.Gradient.orientation_free A hK tTurn τ t hτ ht

/-- Totality: on the graph of `U`, relational merge⇒register is the
graph specialization of ordinary registration on the domain. -/
theorem totality_is_registration {S E : Type}
    (U : S × E → S × E) (dom : List (S × E))
    (hU : Geom.Totality.InjOn U dom) :
    Geom.Totality.RelMerges (Geom.Totality.graphTotality U dom) 0 →
      Geom.Totality.RelRegisters (Geom.Totality.graphTotality U dom) 0 :=
  Geom.Totality.graph_rel_merge_registers U dom hU

/-- Relational merge⇒register on `graphTotality U dom` is ordinary
registration on the domain. -/
theorem scaffolding_change {S E : Type}
    (U : S × E → S × E) (dom : List (S × E))
    (hU : Geom.Totality.InjOn U dom) :
    Geom.Totality.RelMerges (Geom.Totality.graphTotality U dom) 0 →
      Geom.Totality.RelRegisters (Geom.Totality.graphTotality U dom) 0 :=
  totality_is_registration U dom hU

/-- Product freshness and stream muteness are independent; the expanding
conveyor is stream-mute without equating the predicates. -/
theorem freshness_predicates_independent {S Eout : Type}
    (g : S → S) (blank : Eout) (s0 : S) (A : List Eout) (t : Nat) :
    (∀ σ es caps u,
      Geom.Freshness.StreamMuteAt Geom.Freshness.muteU σ es caps u)
    ∧ ¬ Geom.Freshness.ProductSupport (S := Bool) (E := Bool)
        Geom.Freshness.correlatedSupport
    ∧ Geom.Freshness.ProductSupport (S := Bool) (E := Bool)
        Geom.Freshness.fullProductSupport
    ∧ ¬ Geom.Freshness.StreamMuteAt Geom.Freshness.revealU (fun _ => false)
        (fun _ => [false, true]) (fun _ => [false]) 0
    ∧ Geom.Freshness.StreamMuteAt (Geom.Provision.expandStep g blank)
        (Geom.Provision.gIter g s0) (fun _ => A)
        (Geom.Provision.expandCaps A) t :=
  Geom.Freshness.freshness_hygiene g blank s0 A t

/-- Core conjunction: merge registers; bounce alive iff ≤ turnaround;
eternal alive needs a non-flat profile. -/
theorem stage1_geometry {K : Nat} (hK : 2 ≤ K) (tTurn T : Nat) :
    (∀ {S E : Type} (U : S × E → S × E),
      Geom.Registration.Inj U →
      Geom.Registration.Merges U → Geom.Registration.Registers U)
    ∧ (Geom.Profile.Alive K (Geom.Profile.bounce tTurn) T ↔ T ≤ tTurn)
    ∧ (∀ prof : Nat → Nat, (∀ u : Nat, K ^ u ≤ K ^ prof u) →
        ∀ C : Nat, ¬ (∀ u : Nat, prof u = C)) :=
  ⟨fun U hU => Geom.Registration.merge_registers (U := U) hU,
   Geom.Profile.bounce_alive_iff hK tTurn T,
   fun prof halive => Geom.Gradient.eternal_aliveness_needs_gradient hK prof halive⟩

end Geom.Arc

#print axioms Geom.Arc.registration_is_ledger_pair
#print axioms Geom.Arc.provision_meets_exhaustion
#print axioms Geom.Arc.profile_bounce_is_bounce
#print axioms Geom.Arc.orientation_free_weld
#print axioms Geom.Arc.totality_is_registration
#print axioms Geom.Arc.scaffolding_change
#print axioms Geom.Arc.freshness_predicates_independent
#print axioms Geom.Arc.stage1_geometry
