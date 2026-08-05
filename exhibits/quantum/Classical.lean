import Ortho
import Canon
import Density
import Limit

/-!
# Classical — the spine, on its own, lands on the classical bit

Establishes the negative half of the answer at the fundamental layer: there the
spine does not merely fail to prove Hilbert-space structure, it **proves the
opposite**. Claims about the layers above are weaker and are marked as such
below.

* **Exactly two states** (`fundamental_has_two_states`, `no_third_state`): a
  fundamental carrier has precisely two elements. Superposition asks for a
  third pure state between two; the spine refutes that request.
* **Predicates correspond to the bit** (`bitOfPred`, `pred_takes_bit_values`,
  `bitOfPred_faithful`, `bitOfPred_surjective`): predicates on a fundamental
  carrier are determined by their two values, and every element of `Ortho.Bit`
  is realised (the last under `DecidableEq`). This is a correspondence of
  *underlying sets*. That it is an isomorphism of ortholattices — which is what
  would transport `Ortho.bit_no_superposition` back to the spine — is not
  constructed here.
* **Rung size counter** (`levelCard_closed_form`): the spine's `Density.levelCard`
  recursion satisfies `levelCard k = k + 2`. This is arithmetic about a `Nat`
  recursion, **not** a cardinality theorem about the type `Ladder.Level k`.
* **Shape of the limit** (`omega_is_base_or_stage`): every colimit element is a
  base point or a `Nat`-indexed stage. Countability follows informally; the
  theorem is the case split alone.

The load-bearing result is the first one: `no_third_state`. The remaining two
are shape observations recorded for orientation, and the module claims no more
for them than they prove. Nothing here claims Hilbert-space structure; the
module locates what an added axiom must supply.
-/
namespace Quantum.Classical

open Quantum.Ortho

/-! ## The fundamental carrier has exactly two states -/

/-- A fundamental carrier has precisely two elements: every element is one of
    the two readings from any seed, and those two differ. -/
theorem fundamental_has_two_states {α : Type} (act : α → α)
    (h : Canon.IsFundamental act) (z : α) :
    (∀ x : α,
      x = TwoCycle.reading act z false ∨ x = TwoCycle.reading act z true) ∧
    TwoCycle.reading act z false ≠ TwoCycle.reading act z true := by
  constructor
  · intro x
    obtain ⟨b, hb⟩ := TwoCycle.reading_surjective act h.exhaustive z x
    cases b
    · exact Or.inl hb.symm
    · exact Or.inr hb.symm
  · intro he
    exact Bool.noConfusion (TwoCycle.reading_injective act h.live z false true he)

/-- **No third state.** Given two distinct elements of a fundamental carrier,
    nothing else exists. This is the direct refutation of superposition at the
    fundamental layer: the request for a state that is neither of two given
    alternatives has no solution. -/
theorem no_third_state {α : Type} (act : α → α) (h : Canon.IsFundamental act)
    (x y : α) (hxy : x ≠ y) : ∀ w : α, w = x ∨ w = y := by
  intro w
  rcases h.exhaustive x w with hw | hw
  · exact Or.inl hw
  · rcases h.exhaustive x y with hy | hy
    · exact absurd hy.symm hxy
    · exact Or.inr (hw.trans hy.symm)

/-! ## Predicates on a fundamental carrier are the classical bit -/

/-- The proposition of `Ortho.bit` attached to a predicate on a fundamental
    carrier: its values at the two readings. -/
def bitOfPred {α : Type} (act : α → α) (z : α) (p : α → Bool) : Bit :=
  (p (TwoCycle.reading act z false), p (TwoCycle.reading act z true))

/-- A predicate takes only its two recorded values: it is exhausted by the
    proposition `bitOfPred` assigns to it. -/
theorem pred_takes_bit_values {α : Type} (act : α → α)
    (h : Canon.IsFundamental act) (z : α) (p : α → Bool) (x : α) :
    p x = (bitOfPred act z p).1 ∨ p x = (bitOfPred act z p).2 := by
  obtain ⟨b, hb⟩ := TwoCycle.reading_surjective act h.exhaustive z x
  cases b
  · exact Or.inl (congrArg p hb.symm)
  · exact Or.inr (congrArg p hb.symm)

/-- `bitOfPred` is faithful: predicates agreeing on the two readings agree
    everywhere. Stated pointwise, so no function extensionality is used. -/
theorem bitOfPred_faithful {α : Type} (act : α → α)
    (h : Canon.IsFundamental act) (z : α) (p q : α → Bool)
    (heq : bitOfPred act z p = bitOfPred act z q) (x : α) : p x = q x := by
  obtain ⟨b, hb⟩ := TwoCycle.reading_surjective act h.exhaustive z x
  cases b
  · rw [← hb]; exact congrArg Prod.fst heq
  · rw [← hb]; exact congrArg Prod.snd heq

/-- Every proposition of `Ortho.bit` is realised by a predicate on a
    fundamental carrier with decidable equality: the correspondence is onto. -/
theorem bitOfPred_surjective {α : Type} [DecidableEq α] (act : α → α)
    (h : Canon.IsFundamental act) (z : α) (v : Bit) :
    ∃ p : α → Bool, bitOfPred act z p = v := by
  refine ⟨fun x => if x = TwoCycle.reading act z true then v.2 else v.1, ?_⟩
  have hne : TwoCycle.reading act z false ≠ TwoCycle.reading act z true :=
    (fundamental_has_two_states act h z).2
  show ((if TwoCycle.reading act z false = TwoCycle.reading act z true then v.2
          else v.1),
        (if TwoCycle.reading act z true = TwoCycle.reading act z true then v.2
          else v.1)) = v
  rw [if_neg hne, if_pos rfl]

/-! ## Every rung is finite; the limit is countable -/

/-- The spine's level-size counter satisfies `levelCard k = k + 2`
    (`Density.levelCard_eq`). Note what this is and is not: `Density.levelCard`
    is a `Nat`-valued recursion (`0 ↦ 2`, `k+1 ↦ levelCard k + 1`), so this is
    arithmetic about that recursion, **not** a proof that the type
    `Ladder.Level k` has `k+2` inhabitants. The spine records no cardinality
    theorem about the type; `Ladder.none_is_new` gives only that each rung
    gains at least one element. -/
theorem levelCard_closed_form (k : Nat) : Density.levelCard k = k + 2 :=
  Density.levelCard_eq k

/-- The colimit carrier is exhausted by the two base points and the
    `Nat`-indexed stages. Countability follows, since `Bool ⊕ Nat` is
    countable — but that step is not formalised here, and this theorem is the
    case split alone. -/
theorem omega_is_base_or_stage :
    ∀ u : Limit.LevelOmega,
      (∃ b : Bool, u = Limit.LevelOmega.base b) ∨
      (∃ n : Nat, u = Limit.LevelOmega.stage n) := by
  intro u
  cases u with
  | base b => exact Or.inl ⟨b, rfl⟩
  | stage n => exact Or.inr ⟨n, rfl⟩

/-! ## Summary -/

/-- **The spine is classical at the fundamental layer.** Given two distinct
    elements of a fundamental carrier there is no third; the level-size counter
    is `k+2`; every colimit element is a base or a stage; and `Ortho.bit`, the
    four-element proposition structure those two states correspond to, admits
    no superposition.

    The conjuncts are of unequal weight. The first and last carry the argument.
    The middle two are shape observations — see their own docstrings for what
    they do and do not establish. The last conjunct is a statement about
    `Ortho.bit` itself; transporting it to the spine's own predicates would
    need the ortholattice isomorphism this module does not build.

    This does not say a Hilbert space is impossible. It says the fundamental
    carrier is not one, and fixes what an added axiom has to supply: a state
    space not exhausted by two alternatives. -/
theorem spine_is_classical :
    (∀ {α : Type} (act : α → α), Canon.IsFundamental act → ∀ x y : α, x ≠ y →
      ∀ w : α, w = x ∨ w = y) ∧
    (∀ k, Density.levelCard k = k + 2) ∧
    (∀ u : Limit.LevelOmega,
      (∃ b : Bool, u = Limit.LevelOmega.base b) ∨
      (∃ n : Nat, u = Limit.LevelOmega.stage n)) ∧
    ¬ Superposition bit :=
  ⟨fun act h x y hxy w => no_third_state act h x y hxy w,
   levelCard_closed_form, omega_is_base_or_stage, bit_no_superposition⟩

#print axioms Quantum.Classical.fundamental_has_two_states
#print axioms Quantum.Classical.no_third_state
#print axioms Quantum.Classical.pred_takes_bit_values
#print axioms Quantum.Classical.bitOfPred_faithful
#print axioms Quantum.Classical.bitOfPred_surjective
#print axioms Quantum.Classical.levelCard_closed_form
#print axioms Quantum.Classical.omega_is_base_or_stage
#print axioms Quantum.Classical.spine_is_classical

end Quantum.Classical
