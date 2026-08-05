import SelfReference
import NoExterior
import Apophasis

/-!
# SelfArticulation — the conditional monist thesis, assembled

World is the structured self-articulation of the canon, conditional on
one drawn distinction. The package conjoins five clauses, each a
re-export in dependency order.

* **I. Retorsion** (`Monism.retorsion`): any registration distinguishing
  the denial of a drawn distinction from its affirmation draws the
  registering carrier. The antecedent of the thesis is discharged by any
  inscribed denial of it.
* **II. Articulation forced** (`Apophasis.draws_forces_live` with the
  `TwoCycle` reading laws): on a drawn carrier, a symmetric generated
  act is live and involutive and reads as negation exhaustively and
  injectively from every seed.
* **III. Witness interior** (`Observer`): every ladder level
  self-represents under seal, self-opacity, and outrun; standpoints
  arise as inhabitants of the articulation.
* **IV. No exterior standpoint** (`NoExterior`): every self-reading by
  any carrier is sealed and self-opaque, and every presentation to a
  second term retracts the articulation, forcing liveness and embedding
  the canon.
* **V. No rung completes** (`SelfReference`, `OmegaDuration`): names lag
  predicates at every level, the lag recedes under completion, and the
  ω-colimit embeds in no level. Completeness is duration.

The identification of the conditional's consequent with "world" is
interpretation and remains outside this module; the theorem states the
consequent.
-/
namespace SelfArticulation

open Orbit

/-- **Self-articulation.** Conditional monist package in five clauses:
    retorsion, forced articulation from a drawn distinction, witness
    interiority at every level, no exterior standpoint, and
    completeness only as duration. -/
theorem self_articulation :
    -- I. Retorsion: registered denial draws the registering carrier
    (∀ (M : Type) (t : Prop → M),
      t (¬ Monism.Draws M) ≠ t (Monism.Draws M) → Monism.Draws M) ∧
    -- II. Articulation forced from a drawn distinction
    (∀ (α : Type) (act : α → α), Orbit.SymmetricStep act →
      TwoCycle.Generated act → Monism.Draws α → ∀ z : α,
      Orbit.Live act ∧
      (∀ x, act (act x) = x) ∧
      (∀ b, TwoCycle.reading act z (!b) =
        act (TwoCycle.reading act z b)) ∧
      (∀ x, ∃ b, TwoCycle.reading act z b = x) ∧
      (∀ b b', TwoCycle.reading act z b = TwoCycle.reading act z b' →
        b = b')) ∧
    -- III. Witness interior at every ladder level
    (∀ k, (¬ Diagonal.PointSurjective (Ladder.rep k)) ∧
      (¬ Interior.Articulates (Ladder.rep k)
        (Diagonal.dodgeWith not (Ladder.rep k))) ∧
      (∃ b, ∀ a, ∃ x,
        Ladder.rep (k + 1) (some a) (some x) ≠
          Ladder.rep (k + 1) b (some x))) ∧
    -- IV. No exterior standpoint: witnesses sealed; presentation retracts
    (∀ (W : Type) (r : W → W → Bool),
      ¬ Diagonal.PointSurjective r ∧
      ¬ Interior.Articulates r (Diagonal.dodgeWith not r)) ∧
    (∀ (β : Type) (act : β → β) (z : β) (g : β → Bool),
      NoExterior.Presentation act z g →
      Orbit.Live act ∧
      (∀ b, g (TwoCycle.reading act z b) = b) ∧
      (∀ b b', TwoCycle.reading act z b = TwoCycle.reading act z b' →
        b = b')) ∧
    -- V. No rung completes; the colimit is duration
    (∀ k, Density.levelCard k < Density.predicateCount k) ∧
    (∀ k, SelfReference.unsayable k <
      SelfReference.unsayable (k + Density.predicateCount k)) ∧
    (∀ k, ¬ ∃ f : Limit.LevelOmega → Ladder.Level k,
      ∀ x y, f x = f y → x = y) := by
  refine ⟨fun _ t h => Monism.retorsion t h, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro α act hs hgen hd z
    have hl : Orbit.Live act := Apophasis.draws_forces_live act hgen hd
    exact ⟨hl,
      (Orbit.symmetricStep_iff_involutive act).mp hs,
      TwoCycle.reading_equivariant act hs z,
      TwoCycle.reading_surjective act hgen z,
      TwoCycle.reading_injective act hl z⟩
  · intro k
    exact ⟨Observer.observer_sealed k, Observer.observer_interior k,
      Observer.observer_outrun k⟩
  · exact NoExterior.witness_is_observer
  · intro β act z g hp
    exact ⟨NoExterior.presentation_forces_live act z g hp,
      NoExterior.presentation_retracts act z g hp,
      NoExterior.standpoint_embeds_canon act z g hp⟩
  · exact SelfReference.deficit_strict
  · exact SelfReference.lag_recedes
  · exact OmegaDuration.omega_not_a_rung

#print axioms SelfArticulation.self_articulation

end SelfArticulation
