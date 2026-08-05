import Observer

/-!
# NoExterior — presentation to a second term is articulation read back

World is not the presentation of the canon to a second term. This module
makes that slogan a theorem in four clauses. A *presentation* is a
pointed map from a standpoint's carrier to `Bool` carrying the act to
negation. Then:

* **Liveness forced** (`presentation_forces_live`): a carrier hosting a
  presentation has no resting point.
* **Retraction** (`presentation_retracts`): the presentation composed
  with the canon's articulation `TwoCycle.reading` is the identity; the
  standpoint's view of the canon is the canon's self-articulation read
  back.
* **Embedding** (`standpoint_embeds_canon`): the articulation into the
  standpoint is injective; the standpoint contains the canon.
* **Uniqueness** (`presentation_unique`): on a generated carrier the
  presentation is unique; no independent standpoint content remains.

The corpus witnesses (`TwoCycle.TDiff`, `TwoCycle.Alive`) yield a
presentation up to pole swap (`presentation_of_witness`), placing the
choice in the label gauge. Independently of any ambient hypothesis,
every standpoint's self-reading is sealed and self-opaque
(`witness_is_observer`): witnessing does not exempt from the interior
triad. The assembly is `no_exterior_standpoint`.
-/
namespace NoExterior

open Orbit

variable {α : Type}

/-- A presentation of the canon at a standpoint: a pointed map to `Bool`
    that carries the act to negation. -/
def Presentation (act : α → α) (z : α) (g : α → Bool) : Prop :=
  g z = true ∧ ∀ x, g (act x) = !(g x)

/-! ## Presentation forces liveness -/

/-- A carrier hosting a presentation has no resting point. -/
theorem presentation_forces_live (act : α → α) (z : α) (g : α → Bool)
    (hp : Presentation act z g) : Live act := by
  intro x hfix
  have h := hp.2 x
  rw [hfix] at h
  cases hgx : g x with
  | true => rw [hgx] at h; exact absurd h (by decide)
  | false => rw [hgx] at h; exact absurd h (by decide)

/-! ## Retraction and embedding -/

/-- The presentation returns the canon's own articulation: the composite
    with `TwoCycle.reading` is the identity on `Bool`. -/
theorem presentation_retracts (act : α → α) (z : α) (g : α → Bool)
    (hp : Presentation act z g) :
    ∀ b, g (TwoCycle.reading act z b) = b := by
  intro b
  cases b with
  | true => exact hp.1
  | false =>
    show g (act z) = false
    rw [hp.2 z, hp.1]
    rfl

/-- The standpoint contains the canon: the articulation into a carrier
    hosting a presentation is injective. -/
theorem standpoint_embeds_canon (act : α → α) (z : α) (g : α → Bool)
    (hp : Presentation act z g) :
    ∀ b b', TwoCycle.reading act z b = TwoCycle.reading act z b' →
      b = b' := by
  intro b b' h
  have hb := presentation_retracts act z g hp b
  have hb' := presentation_retracts act z g hp b'
  rw [← hb, ← hb', h]

/-! ## Uniqueness on generated carriers -/

/-- On a generated carrier the presentation is unique: the view carries
    no information beyond the articulation. -/
theorem presentation_unique (act : α → α) (z : α)
    (hgen : TwoCycle.Generated act) (g g' : α → Bool)
    (hp : Presentation act z g) (hp' : Presentation act z g') :
    ∀ x, g x = g' x := by
  intro x
  cases hgen z x with
  | inl h => rw [h, hp.1, hp'.1]
  | inr h => rw [h, hp.2 z, hp'.2 z, hp.1, hp'.1]

/-! ## Bridge from the corpus witnesses -/

/-- `TDiff` and `Alive` yield pointwise co-equivariance. -/
theorem coequivariant_of_witness (g : α → Bool) (act : α → α) (z₀ : α)
    (hT : TwoCycle.TDiff g act) (hA : TwoCycle.Alive g act z₀) :
    ∀ x, g (act x) = !(g x) := by
  intro x
  have h : (g (act x) ^^ g x) = true := by
    have hx := hT x z₀
    rw [hx]
    exact hA
  cases hgx : g x with
  | true =>
    cases hax : g (act x) with
    | true => rw [hgx, hax] at h; exact absurd h (by decide)
    | false => rfl
  | false =>
    cases hax : g (act x) with
    | true => rfl
    | false => rw [hgx, hax] at h; exact absurd h (by decide)

/-- A live context-free witness determines a presentation up to pole
    swap: some presentation agrees with the witness or with its flip.
    The residual choice is the label gauge and nothing else. -/
theorem presentation_of_witness (g : α → Bool) (act : α → α) (z : α)
    (hT : TwoCycle.TDiff g act) (hA : TwoCycle.Alive g act z) :
    ∃ g' : α → Bool, Presentation act z g' ∧
      ((∀ x, g' x = g x) ∨ (∀ x, g' x = !(g x))) := by
  have hco := coequivariant_of_witness g act z hT hA
  cases hz : g z with
  | true => exact ⟨g, ⟨hz, hco⟩, Or.inl fun _ => rfl⟩
  | false =>
    refine ⟨fun x => !(g x), ⟨?_, ?_⟩, Or.inr fun _ => rfl⟩
    · show (!(g z)) = true
      rw [hz]
      rfl
    · intro x
      show (!(g (act x))) = (!(!(g x)))
      rw [hco x]

/-! ## Witnessing does not exempt -/

/-- Any standpoint whatsoever, equipped with any self-reading, is sealed
    and self-opaque: the interior triad applies to witnesses. -/
theorem witness_is_observer (W : Type) (r : W → W → Bool) :
    ¬ Diagonal.PointSurjective r ∧
    ¬ Interior.Articulates r (Diagonal.dodgeWith not r) :=
  ⟨Diagonal.seal_bool r,
   Interior.self_opacity not TwoCycle.bool_fundamental.1 r⟩

/-! ## Assembly -/

/-- **No exterior standpoint.** (A) Every standpoint's self-reading is
    sealed and self-opaque. (B) Every presentation forces liveness,
    retracts the canon's articulation, and embeds the canon. (C) On
    generated carriers the presentation is unique. A second term's view
    of the fundamental is the fundamental's self-articulation read back,
    and the second term is itself subject to the interior triad. -/
theorem no_exterior_standpoint :
    (∀ (W : Type) (r : W → W → Bool),
      ¬ Diagonal.PointSurjective r ∧
      ¬ Interior.Articulates r (Diagonal.dodgeWith not r)) ∧
    (∀ (β : Type) (act : β → β) (z : β) (g : β → Bool),
      Presentation act z g →
      Orbit.Live act ∧
      (∀ b, g (TwoCycle.reading act z b) = b) ∧
      (∀ b b', TwoCycle.reading act z b = TwoCycle.reading act z b' →
        b = b')) ∧
    (∀ (β : Type) (act : β → β) (z : β),
      TwoCycle.Generated act → ∀ g g' : β → Bool,
      Presentation act z g → Presentation act z g' →
      ∀ x, g x = g' x) :=
  ⟨witness_is_observer,
   fun _ act z g hp =>
     ⟨presentation_forces_live act z g hp,
      presentation_retracts act z g hp,
      standpoint_embeds_canon act z g hp⟩,
   fun _ act z hgen g g' hp hp' =>
     presentation_unique act z hgen g g' hp hp'⟩

#print axioms NoExterior.presentation_forces_live
#print axioms NoExterior.presentation_retracts
#print axioms NoExterior.standpoint_embeds_canon
#print axioms NoExterior.presentation_unique
#print axioms NoExterior.coequivariant_of_witness
#print axioms NoExterior.presentation_of_witness
#print axioms NoExterior.witness_is_observer
#print axioms NoExterior.no_exterior_standpoint

end NoExterior
