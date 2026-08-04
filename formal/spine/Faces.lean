import Interior

/-!
# Faces — comparative exhibit of diagonal signatures

Four spine theorems restated under names whose apophatic signatures they
parallel in theorem shape. No tradition is axiomatized; no dialect carrier
is identified with `not`. The claim is structural parallel between named
signatures and proved forms.

| Face | Signature | Theorem shape |
|---|---|---|
| Cantor | *neti neti* | exhibited escape from every self-inventory |
| Lawvere | untold constant Dao | no point-surjective self-map |
| Temporal | no final level | no settling; tracked ascription flips |
| Void | creatio ex nihilo | no fixed state; the excluded coincidence is uninstantiated |
-/
namespace Faces

variable {α : Type}

/-- **Cantor face.** For every inventory `f`, some predicate escapes
    `f`, with witness (`Diagonal.cantor_fundamental`). -/
theorem neti_neti {A : Type} (act : α → α) (hl : Orbit.Live act)
    (f : A → A → α) : ∃ g : A → α, ∀ a, f a ≠ g :=
  Diagonal.cantor_fundamental act hl f

/-- **Lawvere face.** No map is point-surjective onto fundamental-valued
    predicates (`Diagonal.seal_on_fundamental`). -/
theorem dao_untold {A : Type} (act : α → α) (hl : Orbit.Live act)
    (f : A → A → α) : ¬ Diagonal.PointSurjective f :=
  Diagonal.seal_on_fundamental act hl f

/-- **Temporal face.** No level settles; a flipping tracked ascription
    is never constant on its orbit. -/
theorem self_liberation (act : α → α) (hl : Orbit.Live act) :
    (∀ (A : Type) (f : A → A → α), ∃ g : A → α, ∀ a, f a ≠ g) ∧
    (∀ E : α → Bool, (∀ c, E (act c) = !(E c)) →
      ∀ c, E (act c) ≠ E c) :=
  ⟨Tower.no_settling act hl,
   fun E h => Interior.restless_refuses_stable_flag E act h⟩

/-- The three faces are one diagonal on one live act, from one
    liveness hypothesis. -/
theorem three_faces_one_diagonal {A : Type} (act : α → α)
    (hl : Orbit.Live act) (f : A → A → α) :
    (∃ g : A → α, ∀ a, f a ≠ g) ∧
    (¬ Diagonal.PointSurjective f) ∧
    (∀ E : α → Bool, (∀ c, E (act c) = !(E c)) →
      ∀ c, E (act c) ≠ E c) :=
  ⟨neti_neti act hl f,
   dao_untold act hl f,
   fun E h => Interior.restless_refuses_stable_flag E act h⟩

theorem creatio_ex_nihilo (act : α → α) (hl : Orbit.Live act) :
    ∀ x, act x ≠ x :=
  Orbit.void_is_excluded_fixed_point act hl

theorem four_faces_one_diagonal {A : Type} (act : α → α)
    (hl : Orbit.Live act) (f : A → A → α) :
    (∃ g : A → α, ∀ a, f a ≠ g) ∧
    (¬ Diagonal.PointSurjective f) ∧
    (∀ E : α → Bool, (∀ c, E (act c) = !(E c)) →
      ∀ c, E (act c) ≠ E c) ∧
    (∀ x, act x ≠ x) :=
  ⟨neti_neti act hl f,
   dao_untold act hl f,
   fun E h => Interior.restless_refuses_stable_flag E act h,
   creatio_ex_nihilo act hl⟩

#print axioms Faces.neti_neti
#print axioms Faces.dao_untold
#print axioms Faces.self_liberation
#print axioms Faces.three_faces_one_diagonal
#print axioms Faces.creatio_ex_nihilo
#print axioms Faces.four_faces_one_diagonal

end Faces
