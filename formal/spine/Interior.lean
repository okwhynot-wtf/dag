import Tower

/-!
# Interior — self-opacity, portrait mismatch, restless signature

Three asymmetries from one live-act hypothesis, stated at the
representational level.

* **Self-opacity** (`self_opacity`, `residue_definite`): the dodge is not
  articulated by any element; it equals `act (f x x)`.
* **Outdated portrait** (`outdated_portrait`): in a naming extension, no
  old element matches the new namer on all old inputs.
* **Restless signature** (`self_modeling_forces_restless`,
  `constant_ascription_not_self_modeling`,
  `restless_refuses_stable_flag`): an ascription tracking a live
  context-free witness flips under the act; constant ascriptions cannot
  track; no stable stored flag.
-/
namespace Interior

open Diagonal

variable {α : Type}

/-! ## Self-opacity -/

/-- Some element realises predicate `p` on the diagonal. -/
def Articulates {A : Type} (f : A → A → α) (p : A → α) : Prop :=
  ∃ a, f a = p

/-- Under a live act, no element articulates the dodge. -/
theorem self_opacity {A : Type} (act : α → α) (hl : Orbit.Live act)
    (f : A → A → α) :
    ¬ Articulates f (dodgeWith act f) := by
  intro ha
  obtain ⟨a, ha⟩ := ha
  exact dodgeWith_unrepresented act hl f a ha

/-- The dodge equals `act (f x x)` at each point. -/
theorem residue_definite {A : Type} (act : α → α) (f : A → A → α) :
    ∀ x, dodgeWith act f x = act (f x x) :=
  fun _ => rfl

/-! ## The outdated portrait -/

/-- In a naming extension, the new namer differs from every old element
    on some old input. -/
theorem outdated_portrait {A B : Type}
    {f : A → A → α} {g : B → B → α} {ι : A → B} {e : A → α}
    (ne : Tower.NamingExtension f g ι e) :
    ∃ b, ∀ a, ∃ x, g (ι a) (ι x) ≠ g b (ι x) := by
  obtain ⟨b, hb⟩ := ne.names
  refine ⟨b, fun a => ?_⟩
  obtain ⟨x, hx⟩ := ne.misses a
  refine ⟨x, ?_⟩
  intro h
  have h1 : g (ι a) (ι x) = f a x := ne.conservative a x
  have h2 : g b (ι x) = e x := hb x
  exact hx (h1.symm.trans (h.trans h2))

/-! ## The restless signature -/

/-- `E` tracks witness `S` pointwise. -/
def Tracks (E S : α → Bool) : Prop := ∀ c, E c = S c

theorem xor_eq_true_iff (a b : Bool) : (a ^^ b) = true ↔ a = (!b) := by
  revert a b
  decide

/-- Live context-free witness: `S (act c) = !(S c)` at every `c`. -/
theorem descent (S : α → Bool) (act : α → α) (z₀ : α)
    (hT : TwoCycle.TDiff S act) (hA : TwoCycle.Alive S act z₀) :
    ∀ c, S (act c) = !(S c) := by
  intro c
  exact (xor_eq_true_iff _ _).mp ((hT c z₀).trans hA)

/-- If `E` tracks a live context-free witness, then `E` flips under the
    act at every state. -/
theorem self_modeling_forces_restless (S E : α → Bool) (act : α → α)
    (z₀ : α) (hT : TwoCycle.TDiff S act) (hA : TwoCycle.Alive S act z₀)
    (htr : Tracks E S) : ∀ c, E (act c) = !(E c) := by
  intro c
  rw [htr (act c), htr c]
  exact descent S act z₀ hT hA c

/-- No constant ascription tracks a live context-free witness. -/
theorem constant_ascription_not_self_modeling (S : α → Bool)
    (act : α → α) (z₀ : α) (hT : TwoCycle.TDiff S act)
    (hA : TwoCycle.Alive S act z₀) (v : Bool) :
    ¬ Tracks (fun _ => v) S := by
  intro htr
  have h := self_modeling_forces_restless S (fun _ => v) act z₀ hT hA htr z₀
  cases v with
  | true => exact Bool.noConfusion h
  | false => exact Bool.noConfusion h

/-- If `E` flips under the act, then `E (act c) ≠ E c`. -/
theorem restless_refuses_stable_flag (E : α → Bool) (act : α → α)
    (h : ∀ c, E (act c) = !(E c)) : ∀ c, E (act c) ≠ E c := by
  intro c he
  rw [h c] at he
  exact Diagonal.not_restless (E c) he

/-! ## Summary -/

/-- Summary: self-opacity, outdated portrait, and restless tracking. -/
theorem interior_package (act : α → α) (hl : Orbit.Live act) :
    (∀ (A : Type) (f : A → A → α),
      ¬ Articulates f (dodgeWith act f)) ∧
    (∀ (A B : Type) (f : A → A → α) (g : B → B → α) (ι : A → B)
      (e : A → α), Tower.NamingExtension f g ι e →
        ∃ b, ∀ a, ∃ x, g (ι a) (ι x) ≠ g b (ι x)) ∧
    (∀ (S E : α → Bool) (z₀ : α),
      TwoCycle.TDiff S act → TwoCycle.Alive S act z₀ → Tracks E S →
        ∀ c, E (act c) = !(E c)) :=
  ⟨fun _ f => self_opacity act hl f,
   fun _ _ _ _ _ _ ne => outdated_portrait ne,
   fun S E z₀ hT hA htr => self_modeling_forces_restless S E act z₀ hT hA htr⟩

#print axioms Interior.self_opacity
#print axioms Interior.residue_definite
#print axioms Interior.outdated_portrait
#print axioms Interior.descent
#print axioms Interior.self_modeling_forces_restless
#print axioms Interior.constant_ascription_not_self_modeling
#print axioms Interior.restless_refuses_stable_flag
#print axioms Interior.interior_package

end Interior
