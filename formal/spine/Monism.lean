import Interior
import Cause

/-!
# Monism — master conjunction from a live generating act

From a live, symmetric-step, generating act on a carrier, the module
derives a single conjunction chaining form, reading, diagonal seal,
tower ascent, interior opacity, and causal faithfulness.

* **Master conjunction** (`diagonal_monism`): involutive restless
  two-cycle with Bool/`¬` reading; no point-surjective self-map;
  strict naming growth with no fundamental extension; self-opacity and
  restless tracked ascription; cause/effect agreement and exact
  difference transmission.
* **Interpretive structure** (`FundamentalReading`): optional packaging of
  carrier, act, liveness, symmetry, generation, and occupancy for the
  Fundamental reading; not an axiom.
* **Inheritance** (`reading_inherits_the_chain`): any instance yields the
  carrier-level conclusions of the chain.
* **Non-vacuity** (`canonicalReading`): `Bool` with `not` is an
  instance.
* **Retorsion** (`retorsion`): if affirmation and denial of `Draws M` are
  registered distinctly, then `Draws M`.

No declared axioms.
-/
namespace Monism

/-! ## Master conjunction -/

/-- **Diagonal monism.** From liveness, symmetric step, and generation
    on `act`, the conjunction of form, reading, seal, tower, interior,
    and cause properties stated below. -/
theorem diagonal_monism {α : Type} (act : α → α)
    (hl : Orbit.Live act) (hs : Orbit.SymmetricStep act)
    (hgen : TwoCycle.Generated act) (z : α) :
    -- I. Form: involutive two-cycle
    (∀ x, act (act x) = x) ∧
    (∀ x, act x ≠ x) ∧
    (∀ n, Orbit.iter act n z = z ∨ Orbit.iter act n z = act z) ∧
    -- II. Reading: Bool/¬ coordinates
    (∀ b, act (TwoCycle.reading act z b) = TwoCycle.reading act z (!b)) ∧
    (∀ x, ∃ b, TwoCycle.reading act z b = x) ∧
    (∀ b b', TwoCycle.reading act z b = TwoCycle.reading act z b' → b = b') ∧
    -- III. Seal: no point-surjective self-map
    (∀ (A : Type) (f : A → A → α), ¬ Diagonal.PointSurjective f) ∧
    -- IV. Tower: naming growth; orientation above fundamental
    (∀ (A B : Type) (f : A → A → α) (g : B → B → α) (ι : A → B)
      (e : A → α), Tower.NamingExtension f g ι e → ∃ b, ∀ a, ι a ≠ b) ∧
    (∀ (A : Type) (f g : A → A → α) (e : A → α),
      ¬ Tower.NamingExtension f g (fun a => a) e) ∧
    (∀ (A : Type) (f : A → A → α), ∃ g : A → α, ∀ a, f a ≠ g) ∧
    -- V. Interior: self-opacity; tracked ascription flips
    (∀ (A : Type) (f : A → A → α),
      ¬ Interior.Articulates f (Diagonal.dodgeWith act f)) ∧
    (∀ (S E : α → Bool) (z₀ : α),
      TwoCycle.TDiff S act → TwoCycle.Alive S act z₀ →
        Interior.Tracks E S → ∀ c, E (act c) = !(E c)) ∧
    -- VI. Cause: determination and exact transmission
    (∀ (A : Type) (f f' : A → A → α),
      (∀ x, f x x = f' x x) →
        ∀ a, Cause.effectOf act f a = Cause.effectOf act f' a) ∧
    (∀ (A : Type) (f f' : A → A → α) (a : A),
      Cause.effectOf act f a ≠ Cause.effectOf act f' a ↔
        f a a ≠ f' a a) := by
  have form := Orbit.two_cycle act hs hl z
  refine ⟨(Orbit.symmetricStep_iff_involutive act).mp hs,
          hl,
          form.2.2,
          TwoCycle.act_reads_as_not act hs z,
          TwoCycle.reading_surjective act hgen z,
          TwoCycle.reading_injective act hl z,
          fun A f => Diagonal.seal_on_fundamental act hl f,
          fun A B f g ι e ne => Tower.strict_growth ne,
          fun A f g e => Tower.no_self_extension f g e,
          Tower.no_settling act hl,
          fun A f => Interior.self_opacity act hl f,
          fun S E z₀ hT hA htr =>
            Interior.self_modeling_forces_restless S E act z₀ hT hA htr,
          fun A f f' h => Cause.same_cause_same_effect act f f' h,
          fun A f f' a => Cause.fundamental_faithful act hs f f' a⟩

/-! ## Interpretive structure -/

/-- **Fundamental reading** (`FundamentalReading`). An interpretive
    structure: carrier, act, liveness, symmetric step, generation, and
    a distinguished point. Instantiating it is optional; the theorems
    above do not depend on any instance. -/
structure FundamentalReading where
  /-- Carrier type. -/
  Carrier : Type
  /-- Fundamental act. -/
  actOf : Carrier → Carrier
  /-- No fixed point (`Orbit.Live`). -/
  live : Orbit.Live actOf
  /-- Symmetric step (`Orbit.SymmetricStep`). -/
  unoriented : Orbit.SymmetricStep actOf
  /-- Generation (`TwoCycle.Generated`). -/
  simple : TwoCycle.Generated actOf
  /-- Distinguished element of the carrier. -/
  occupied : Carrier

/-- Any `FundamentalReading` inherits the carrier-level conclusions of
    `diagonal_monism` for its act. -/
theorem reading_inherits_the_chain (R : FundamentalReading) :
    (∀ x, R.actOf (R.actOf x) = x) ∧
    (∀ x, R.actOf x ≠ x) ∧
    (∀ (A : Type) (f : A → A → R.Carrier),
      ¬ Diagonal.PointSurjective f) ∧
    (∀ (A : Type) (f : A → A → R.Carrier), ∃ g : A → R.Carrier, ∀ a, f a ≠ g) ∧
    (∀ (A : Type) (f : A → A → R.Carrier),
      ¬ Interior.Articulates f (Diagonal.dodgeWith R.actOf f)) := by
  have m := diagonal_monism R.actOf R.live R.unoriented R.simple R.occupied
  exact ⟨m.1, m.2.1, m.2.2.2.2.2.2.1, m.2.2.2.2.2.2.2.2.2.1,
         m.2.2.2.2.2.2.2.2.2.2.1⟩

/-- Canonical instance on `Bool` with `not`. Establishes non-vacuity of
    `FundamentalReading`; does not identify `Bool` with any particular
    metaphysical Fundamental. -/
def canonicalReading : FundamentalReading where
  Carrier := Bool
  actOf := not
  live := TwoCycle.bool_fundamental.1
  unoriented := TwoCycle.bool_fundamental.2.1
  simple := TwoCycle.bool_fundamental.2.2
  occupied := true

/-! ## Retorsion -/

/-- There exist two distinct elements of `M`. -/
def Draws (M : Type) : Prop := ∃ a b : M, a ≠ b

/-- If a map `t : Prop → M` assigns different values to `Draws M` and
    its negation, then `Draws M` holds. -/
theorem retorsion {M : Type} (t : Prop → M)
    (h : t (¬ Draws M) ≠ t (Draws M)) : Draws M :=
  ⟨_, _, h⟩

#print axioms Monism.diagonal_monism
#print axioms Monism.reading_inherits_the_chain
#print axioms Monism.canonicalReading
#print axioms Monism.retorsion

end Monism
