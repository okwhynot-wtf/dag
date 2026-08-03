import Monism

/-!
# Apophasis — derived liveness and equivalent formulations

From generation and a drawn distinction (`Monism.Draws`), liveness is a
theorem rather than a premise. The remaining clauses admit equivalent
negative formulations; `ApophaticReading` packages the interpretive
structure and inherits the spine conclusions.

* **Derived liveness** (`draws_forces_live`): `TwoCycle.Generated` and
  `Monism.Draws` imply `Orbit.Live`.
* **Static collapse** (`no_static_fundamental`, `no_constant_fills`): a
  resting point under generation yields a singleton carrier; constant
  acts are not live.
* **Equivalent formulations** (`live_iff_no_rest`, `symmetric_refuses_arrow`,
  `generated_refuses_remainder`): liveness ↔ no fixed point; symmetric
  step ↔ no asymmetric step pair; generation ↔ no third point off the
  two-cycle.
* **Interpretive structure** (`ApophaticReading`): symmetric step,
  generation, and `Draws`; liveness recovered by
  `ApophaticReading.live`.
* **Compatibility** (`ofFundamental`): `Monism.FundamentalReading` (Fundamental
  reading) converts to `ApophaticReading`.
* **Inheritance** (`apophatic_inherits_the_chain`, `apophatic_chain`):
  seal, escape, self-opacity, and causal faithfulness; full master
  conjunction at any seed.
* **Underdetermination** (`essence_exceeds_inventory`): restatement of
  `Tower.underdetermined_at_fundamental`.

No declared axioms.
-/
namespace Apophasis

open Orbit

variable {α : Type}

/-! ## Liveness derived -/

/-- A generated act with a fixed point has a singleton carrier; with
    `Monism.Draws`, the act is live. -/
theorem draws_forces_live (act : α → α) (hgen : TwoCycle.Generated act)
    (hd : Monism.Draws α) : Live act := by
  intro z hz
  obtain ⟨a, b, hab⟩ := hd
  have ha : a = z := by
    cases hgen z a with
    | inl h => exact h
    | inr h => rw [hz] at h; exact h
  have hb : b = z := by
    cases hgen z b with
    | inl h => exact h
    | inr h => rw [hz] at h; exact h
  exact hab (ha.trans hb.symm)

/-- Under generation, a fixed point forces all points to equal it. -/
theorem no_static_fundamental (act : α → α) (hgen : TwoCycle.Generated act)
    {z : α} (hz : act z = z) : ∀ w, w = z := by
  intro w
  cases hgen z w with
  | inl h => exact h
  | inr h => rw [hz] at h; exact h

/-- Constant acts are not live. -/
theorem no_constant_fills (c : α) : ¬ Live (fun _ : α => c) := by
  intro h
  exact h c rfl

/-! ## Equivalent formulations -/

/-- `Live act` iff no fixed point exists. -/
theorem live_iff_no_rest (act : α → α) :
    Live act ↔ ¬ ∃ x, act x = x := by
  constructor
  · intro h hx
    obtain ⟨x, hx⟩ := hx
    exact h x hx
  · intro h x hx
    exact h ⟨x, hx⟩

/-- `SymmetricStep act` implies no asymmetric step pair. -/
theorem symmetric_refuses_arrow (act : α → α)
    (hs : SymmetricStep act) :
    ¬ ∃ x y, Step act x y ∧ ¬ Step act y x := by
  intro h
  obtain ⟨x, y, hxy, hn⟩ := h
  exact hn (hs x y hxy)

/-- `TwoCycle.Generated act` implies no point off the two-cycle. -/
theorem generated_refuses_remainder (act : α → α)
    (hgen : TwoCycle.Generated act) :
    ¬ ∃ x y : α, y ≠ x ∧ y ≠ act x := by
  intro h
  obtain ⟨x, y, h1, h2⟩ := h
  cases hgen x y with
  | inl h => exact h1 h
  | inr h => exact h2 h

/-! ## Interpretive structure -/

/-- Apophatic reading: symmetric step, generation, and a drawn
    distinction. Liveness is derived (`ApophaticReading.live`). -/
structure ApophaticReading where
  /-- Carrier type. -/
  Carrier : Type
  /-- Fundamental act. -/
  actOf : Carrier → Carrier
  /-- Symmetric step. -/
  unoriented : Orbit.SymmetricStep actOf
  /-- Generation. -/
  simple : TwoCycle.Generated actOf
  /-- Distinct elements exist (`Monism.retorsion` applies to its
      negation). -/
  draws : Monism.Draws Carrier

/-- Liveness, derived from `draws` and `simple`. -/
theorem ApophaticReading.live (R : ApophaticReading) :
    Orbit.Live R.actOf :=
  draws_forces_live R.actOf R.simple R.draws

/-- Conversion from `Monism.FundamentalReading`; occupancy and liveness
    yield `draws`. -/
def ofFundamental (R : Monism.FundamentalReading) : ApophaticReading where
  Carrier := R.Carrier
  actOf := R.actOf
  unoriented := R.unoriented
  simple := R.simple
  draws := ⟨R.actOf R.occupied, R.occupied, R.live R.occupied⟩

/-- Carrier-level conclusions of the chain: involution, restlessness,
    seal, exhibited escape, self-opacity, exact causal transmission. -/
theorem apophatic_inherits_the_chain (R : ApophaticReading) :
    (∀ x, R.actOf (R.actOf x) = x) ∧
    (∀ x, R.actOf x ≠ x) ∧
    (∀ (A : Type) (f : A → A → R.Carrier),
      ¬ Diagonal.PointSurjective f) ∧
    (∀ (A : Type) (f : A → A → R.Carrier),
      ∃ g : A → R.Carrier, ∀ a, f a ≠ g) ∧
    (∀ (A : Type) (f : A → A → R.Carrier),
      ¬ Interior.Articulates f (Diagonal.dodgeWith R.actOf f)) ∧
    (∀ (A : Type) (f f' : A → A → R.Carrier) (a : A),
      Cause.effectOf R.actOf f a ≠ Cause.effectOf R.actOf f' a ↔
        f a a ≠ f' a a) := by
  have hl := R.live
  exact ⟨(Orbit.symmetricStep_iff_involutive R.actOf).mp R.unoriented,
         hl,
         fun _ f => Diagonal.seal_on_fundamental R.actOf hl f,
         fun _ f => Diagonal.cantor_fundamental R.actOf hl f,
         fun _ f => Interior.self_opacity R.actOf hl f,
         fun _ f f' a => Cause.fundamental_faithful R.actOf R.unoriented f f' a⟩

/-- Full master conjunction at seed `z`; the carrier is inhabited via
    `draws`. -/
theorem apophatic_chain (R : ApophaticReading) (z : R.Carrier) :
    (∀ x, R.actOf (R.actOf x) = x) ∧
    (∀ x, R.actOf x ≠ x) ∧
    (∀ n, Orbit.iter R.actOf n z = z ∨
      Orbit.iter R.actOf n z = R.actOf z) ∧
    (∀ b, R.actOf (TwoCycle.reading R.actOf z b) =
      TwoCycle.reading R.actOf z (!b)) ∧
    (∀ x, ∃ b, TwoCycle.reading R.actOf z b = x) := by
  have m := Monism.diagonal_monism R.actOf R.live R.unoriented R.simple z
  exact ⟨m.1, m.2.1, m.2.2.1, m.2.2.2.1, m.2.2.2.2.1⟩

/-! ## Underdetermination -/

/-- Every self-reading on `Bool` leaves at least two distinct predicates
    unrealized (restatement of `Tower.underdetermined_at_fundamental`). -/
theorem essence_exceeds_inventory (f : Bool → Bool → Bool) :
    ∃ g h : Bool → Bool,
      (∃ x, g x ≠ h x) ∧
      (∀ a, ∃ x, f a x ≠ g x) ∧
      (∀ a, ∃ x, f a x ≠ h x) :=
  Tower.underdetermined_at_fundamental f

/-! ## Summary -/

/-- Collected apophatic results: derived liveness, static collapse,
    equivalent formulations. -/
theorem apophasis_package (act : α → α) (hgen : TwoCycle.Generated act) :
    (Monism.Draws α → Live act) ∧
    (∀ {z : α}, act z = z → ∀ w, w = z) ∧
    (∀ c : α, ¬ Live (fun _ : α => c)) ∧
    (Live act ↔ ¬ ∃ x, act x = x) :=
  ⟨fun hd => draws_forces_live act hgen hd,
   fun {_z} hz w => no_static_fundamental act hgen hz w,
   fun c => no_constant_fills c,
   live_iff_no_rest act⟩

#print axioms Apophasis.draws_forces_live
#print axioms Apophasis.no_static_fundamental
#print axioms Apophasis.no_constant_fills
#print axioms Apophasis.live_iff_no_rest
#print axioms Apophasis.symmetric_refuses_arrow
#print axioms Apophasis.generated_refuses_remainder
#print axioms Apophasis.ApophaticReading.live
#print axioms Apophasis.ofFundamental
#print axioms Apophasis.apophatic_inherits_the_chain
#print axioms Apophasis.apophatic_chain
#print axioms Apophasis.essence_exceeds_inventory
#print axioms Apophasis.apophasis_package

end Apophasis
