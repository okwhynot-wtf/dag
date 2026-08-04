import Diagonal

/-!
# Tower — naming extension, orientation, and underdetermination

From `Diagonal.seal_on_fundamental` and a live symmetric act, derives iterated
self-articulation by naming extensions.

* **Naming** (`NamingExtension`): an embedding that conserves the old
  reading and names an arbitrary unrepresented escape predicate; the
  Lawvere dodge is the default special case (`of_dodge`).
* **Strict growth** (`namer_is_new`, `strict_growth`): the namer of an
  escape lies outside the image of the old carrier (from unrepresentation,
  without a separate liveness hypothesis).
* **Arrow placement** (`arrow_placement`, `no_self_extension`): the
  fundamental step is involutive; no naming extension is reflexive on a
  carrier.
* **No settling** (`no_settling`): at every level some predicate escapes
  the representation.
* **Underdetermination** (`underdetermined_at_fundamental`): at the fundamental,
  any reading leaves at least two distinct unrepresented predicates.
* **First emanation** (`first_emanation`, `first_emanation_of`): a
  concrete one-step naming extension at the fundamental; the default names
  `not` applied to the constant reading, and any fundamental escape yields a
  naming extension.
-/
namespace Tower

open Diagonal

variable {α : Type}

/-! ## Naming extensions -/

/-- A naming extension: embedding `ι`, conservative successor `g`, and
    some `b` naming an escape predicate `e` that no old row matches. -/
structure NamingExtension {A B : Type}
    (f : A → A → α) (g : B → B → α) (ι : A → B) (e : A → α) : Prop where
  conservative : ∀ a a', g (ι a) (ι a') = f a a'
  misses : ∀ a, ∃ x, f a x ≠ e x
  names : ∃ b, ∀ a, g b (ι a) = e a

/-- The Lawvere dodge of a live act is a naming-extension escape. -/
theorem of_dodge {A B : Type} (act : α → α) (hl : Orbit.Live act)
    {f : A → A → α} {g : B → B → α} {ι : A → B}
    (cons : ∀ a a', g (ι a) (ι a') = f a a')
    (nm : ∃ b, ∀ a, g b (ι a) = dodgeWith act f a) :
    NamingExtension f g ι (dodgeWith act f) where
  conservative := cons
  misses := fun a => ⟨a, fun h => hl (f a a) h.symm⟩
  names := nm

/-- In a naming extension, the namer of the escape is not in the image
    of `ι`. -/
theorem namer_is_new {A B : Type} {f : A → A → α} {g : B → B → α}
    {ι : A → B} {e : A → α} (ne : NamingExtension f g ι e) :
    ∃ b, (∀ a, g b (ι a) = e a) ∧ (∀ a, ι a ≠ b) := by
  obtain ⟨b, hb⟩ := ne.names
  refine ⟨b, hb, ?_⟩
  intro a hab
  obtain ⟨x, hx⟩ := ne.misses a
  have h1 : g (ι a) (ι x) = f a x := ne.conservative a x
  have h2 : g b (ι x) = e x := hb x
  have heq : f a x = e x := by
    rw [← h1, hab, h2]
  exact hx heq

/-- Some element of the new carrier lies outside the image of `ι`. -/
theorem strict_growth {A B : Type} {f : A → A → α} {g : B → B → α}
    {ι : A → B} {e : A → α} (ne : NamingExtension f g ι e) :
    ∃ b, ∀ a, ι a ≠ b := by
  obtain ⟨b, _, hnew⟩ := namer_is_new ne
  exact ⟨b, hnew⟩

/-! ## Orientation -/

/-- No naming extension with identity embedding exists. -/
theorem no_self_extension {A : Type} (f g : A → A → α) (e : A → α) :
    ¬ NamingExtension f g (fun a => a) e := by
  intro ne
  obtain ⟨b, hnew⟩ := strict_growth ne
  exact hnew b rfl

/-- The act is involutive on the fundamental, and no naming extension is
    reflexive on any carrier. -/
theorem arrow_placement (act : α → α) (hs : Orbit.SymmetricStep act) :
    (∀ x, act (act x) = x) ∧
    (∀ (A : Type) (f g : A → A → α) (e : A → α),
      ¬ NamingExtension f g (fun a => a) e) :=
  ⟨(Orbit.symmetricStep_iff_involutive act).mp hs,
   fun _ f g e => no_self_extension f g e⟩

/-! ## No settling -/

/-- At every level, some predicate is not represented on the diagonal. -/
theorem no_settling (act : α → α) (hl : Orbit.Live act) :
    ∀ (A : Type) (f : A → A → α), ∃ g : A → α, ∀ a, f a ≠ g :=
  fun _ f => cantor_fundamental act hl f

/-! ## Contingency -/

/-- Negation is injective on Bool. -/
theorem not_inj {a b : Bool} (h : (!a) = (!b)) : a = b := by
  cases a <;> cases b <;> first | rfl | exact absurd h (by decide)

/-- For represented pairs `(ut,uf)` and `(vt,vf)`, two distinct pairs
    escape both; witnesses are diagonal and anti-diagonal dodges. -/
theorem underdetermined_core (ut uf vt vf : Bool) :
    ∃ g1 g2 h1 h2 : Bool,
      (g1 ≠ h1 ∨ g2 ≠ h2) ∧
      (g1 ≠ ut ∨ g2 ≠ uf) ∧ (g1 ≠ vt ∨ g2 ≠ vf) ∧
      (h1 ≠ ut ∨ h2 ≠ uf) ∧ (h1 ≠ vt ∨ h2 ≠ vf) :=
  if hu : ut = vt then
    if hf : uf = vf then
      ⟨!ut, !vf, ut, !uf,
        Or.inl (not_restless ut),
        Or.inl (not_restless ut),
        Or.inl (fun e => not_restless ut (e.trans hu.symm)),
        Or.inr (not_restless uf),
        Or.inr (fun e => not_restless uf (e.trans hf.symm))⟩
    else
      ⟨!ut, !vf, !vt, !uf,
        Or.inr (fun e => hf (not_inj e).symm),
        Or.inl (not_restless ut),
        Or.inr (not_restless vf),
        Or.inr (not_restless uf),
        Or.inl (not_restless vt)⟩
  else
    ⟨!ut, !vf, !vt, !uf,
      Or.inl (fun e => hu (not_inj e)),
      Or.inl (not_restless ut),
      Or.inr (not_restless vf),
      Or.inr (not_restless uf),
      Or.inl (not_restless vt)⟩

/-- At the fundamental, any reading leaves at least two distinct predicates
    unrepresented on the diagonal. -/
theorem underdetermined_at_fundamental (f : Bool → Bool → Bool) :
    ∃ g h : Bool → Bool,
      (∃ x, g x ≠ h x) ∧
      (∀ a, ∃ x, f a x ≠ g x) ∧
      (∀ a, ∃ x, f a x ≠ h x) := by
  obtain ⟨g1, g2, h1, h2, hgh, hgu, hgv, hhu, hhv⟩ :=
    underdetermined_core (f true true) (f true false)
      (f false true) (f false false)
  refine ⟨fun x => cond x g1 g2, fun x => cond x h1 h2, ?_, ?_, ?_⟩
  · cases hgh with
    | inl h => exact ⟨true, h⟩
    | inr h => exact ⟨false, h⟩
  · intro a
    cases a with
    | true =>
      cases hgu with
      | inl h => exact ⟨true, fun e => h e.symm⟩
      | inr h => exact ⟨false, fun e => h e.symm⟩
    | false =>
      cases hgv with
      | inl h => exact ⟨true, fun e => h e.symm⟩
      | inr h => exact ⟨false, fun e => h e.symm⟩
  · intro a
    cases a with
    | true =>
      cases hhu with
      | inl h => exact ⟨true, fun e => h e.symm⟩
      | inr h => exact ⟨false, fun e => h e.symm⟩
    | false =>
      cases hhv with
      | inl h => exact ⟨true, fun e => h e.symm⟩
      | inr h => exact ⟨false, fun e => h e.symm⟩

/-- Two-point extension of Bool values along distinguished points, with
    a default off that pair. Defined via `decEq` matches for axiom-free
    reduction. -/
def ext2 {A : Type} [DecidableEq A] (p q : A) (u v : Bool)
    (d : A → Bool) : A → Bool :=
  fun x =>
    match decEq x p, decEq x q with
    | isTrue _, _ => u
    | isFalse _, isTrue _ => v
    | isFalse _, isFalse _ => d x

theorem ext2_at_p {A : Type} [DecidableEq A] (p q : A) (u v : Bool)
    (d : A → Bool) : ext2 p q u v d p = u := by
  dsimp [ext2]
  cases h : decEq p p with
  | isTrue _ => rfl
  | isFalse n => exact absurd rfl n

theorem ext2_at_q {A : Type} [DecidableEq A] (p q : A) (hpq : p ≠ q)
    (u v : Bool) (d : A → Bool) : ext2 p q u v d q = v := by
  dsimp [ext2]
  cases h : decEq q p with
  | isTrue heq => exact absurd heq hpq.symm
  | isFalse _ =>
    cases h' : decEq q q with
    | isTrue _ => rfl
    | isFalse n => exact absurd rfl n

theorem ext2_off {A : Type} [DecidableEq A] (p q : A) (u v : Bool)
    (d : A → Bool) (x : A) (hp : x ≠ p) (hq : x ≠ q) :
    ext2 p q u v d x = d x := by
  dsimp [ext2]
  cases h : decEq x p with
  | isTrue heq => exact absurd heq hp
  | isFalse _ =>
    cases h' : decEq x q with
    | isTrue heq => exact absurd heq hq
    | isFalse _ => rfl

/-- On any decidable carrier with two distinct points, every Bool-valued
    reading omits at least two distinct predicates. Witnesses agree with
    the Bool-core on the two points and equal the dodge elsewhere. -/
theorem underdetermined_at_two {A : Type} [DecidableEq A]
    (p q : A) (hpq : p ≠ q) (f : A → A → Bool) :
    ∃ g h : A → Bool,
      (∃ x, g x ≠ h x) ∧
      (∀ a, ∃ x, f a x ≠ g x) ∧
      (∀ a, ∃ x, f a x ≠ h x) := by
  obtain ⟨g1, g2, h1, h2, hgh, hgu, hgv, hhu, hhv⟩ :=
    underdetermined_core (f p p) (f p q) (f q p) (f q q)
  let g := ext2 p q g1 g2 (fun x => !(f x x))
  let h := ext2 p q h1 h2 (fun x => !(f x x))
  have gp : g p = g1 := ext2_at_p p q g1 g2 _
  have gq : g q = g2 := ext2_at_q p q hpq g1 g2 _
  have hp' : h p = h1 := ext2_at_p p q h1 h2 _
  have hq' : h q = h2 := ext2_at_q p q hpq h1 h2 _
  refine ⟨g, h, ?_, ?_, ?_⟩
  · cases hgh with
    | inl hne =>
      refine ⟨p, ?_⟩
      rw [gp, hp']
      exact hne
    | inr hne =>
      refine ⟨q, ?_⟩
      rw [gq, hq']
      exact hne
  · intro a
    if hap : a = p then
      cases hgu with
      | inl hne =>
        refine ⟨p, ?_⟩
        rw [hap, gp]
        exact fun e => hne e.symm
      | inr hne =>
        refine ⟨q, ?_⟩
        rw [hap, gq]
        exact fun e => hne e.symm
    else if haq : a = q then
      cases hgv with
      | inl hne =>
        refine ⟨p, ?_⟩
        rw [haq, gp]
        exact fun e => hne e.symm
      | inr hne =>
        refine ⟨q, ?_⟩
        rw [haq, gq]
        exact fun e => hne e.symm
    else
      refine ⟨a, ?_⟩
      have ga : g a = !(f a a) := ext2_off p q g1 g2 _ a hap haq
      rw [ga]
      intro e
      exact Diagonal.not_restless (f a a) e.symm
  · intro a
    if hap : a = p then
      cases hhu with
      | inl hne =>
        refine ⟨p, ?_⟩
        rw [hap, hp']
        exact fun e => hne e.symm
      | inr hne =>
        refine ⟨q, ?_⟩
        rw [hap, hq']
        exact fun e => hne e.symm
    else if haq : a = q then
      cases hhv with
      | inl hne =>
        refine ⟨p, ?_⟩
        rw [haq, hp']
        exact fun e => hne e.symm
      | inr hne =>
        refine ⟨q, ?_⟩
        rw [haq, hq']
        exact fun e => hne e.symm
    else
      refine ⟨a, ?_⟩
      have ha : h a = !(f a a) := ext2_off p q h1 h2 _ a hap haq
      rw [ha]
      intro e
      exact Diagonal.not_restless (f a a) e.symm

def ext2v {A : Type} [DecidableEq A] (p q : A) (u v : α)
    (d : A → α) : A → α :=
  fun x =>
    match decEq x p, decEq x q with
    | isTrue _, _ => u
    | isFalse _, isTrue _ => v
    | isFalse _, isFalse _ => d x

theorem ext2v_at_p {A : Type} [DecidableEq A] (p q : A) (u v : α)
    (d : A → α) : ext2v p q u v d p = u := by
  dsimp [ext2v]
  cases h : decEq p p with
  | isTrue _ => rfl
  | isFalse n => exact absurd rfl n

theorem ext2v_at_q {A : Type} [DecidableEq A] (p q : A) (hpq : p ≠ q)
    (u v : α) (d : A → α) : ext2v p q u v d q = v := by
  dsimp [ext2v]
  cases h : decEq q p with
  | isTrue heq => exact absurd heq hpq.symm
  | isFalse _ =>
    cases h' : decEq q q with
    | isTrue _ => rfl
    | isFalse n => exact absurd rfl n

theorem ext2v_off {A : Type} [DecidableEq A] (p q : A) (u v : α)
    (d : A → α) (x : A) (hp : x ≠ p) (hq : x ≠ q) :
    ext2v p q u v d x = d x := by
  dsimp [ext2v]
  cases h : decEq x p with
  | isTrue heq => exact absurd heq hp
  | isFalse _ =>
    cases h' : decEq x q with
    | isTrue heq => exact absurd heq hq
    | isFalse _ => rfl

theorem underdetermined_at_two_valued [DecidableEq α] {A : Type}
    [DecidableEq A] (act : α → α) (hl : Orbit.Live act)
    (p q : A) (hpq : p ≠ q) (f : A → A → α) :
    ∃ g h : A → α,
      (∃ x, g x ≠ h x) ∧
      (∀ a, ∃ x, f a x ≠ g x) ∧
      (∀ a, ∃ x, f a x ≠ h x) := by
  have hdodge : ∀ a, ∃ x, f a x ≠ dodgeWith act f x :=
    fun a => ⟨a, fun e => hl (f a a) e.symm⟩
  if hqp : f q p = act (f p p) then
    if hpq2 : f p q = act (f q q) then
      refine ⟨dodgeWith act f,
        ext2v p q (f p p) (f q q) (dodgeWith act f), ?_, hdodge, ?_⟩
      · refine ⟨p, ?_⟩
        rw [ext2v_at_p]
        exact hl (f p p)
      · intro a
        if hap : a = p then
          refine ⟨q, ?_⟩
          rw [ext2v_at_q p q hpq, hap, hpq2]
          exact hl (f q q)
        else if haq : a = q then
          refine ⟨p, ?_⟩
          rw [ext2v_at_p, haq, hqp]
          exact hl (f p p)
        else
          refine ⟨a, ?_⟩
          rw [ext2v_off p q _ _ _ a hap haq]
          exact fun e => hl (f a a) e.symm
    else
      refine ⟨dodgeWith act f,
        ext2v p q (f p p) (act (f q q)) (dodgeWith act f), ?_, hdodge, ?_⟩
      · refine ⟨p, ?_⟩
        rw [ext2v_at_p]
        exact hl (f p p)
      · intro a
        if hap : a = p then
          refine ⟨q, ?_⟩
          rw [ext2v_at_q p q hpq, hap]
          exact hpq2
        else if haq : a = q then
          refine ⟨q, ?_⟩
          rw [ext2v_at_q p q hpq, haq]
          exact fun e => hl (f q q) e.symm
        else
          refine ⟨a, ?_⟩
          rw [ext2v_off p q _ _ _ a hap haq]
          exact fun e => hl (f a a) e.symm
  else
    refine ⟨dodgeWith act f,
      ext2v p q (act (f p p)) (f q q) (dodgeWith act f), ?_, hdodge, ?_⟩
    · refine ⟨q, ?_⟩
      rw [ext2v_at_q p q hpq]
      exact hl (f q q)
    · intro a
      if hap : a = p then
        refine ⟨p, ?_⟩
        rw [ext2v_at_p, hap]
        exact fun e => hl (f p p) e.symm
      else if haq : a = q then
        refine ⟨p, ?_⟩
        rw [ext2v_at_p, haq]
        exact hqp
      else
        refine ⟨a, ?_⟩
        rw [ext2v_off p q _ _ _ a hap haq]
        exact fun e => hl (f a a) e.symm

theorem underdetermination_needs_two_points {A : Type}
    (hsub : ∀ x y : A, x = y) (f : A → A → Bool) (g h : A → Bool)
    (hg : ∀ a, ∃ x, f a x ≠ g x) (hh : ∀ a, ∃ x, f a x ≠ h x) :
    ∀ x, g x = h x := by
  intro x
  obtain ⟨y, hy⟩ := hg x
  obtain ⟨z, hz⟩ := hh x
  rw [hsub y x] at hy
  rw [hsub z x] at hz
  have key : ∀ a b c : Bool, a ≠ b → a ≠ c → b = c := by decide
  exact key (f x x) (g x) (h x) hy hz

/-! ## Non-vacuity: the first emanation, concretely -/

/-- Fundamental reading: each state names its constant predicate. -/
def f₀ : Bool → Bool → Bool := fun a _ => a

/-- The dodge of `f₀` is pointwise negation. -/
theorem dodge_f₀_is_not : ∀ x, dodgeWith not f₀ x = !x :=
  fun _ => rfl

/-- Successor reading naming a given fundamental escape `e` at `none`. -/
def gOf (e : Bool → Bool) : Option Bool → Option Bool → Bool
  | some a, some x => f₀ a x
  | some _, none => false
  | none, some x => e x
  | none, none => false

/-- Successor reading: `none` names the dodge of the predecessor. -/
def g₀ : Option Bool → Option Bool → Bool :=
  gOf (fun x => !x)

/-- Any unrepresented fundamental escape yields a naming extension of `f₀`. -/
theorem first_emanation_of (e : Bool → Bool)
    (hm : ∀ a, ∃ x, f₀ a x ≠ e x) :
    NamingExtension f₀ (gOf e) (fun a => some a) e :=
  ⟨fun _ _ => rfl, hm, ⟨none, fun _ => rfl⟩⟩

/-- `g₀` is a naming extension of `f₀` under `not` (default dodge). -/
theorem first_emanation :
    NamingExtension f₀ g₀ (fun a => some a) (fun x => !x) :=
  first_emanation_of (fun x => !x) (fun a => ⟨a, by
    cases a <;> decide⟩)

/-- The namer in `first_emanation` is not in the image of `some`. -/
theorem first_emanation_grows :
    ∃ b, ∀ a : Bool, (some a : Option Bool) ≠ b :=
  strict_growth first_emanation

/-- Two distinct fundamental escapes yield distinct first-step namings at
    `none`. -/
theorem first_emanations_differ (e e' : Bool → Bool)
    (hne : ∃ x, e x ≠ e' x) :
    ∃ x : Bool, gOf e none (some x) ≠ gOf e' none (some x) :=
  hne

/-- Underdetermination at `f₀` supplies two distinct first emanations. -/
theorem first_step_underdetermined :
    ∃ e e' : Bool → Bool,
      (∃ x, e x ≠ e' x) ∧
      NamingExtension f₀ (gOf e) (fun a => some a) e ∧
      NamingExtension f₀ (gOf e') (fun a => some a) e' ∧
      (∃ x, gOf e none (some x) ≠ gOf e' none (some x)) := by
  obtain ⟨e, e', hne, he, he'⟩ := underdetermined_at_fundamental f₀
  exact ⟨e, e', hne, first_emanation_of e he, first_emanation_of e' he',
    first_emanations_differ e e' hne⟩

/-! ## Summary -/

/-- Summary: strict growth, involutive fundamental, no reflexive extension,
    no settling, and underdetermination at the fundamental. -/
theorem tower_package (act : α → α) (hs : Orbit.SymmetricStep act)
    (hl : Orbit.Live act) :
    (∀ (A B : Type) (f : A → A → α) (g : B → B → α) (ι : A → B)
      (e : A → α), NamingExtension f g ι e → ∃ b, ∀ a, ι a ≠ b) ∧
    (∀ x, act (act x) = x) ∧
    (∀ (A : Type) (f g : A → A → α) (e : A → α),
      ¬ NamingExtension f g (fun a => a) e) ∧
    (∀ (A : Type) (f : A → A → α), ∃ g : A → α, ∀ a, f a ≠ g) ∧
    (∃ e e' : Bool → Bool,
      (∃ x, e x ≠ e' x) ∧
      NamingExtension f₀ (gOf e) (fun a => some a) e ∧
      NamingExtension f₀ (gOf e') (fun a => some a) e') :=
  ⟨fun _ _ _ _ _ _ ne => strict_growth ne,
   (Orbit.symmetricStep_iff_involutive act).mp hs,
   fun _ f g e => no_self_extension f g e,
   no_settling act hl,
   by
     obtain ⟨e, e', hne, he, he', _⟩ := first_step_underdetermined
     exact ⟨e, e', hne, he, he'⟩⟩

#print axioms Tower.of_dodge
#print axioms Tower.namer_is_new
#print axioms Tower.strict_growth
#print axioms Tower.no_self_extension
#print axioms Tower.arrow_placement
#print axioms Tower.no_settling
#print axioms Tower.underdetermined_core
#print axioms Tower.underdetermined_at_fundamental
#print axioms Tower.ext2_at_p
#print axioms Tower.ext2_at_q
#print axioms Tower.ext2_off
#print axioms Tower.underdetermined_at_two
#print axioms Tower.underdetermined_at_two_valued
#print axioms Tower.underdetermination_needs_two_points
#print axioms Tower.first_emanation_of
#print axioms Tower.first_emanation
#print axioms Tower.first_emanation_grows
#print axioms Tower.first_emanations_differ
#print axioms Tower.first_step_underdetermined
#print axioms Tower.tower_package

end Tower
