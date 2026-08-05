import Canon
import Ortho

/-!
# Orthoset — the spine's orthogonality space, and the rank it cannot have

The spine supplies an orthogonality space for free. `Orbit.Step act x y` is
`y = act x`; `Orbit.SymmetricStep` makes it symmetric and `Orbit.Live` makes it
irreflexive, which is exactly the definition of an orthogonality space
(orthoset). No axiom is needed for this — it is already there.

What the spine cannot supply is **rank**. Because `Step` is the graph of a
function, two states orthogonal to a common state coincide
(`orthogonal_partner_unique`), so no three states are pairwise orthogonal
(`act_orthoset_has_no_triple`). That is an *upper* bound on rank. It holds
without any hypothesis on `act` beyond what `ofAct` already requires, and in
particular it does not come from `TwoCycle.Generated`; no matching lower bound
is proved here, so "rank at most two" is the claim, not "rank exactly two".

Every representation theorem in this area needs rank at least three (orthoset
routes), four (Piron), or countably infinite (Solèr). So rank is one thing the
act-induced orthogonality forbids, and giving it up is a necessary relaxation.
It is *necessary*, not sufficient — see `Axiom.lean` for the sufficient bundle.

## Which orthogonality relation, and why rank alone is not enough

`Orbit.Step act` is not the only symmetric irreflexive relation available on
the spine's carriers. The other natural candidate is distinguishability,
`x ≠ y`. On any carrier admitting an injective `Nat`-indexed family — the
colimit does, by `Limit.stage_inj` — that relation has rank `n` for every `n`
(`discrete_rank_of_injective`). So the spine is **not** short of rank under
every reading.

That second relation is no help, for a different reason: under it the closure
of a set adds nothing, so no third state lies in the span of two, and
superposition fails
(`Axiom.discrete_no_superposition`). `triangle` below is the three-point case;
it witnesses that rank-3 orthosets exist, not that rank-3 orthosets are
quantum. That the closure lattice of `discrete` is *Boolean* is the usual
description of this situation but is not proved here, and nothing downstream
uses it.

The honest summary is two-pronged. Under the act-induced relation the spine has
rank at most two and cannot reach Piron. Under distinguishability it has ample
rank but no superposition. Neither reading is quantum, and an added axiom has
to fix whichever prong it addresses.

* **Vocabulary** (`Orthoset`, `Orthoset.ofAct`, `HasRank3`, `HasRankN`).
* **The spine's orthoset** (`spineOrthoset`): symmetric and irreflexive from
  `SymmetricStep` and `Live` alone — generation is not used.
* **The cap** (`orthogonal_partner_unique`, `act_orthoset_has_no_triple`): no
  orthogonal triple, forced by functionality of the act.
* **The relaxation** (`rank3_not_from_one_act`): a rank-3 orthoset exists, and
  its orthogonality is not the step relation of any single act.
-/
namespace Quantum.Orthoset

/-! ## Orthogonality spaces -/

/-- An orthogonality space: a symmetric, irreflexive binary relation. Points
    are states; `perp x y` says they are distinguishable with certainty. -/
structure Orthoset (P : Type) where
  /-- The orthogonality relation. -/
  perp : P → P → Prop
  /-- Orthogonality is symmetric. -/
  symm : ∀ x y, perp x y → perp y x
  /-- No state is orthogonal to itself. -/
  irrefl : ∀ x, ¬ perp x x

/-- Three pairwise orthogonal states. The first rank condition beyond the
    spine's reach. -/
def HasRank3 {P : Type} (O : Orthoset P) : Prop :=
  ∃ x y z : P, O.perp x y ∧ O.perp y z ∧ O.perp x z

/-- A `Nat`-indexed family whose first `n` members are pairwise orthogonal.
    Injectivity of the indexing is not imposed; it follows on the relevant
    range, since `perp` is irreflexive and orthogonal members are distinct. -/
def HasRankN {P : Type} (O : Orthoset P) (n : Nat) : Prop :=
  ∃ e : Nat → P, ∀ i j, i < n → j < n → i ≠ j → O.perp (e i) (e j)

/-- **Irredundancy.** Distinct states are separated by orthogonality: some
    state is orthogonal to one and not the other. Equivalently, no two states
    have the same orthocomplement.

    This is not optional bookkeeping. Without it, duplicating every point of an
    orthoset — replacing each `x` by two copies orthogonal to exactly the same
    things — produces a space in which the double polar of an orthogonal pair
    contains the duplicates, so "superposition" holds for free and carries no
    information. Every representation theorem in this area assumes it, usually
    silently, by working with rays rather than vectors. -/
def Irredundant {P : Type} (O : Orthoset P) : Prop :=
  ∀ x y : P, x ≠ y →
    ∃ z, (O.perp z x ∧ ¬ O.perp z y) ∨ (O.perp z y ∧ ¬ O.perp z x)

/-! ## The spine's orthoset -/

/-- The orthogonality space of a symmetric-step live act. Note the hypotheses:
    `SymmetricStep` and `Live` only. `TwoCycle.Generated` is **not** used, so
    this construction is available on any live involution, not just on a
    fundamental. -/
def ofAct {α : Type} (act : α → α) (hs : Orbit.SymmetricStep act)
    (hl : Orbit.Live act) : Orthoset α where
  perp := Orbit.Step act
  symm := fun x y h => hs x y h
  irrefl := fun x h => hl x h.symm

/-- The fundamental's own orthogonality space. -/
def spineOrthoset {α : Type} (act : α → α) (h : Canon.IsFundamental act) :
    Orthoset α :=
  ofAct act h.unoriented h.live

/-! ## The rank cap -/

/-- **No state has two distinct orthogonal partners.** `Orbit.Step act x y` is
    `y = act x`, the graph of a function, so two states orthogonal to the same
    state coincide. An upper bound only — that `act x` *is* orthogonal to `x`
    is `Orbit.Live`, and is not part of this statement. No hypothesis on `act`
    is needed here at all. -/
theorem orthogonal_partner_unique {α : Type} (act : α → α) (x y z : α)
    (hy : Orbit.Step act x y) (hz : Orbit.Step act x z) : y = z :=
  hy.trans hz.symm

/-- **The spine's orthoset has no orthogonal triple.** Rank is capped above by
    two, and the cap comes from orthogonality being induced by a single act —
    `TwoCycle.Generated` is not used. Piron needs rank at least four and Solèr
    countably infinite rank, so neither is available *for this choice of
    orthogonality relation*. That is a statement about `ofAct`, not a claim
    about every possible extension of the spine; `discrete_rank_of_injective`
    shows a different choice of relation has unbounded rank. -/
theorem act_orthoset_has_no_triple {α : Type} (act : α → α)
    (hs : Orbit.SymmetricStep act) (hl : Orbit.Live act) :
    ¬ HasRank3 (ofAct act hs hl) := by
  intro ⟨x, y, z, hxy, hyz, hxz⟩
  have hyz' : y = z := orthogonal_partner_unique act x y z hxy hxz
  exact (ofAct act hs hl).irrefl z (hyz' ▸ hyz)

/-- The cap is not an artefact of the fundamental: it holds for every live
    involution, generated or not. -/
theorem no_triple_without_generation {α : Type} (act : α → α)
    (_hs : Orbit.SymmetricStep act) (hl : Orbit.Live act)
    (x y z : α) (hxy : Orbit.Step act x y) (hxz : Orbit.Step act x z) :
    ¬ Orbit.Step act y z := by
  intro hyz
  have hyz' : y = z := orthogonal_partner_unique act x y z hxy hxz
  rw [hyz'] at hyz
  exact hl z hyz.symm

/-! ## The polarity that generates the lattice

An orthogonality space carries a Galois connection: the polar of a set of
states is the set orthogonal to all of them, and the closed sets — those equal
to their double polar — are the propositions. Piron's lattice is this lattice
of closed sets.

The three Galois facts below are elementary and are proved here. That the
closed sets then form a *complete ortholattice*, i.e. that they instantiate
`Ortho.Ortho`, is standard but is **neither proved here nor imported** — there
is no `Ortho` instance built from an `Orthoset` anywhere in this package. The
orthoset-level clauses in `Axiom.lean` are therefore stated directly on
`polar`/`Closed` rather than routed through a lattice, and
`Axiom.piron_soler_orthoset` consumes them in that form.
-/

/-- The polar of a set of states: everything orthogonal to all of it. -/
def polar {P : Type} (O : Orthoset P) (S : P → Prop) : P → Prop :=
  fun x => ∀ y, S y → O.perp x y

/-- A set is closed when it contains its double polar (hence equals it, given
    `subset_polar_polar`). Closed sets are the propositions. -/
def Closed {P : Type} (O : Orthoset P) (S : P → Prop) : Prop :=
  ∀ x, polar O (polar O S) x → S x

/-- Every set is contained in its double polar. -/
theorem subset_polar_polar {P : Type} (O : Orthoset P) (S : P → Prop) (x : P)
    (hx : S x) : polar O (polar O S) x :=
  fun _ hy => O.symm _ x (hy x hx)

/-- The polar is order-reversing. -/
theorem polar_antitone {P : Type} (O : Orthoset P) (S T : P → Prop)
    (h : ∀ x, S x → T x) (x : P) (hx : polar O T x) : polar O S x :=
  fun y hy => hx y (h y hy)

/-- Triple polar collapses to single polar: the closure operator `polar ∘ polar`
    is idempotent. Together with extensivity and antitonicity this is the
    standard closure-operator package; the lattice structure it usually
    supports is not built here. -/
theorem polar_polar_polar {P : Type} (O : Orthoset P) (S : P → Prop) (x : P) :
    polar O (polar O (polar O S)) x ↔ polar O S x := by
  constructor
  · intro h
    exact polar_antitone O S (polar O (polar O S)) (subset_polar_polar O S) x h
  · exact subset_polar_polar O (polar O S) x

/-- Polars are always closed. -/
theorem polar_closed {P : Type} (O : Orthoset P) (S : P → Prop) :
    Closed O (polar O S) :=
  fun x h => (polar_polar_polar O S x).mp h

/-! ## Equal size without a form

Solèr's hypothesis is that a Hermitian form take the *same value* on each
member of an infinite orthogonal sequence. Stated that way it needs the form,
which is not available before the representation theorem has been applied. The
standard way round is to replace it by a condition on symmetries: two
directions have the same size exactly when a symmetry exchanges them and
disturbs nothing orthogonal to both. That is stated below purely in the
orthoset vocabulary — no scalars, no form, no order.
-/

/-- A symmetry of an orthogonality space: a bijection preserving and
    reflecting orthogonality. -/
structure Auto {P : Type} (O : Orthoset P) where
  /-- The underlying map. -/
  map : P → P
  /-- Its inverse. -/
  inv : P → P
  left_inv : ∀ x, inv (map x) = x
  right_inv : ∀ x, map (inv x) = x
  /-- Orthogonality is preserved and reflected. -/
  perp_iff : ∀ x y, O.perp (map x) (map y) ↔ O.perp x y

/-- The identity symmetry, so `Auto` is never empty. -/
def Auto.id {P : Type} (O : Orthoset P) : Auto O where
  map := fun x => x
  inv := fun x => x
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl
  perp_iff := fun _ _ => Iff.rfl

/-- `x` and `y` have the same size: some symmetry carries `x` to `y` and fixes
    everything orthogonal to both. This is a form-free **surrogate** for
    `⟪x,x⟫ = ⟪y,y⟫`, not a definition of it, and only one direction is
    straightforward.

    Given a Hermitian space, two orthogonal vectors of equal norm are exchanged
    by an isometry fixing their common orthocomplement, so equal norm gives the
    symmetry. The converse does **not** follow from this definition alone: an
    automorphism of an orthogonality space need only preserve orthogonality,
    and such a map may be induced by a similarity — a semilinear map rescaling
    the form — rather than by an isometry, in which case it carries no
    information about norms. Closing that gap is a Wigner/Uhlhorn-type step and
    is neither proved nor assumed here.

    So `HasNormedOrthogonalSequence` is not established to be equivalent to
    Solèr's hypothesis. It is the condition actually fed to
    `Axiom.piron_soler_orthoset`, and the strength of that imported axiom
    should be read accordingly. -/
def SameSize {P : Type} (O : Orthoset P) (x y : P) : Prop :=
  ∃ g : Auto O, g.map x = y ∧ ∀ z, O.perp z x → O.perp z y → g.map z = z

/-- Every point has the same size as itself, via the identity. -/
theorem sameSize_refl {P : Type} (O : Orthoset P) (x : P) : SameSize O x x :=
  ⟨Auto.id O, rfl, fun _ _ _ => rfl⟩

/-- **Solèr's condition, form-free.** An infinite pairwise-orthogonal family
    all of whose members have the same size. -/
def HasNormedOrthogonalSequence {P : Type} (O : Orthoset P) : Prop :=
  ∃ e : Nat → P,
    (∀ i j, i ≠ j → O.perp (e i) (e j)) ∧ (∀ i j, SameSize O (e i) (e j))

/-- The condition implies the plain infinite orthogonal family, so it is at
    least as strong as bare infinite rank. -/
theorem normed_gives_orthogonal {P : Type} (O : Orthoset P)
    (h : HasNormedOrthogonalSequence O) :
    ∃ e : Nat → P, ∀ i j, i ≠ j → O.perp (e i) (e j) := by
  obtain ⟨e, hperp, _⟩ := h
  exact ⟨e, hperp⟩

/-- The act-induced orthoset cannot carry a normed orthogonal sequence: it
    cannot even carry an orthogonal triple. -/
theorem act_has_no_normed_sequence {α : Type} (act : α → α)
    (hs : Orbit.SymmetricStep act) (hl : Orbit.Live act) :
    ¬ HasNormedOrthogonalSequence (ofAct act hs hl) := by
  intro h
  obtain ⟨e, hperp, _⟩ := h
  exact act_orthoset_has_no_triple act hs hl
    ⟨e 0, e 1, e 2,
     hperp 0 1 (by intro hc; exact Nat.noConfusion hc),
     hperp 1 2 (by intro hc; exact Nat.noConfusion (Nat.succ.inj hc)),
     hperp 0 2 (by intro hc; exact Nat.noConfusion hc)⟩

/-! ## What a rank-3 orthoset costs -/

/-- A three-point carrier. -/
inductive Three where
  | a | b | c

/-- The **classical** orthogonality space on any carrier: distinguishability,
    i.e. the complete graph. Rank is cheap here — see
    `discrete_rank_of_injective`. Its closure operator is trivial
    (see `Axiom.discrete_no_superposition`), which is what defeats superposition; the
    further description "its closed sets are all subsets, so it is Boolean" is
    the usual account but is not proved in this package. -/
def discrete (X : Type) : Orthoset X where
  perp := fun x y => x ≠ y
  symm := fun _ _ h => Ne.symm h
  irrefl := fun _ h => h rfl

/-- The classical orthoset on three points. Rank-3 orthosets exist; this one is
    classical, so it witnesses that the rank condition is consistent, not that
    rank suffices for quantum structure. -/
abbrev triangle : Orthoset Three := discrete Three

theorem triangle_has_rank3 : HasRank3 triangle :=
  ⟨Three.a, Three.b, Three.c,
   fun h => Three.noConfusion h,
   fun h => Three.noConfusion h,
   fun h => Three.noConfusion h⟩

/-- **The classical orthoset has unbounded rank.** Any injective `Nat`-indexed
    family of states is pairwise orthogonal under distinguishability, so
    `discrete X` has rank `n` for every `n`. Applied to
    `Limit.LevelOmega.stage` (injective by `Limit.stage_inj`), this says the
    spine is not short of rank under the distinguishability reading — the
    reason that reading fails is superposition, not rank. -/
theorem discrete_rank_of_injective {X : Type} (e : Nat → X)
    (hinj : ∀ i j, e i = e j → i = j) (n : Nat) : HasRankN (discrete X) n :=
  ⟨e, fun i j _ _ hij hc => hij (hinj i j hc)⟩

/-- **The cost of rank.** A rank-3 orthogonality space cannot be the step
    relation of any single act: functionality of the act is exactly what caps
    rank at two. So the minimal relaxation is not a weakening of one of the
    spine's clauses about `act` — it is giving up that orthogonality is
    generated by one act at all. -/
theorem rank3_not_from_one_act {P : Type} (O : Orthoset P) (h : HasRank3 O)
    (act : P → P) (hrepr : ∀ x y, O.perp x y ↔ Orbit.Step act x y) : False := by
  obtain ⟨x, y, z, hxy, hyz, hxz⟩ := h
  have hy : Orbit.Step act x y := (hrepr x y).mp hxy
  have hz : Orbit.Step act x z := (hrepr x z).mp hxz
  have : y = z := orthogonal_partner_unique act x y z hy hz
  exact O.irrefl z (this ▸ hyz)

/-! ## Summary -/

/-- **The rank obstruction.** The spine's orthogonality space is symmetric and
    irreflexive without any added hypothesis, and its rank is exactly two
    without any added hypothesis. Rank three is available in general
    (`triangle`) but never from a single act. -/
theorem rank_obstruction :
    (∀ {α : Type} (act : α → α) (hs : Orbit.SymmetricStep act)
      (hl : Orbit.Live act), ¬ HasRank3 (ofAct act hs hl)) ∧
    HasRank3 triangle ∧
    (∀ {P : Type} (O : Orthoset P), HasRank3 O → ∀ act : P → P,
      (∀ x y, O.perp x y ↔ Orbit.Step act x y) → False) :=
  ⟨fun act hs hl => act_orthoset_has_no_triple act hs hl,
   triangle_has_rank3,
   fun O h act hrepr => rank3_not_from_one_act O h act hrepr⟩

#print axioms Quantum.Orthoset.ofAct
#print axioms Quantum.Orthoset.orthogonal_partner_unique
#print axioms Quantum.Orthoset.act_orthoset_has_no_triple
#print axioms Quantum.Orthoset.no_triple_without_generation
#print axioms Quantum.Orthoset.subset_polar_polar
#print axioms Quantum.Orthoset.polar_antitone
#print axioms Quantum.Orthoset.polar_polar_polar
#print axioms Quantum.Orthoset.polar_closed
#print axioms Quantum.Orthoset.sameSize_refl
#print axioms Quantum.Orthoset.normed_gives_orthogonal
#print axioms Quantum.Orthoset.act_has_no_normed_sequence
#print axioms Quantum.Orthoset.triangle_has_rank3
#print axioms Quantum.Orthoset.rank3_not_from_one_act
#print axioms Quantum.Orthoset.rank_obstruction

end Quantum.Orthoset
