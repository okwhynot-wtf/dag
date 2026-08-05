import Target
import Classical
import Orthoset

/-!
# Axiom — the additional hypothesis, and what it buys

States the additional hypothesis proposed as the minimal one that yields
Hilbert-space structure, and derives the target from it.

Read the word "together with the spine" carefully. The spine appears in this
module only **negatively**: `spine_is_not_orthoframe` says the spine's own
orthogonality relation does not satisfy the hypothesis. The positive direction
uses the hypothesis and the imported theorems alone; the spine contributes
nothing to it. What the spine determines is the *starting position* the
hypothesis has to repair, which is the subject of `SpineFacts` and `Classical`.

Two formulations are given. The **orthoset** formulation (`Orthoframe`) is the
primary one: it is stated in a signature the spine already uses — one binary
relation, no scalars, no order, no algebra. The **lattice** formulation
(`Superposed`) is a parallel statement in Piron's vocabulary, kept because the
imported representation theorems are stated there. The two are *not* proved
equivalent, and `Superposed` is strictly richer: it carries a full `Ortho`
structure, completeness, atomicity and the covering law, none of which appear
in `Orthoframe`. No theorem transfers between them.

## The hypothesis, in one sentence

*Orthogonality is not the step relation of a single act: there are four
mutually exclusive states, every pair of exclusive states has a third state in
the subspace they span, the closure lattice is orthomodular, and some infinite
orthogonal family has all its members of the same size.*

## What is proved here, and what is imported

**Proved in Lean, axiom-free** — the negative results only:

* the spine's act-induced orthoset is not an `Orthoframe`
  (`spine_is_not_orthoframe`);
* the classical orthoset on a carrier with two distinct points is not an
  `Orthoframe` (`discrete_no_superposition`, `discrete_is_not_orthoframe`);
* the classical bit does not satisfy the lattice form
  (`superposition_carries_the_content`).

**Depending on declared axioms** — everything positive, and one negative
result that mentions `Superposed` and so inherits its field types:

* `hilbert_of_orthoframe`, `hilbert_of_superposed` — the assemblies;
* `rank_of_ladder`, `irreducible_of_superposed` — the two discharges;
* `bit_is_not_superposed`.

Run `#print axioms` at the foot of this file, or read the `formal/quantum/`
table in `formal/AXIOMS.md`, for the exact footprint of each. Imported as named
axioms: `Target.piron`, `Target.soler`, `piron_soler_orthoset`,
`superposition_iff_irreducible`, together with the opaque predicates
`Target.IsGeneralizedHilbert`, `Target.HasOrthonormalSequence`,
`Target.IsHilbertLattice` and `IsHilbertOrthoset`.

## In what sense this is minimal — and in what sense it is not

The honest claim is **not** that one Lean clause suffices, and it is not that
every clause has been shown necessary. It is:

1. **Rank is not a clause at all.** `HasNormedOrthogonalSequence` has an
   infinite pairwise-orthogonal family as its first conjunct, so
   `rank_of_normed` reads off rank of every order. `Orthoframe` therefore has
   four fields, of which three are substantive: irredundancy, superposition,
   orthomodularity, same-size.
2. **Superposition cannot be dropped**, and this is now shown properly.
   `Witness.superposition_independent_of_the_rest` exhibits a model — the
   classical orthoset on `Nat` — satisfying irredundancy, orthomodularity, the
   normed family and rank of every order, while failing superposition. An
   earlier version cited `Ortho.superposition_is_independent` for this, which
   does not do the job: the classical bit fails rank too, so it cannot show
   superposition underivable from the rest.
3. **Irredundancy cannot be dropped.** Without it the remaining clauses admit a
   classical model: duplicate every point of `Witness.discrete Nat`, and the
   duplicate of `x` lies in the double polar of any orthogonal pair containing
   `x`, so superposition holds for free. That model is described but not
   formalised here.
4. **Orthomodularity and same-size have no witness in this package.** For
   same-size the literature supplies one (Keller 1980, cited in `Target`). For
   orthomodularity none is offered, and its presence is a hypothesis of
   convenience matching the imported theorem.
5. `rank_of_ladder` and `irreducible_of_superposed` are *discharges, not
   savings*. `rank_of_ladder` derives `HasRankAtLeast` from the `rung` fields,
   which are themselves assumed; `irreducible_of_superposed` is an application
   of a cited axiom.

What remains irreducibly plural is `irredundant ∧ superposition ∧ orthomodular
∧ same-size`. This module does not claim that conjunction can be compressed to
a single clause; it establishes that two of its four clauses cannot be dropped,
and leaves the other two open.
-/
namespace Quantum.Axiom

open Quantum.Ortho
open Quantum.Target
open Quantum.Orthoset

variable {P X : Type}

/-! ## Orthoset-level clauses -/

/-- **Superposition, orthoset form.** Two exclusive states span a subspace
    containing a third state distinct from both. The span is the double polar
    of the pair, so no lattice operations are needed to say this.

    Note the quantifier: this is stated only for **orthogonal** pairs, whereas
    Piron's superposition principle is stated for any two distinct atoms. The
    restriction is formally weaker. It is expected to be harmless in the
    presence of the other clauses — given two distinct atoms one can replace
    one of them by its component orthogonal to the other without changing the
    span — but that reduction is not proved here, and the weaker form is what
    `piron_soler_orthoset` consumes. -/
def SuperpositionO (O : Orthoset X) : Prop :=
  ∀ x y, O.perp x y →
    ∃ z, z ≠ x ∧ z ≠ y ∧
      polar O (polar O (fun w => w = x ∨ w = y)) z

/-- **Orthomodularity, orthoset form.** If `S` is a closed subspace of the
    closed subspace `T`, then `T` is spanned by `S` together with the part of
    `T` orthogonal to `S`. -/
def OrthomodularO (O : Orthoset X) : Prop :=
  ∀ S T : X → Prop, Closed O S → Closed O T → (∀ x, S x → T x) →
    ∀ x, T x →
      polar O (polar O (fun w => S w ∨ (T w ∧ polar O S w))) x

/-! ## The hypothesis -/

/-- **The additional hypothesis, orthoset form.**

    *Consistency.* The hypothesis is satisfiable, so the derivation below is not
    vacuous: take `X` to be the rays of a separable complex Hilbert space with
    `perp` the usual orthogonality. Rank holds; the double polar of an
    orthogonal pair is the ray set of their two-dimensional span, which
    contains the ray of their sum, giving superposition; orthomodularity is the
    Hilbert decomposition `T = S ⊕ (T ∩ S^⊥)`; and for an orthonormal basis the
    unitary transposing two members fixes the rest pointwise, giving the
    same-size condition. That model cannot be built in Lean core — there is no
    `ℂ` here — so this is an informal consistency note, not a theorem. -/
structure Orthoframe (X : Type) where
  /-- The orthogonality space of states. -/
  O : Orthoset X
  /-- Distinct states are separated by orthogonality. Without this the
      remaining clauses are satisfied by a classical model — see
      `Orthoset.Irredundant`. -/
  irredundant : Irredundant O
  /-- Every pair of exclusive states spans a subspace with a third state. -/
  superposition : SuperpositionO O
  /-- The closure lattice is orthomodular. -/
  orthomodular : OrthomodularO O
  /-- Some infinite orthogonal family has all members of the same size. This
      subsumes rank: its first conjunct is an infinite pairwise-orthogonal
      family, so `rank_of_normed` reads off `HasRankN O n` for every `n`, and
      rank is not a separate clause. -/
  normed : HasNormedOrthogonalSequence O

/-- `O` is the orthogonality space of the rays of a real, complex or
    quaternionic Hilbert space. Content fixed by the citations below. -/
axiom IsHilbertOrthoset (O : Orthoset X) : Prop

/-- **The orthoset route, imported.** An irredundant orthogonality space of
    rank at least four whose closure lattice is orthomodular and which
    satisfies the superposition principle is the ray space of a Hermitian space
    over a `*`-division ring; if in addition an infinite orthogonal family has
    constant norm, the ring is `ℝ`, `ℂ` or `ℍ`.

    Attribution, stated carefully. The lattice-level results are Piron 1964 and
    Solèr 1995 (see `Target`). Transposing them to a condition on a symmetric
    irreflexive relation is the orthogonality-space tradition — Dacey,
    Foulis–Randall, and in recent form T. Vetterlein, *Orthogonality spaces of
    finite rank and the complex Hilbert spaces*, J. Geom. 110 (2019). The
    automorphism form of Solèr's condition used here is closest to the symmetry
    variants surveyed in Holland (1995) §5 and to R. Mayet's work on
    ortholattice automorphisms, not to Solèr's own statement. **No single cited
    paper states this axiom in this form**; it is assembled, and the assembly
    is not verified here.

    Two caveats on the correspondence between this declaration and the cited
    results. First, the covering law appears in Piron's hypotheses and not in
    this axiom's; dropping it is not a bookkeeping simplification, and
    superposition is not known to supply it. Second, `HasNormedOrthogonalSequence`
    is a surrogate for Solèr's hypothesis and is not shown equivalent to it —
    see `Orthoset.SameSize`. This declaration is therefore *stronger* than the
    literature it names, and should be read as the assumption actually being
    made rather than as a faithful transcription. Not proved here. -/
axiom piron_soler_orthoset (O : Orthoset X) :
    Irredundant O → HasRankN O 4 → SuperpositionO O → OrthomodularO O →
    HasNormedOrthogonalSequence O → IsHilbertOrthoset O

/-- Rank is not a separate assumption: the infinite orthogonal family inside
    `HasNormedOrthogonalSequence` already supplies `n` mutually orthogonal
    states for every `n`. -/
theorem rank_of_normed (O : Orthoset X) (h : HasNormedOrthogonalSequence O)
    (n : Nat) : HasRankN O n := by
  obtain ⟨e, hperp, _⟩ := h
  exact ⟨e, fun i j _ _ hij => hperp i j hij⟩

/-- **The derivation, orthoset form.** -/
theorem hilbert_of_orthoframe (F : Orthoframe X) : IsHilbertOrthoset F.O :=
  piron_soler_orthoset F.O F.irredundant (rank_of_normed F.O F.normed 4)
    F.superposition F.orthomodular F.normed

/-! ## The hypothesis is not idle

Both ways of reading the spine fail the hypothesis, and they fail different
clauses. That is the content of the answer: there is no single clause to add,
because the two natural readings are deficient in two different directions.
-/

/-- **The spine's own orthoset fails.** Orthogonality induced by one act has no
    orthogonal triple, so it cannot carry an infinite orthogonal family. The
    proof runs through the `normed` field, so what it directly contradicts is
    the same-size clause; the `rank` clause fails for the same underlying
    reason (`Orthoset.act_orthoset_has_no_triple`) but is not the clause used
    here.

    The hypothesis is stated as a pointwise equivalence of relations rather
    than an equality of `Orthoset` structures, so that applying it needs
    neither `propext` nor `funext`. -/
theorem spine_is_not_orthoframe {α : Type} (act : α → α) (hl : Orbit.Live act)
    (F : Orthoframe α) (h : ∀ x y, F.O.perp x y ↔ Orbit.Step act x y) :
    False := by
  obtain ⟨e, hperp, _⟩ := F.normed
  have h01 : Orbit.Step act (e 0) (e 1) :=
    (h _ _).mp (hperp 0 1 (by intro hc; exact Nat.noConfusion hc))
  have h02 : Orbit.Step act (e 0) (e 2) :=
    (h _ _).mp (hperp 0 2 (by intro hc; exact Nat.noConfusion hc))
  have h12 : Orbit.Step act (e 1) (e 2) :=
    (h _ _).mp (hperp 1 2 (by intro hc; exact Nat.noConfusion (Nat.succ.inj hc)))
  have heq : e 1 = e 2 := orthogonal_partner_unique act (e 0) (e 1) (e 2) h01 h02
  rw [heq] at h12
  exact hl (e 2) h12.symm

/-- **The classical orthoset fails the superposition clause.** Under
    distinguishability the closure of a pair is the pair, so no third state
    lies in their span — however large the carrier, and hence however large the
    rank. -/
theorem discrete_no_superposition (hX : ∃ x y : X, x ≠ y) :
    ¬ SuperpositionO (discrete X) := by
  intro hsup
  obtain ⟨x, y, hxy⟩ := hX
  obtain ⟨z, _hzx, _hzy, hz⟩ := hsup x y hxy
  have hzpolar : polar (discrete X) (fun w => w = x ∨ w = y) z := by
    intro w hw
    rcases hw with rfl | rfl
    · exact _hzx
    · exact _hzy
  exact (hz z hzpolar) rfl

/-- The classical orthoset is not an `Orthoframe`, on any carrier with two
    distinct points. Stated pointwise, as for `spine_is_not_orthoframe`. -/
theorem discrete_is_not_orthoframe (hX : ∃ x y : X, x ≠ y) (F : Orthoframe X)
    (h : ∀ x y, F.O.perp x y ↔ x ≠ y) : False := by
  obtain ⟨x, y, hxy⟩ := hX
  obtain ⟨z, hzx, hzy, hz⟩ := F.superposition x y ((h x y).mpr hxy)
  exact (h z z).mp
    (hz z (fun w hw => (h z w).mpr (by
      rcases hw with rfl | rfl
      · exact hzx
      · exact hzy))) rfl

/-! ## Lattice form, for the imported theorems -/

/-- **Piron's superposition/irreducibility equivalence, imported.** In a
    complete, atomistic, orthomodular ortholattice **satisfying the covering
    law** — an AC lattice — the superposition principle holds exactly when the
    lattice is irreducible, i.e. exactly when the system has no nontrivial
    classical part. Piron 1964; E. Beltrametti and G. Cassinelli, *The Logic of
    Quantum Mechanics*, Addison-Wesley 1981, Ch. 10 (AC lattices). Not proved
    here.

    The covering-law hypothesis is **not** decorative and was missing from an
    earlier version of this declaration. Without it the statement is false: the
    horizontal sum of two copies of the eight-element Boolean algebra is
    complete, atomistic, orthomodular and irreducible, yet two atoms in the same
    block join to an element covering only themselves, so superposition fails.
    A false declared axiom would make `False` derivable, since every symbol in
    this statement is fully defined in Lean and none is opaque. -/
axiom superposition_iff_irreducible (L : Ortho P) :
    Complete L → Atomistic L → Orthomodular L → CoveringLaw L →
    (Superposition L ↔ Irreducible L)

/-- The same hypothesis in Piron's vocabulary, with the spine's ladder present
    as a strictly ascending chain. -/
structure Superposed (P : Type) where
  /-- The proposition lattice. -/
  L : Ortho P
  /-- Every family of propositions has a least upper bound. -/
  complete : Complete L
  /-- Every nonzero proposition dominates an atom. -/
  atomistic : Atomistic L
  /-- Piron's compatibility law. -/
  orthomodular : Orthomodular L
  /-- Piron's covering law. -/
  covering : CoveringLaw L
  /-- Two distinct sharp alternatives always admit a third below their join. -/
  superposition : Superposition L
  /-- Solèr's condition on the coordinatising form. -/
  orthonormal : HasOrthonormalSequence L
  /-- Image of the spine's ladder: the proposition reached by rung `i`. -/
  rung : Nat → P
  /-- The ladder ascends. -/
  rung_mono : ∀ i, L.le (rung i) (rung (i + 1))
  /-- Each rung is strictly new — the spine's `Ladder.none_is_new`. -/
  rung_strict : ∀ i, rung i ≠ rung (i + 1)

/-- Rank of every finite order, read off the `rung` fields. This *discharges*
    Piron's rank-4 hypothesis rather than saving it: `rung`, `rung_mono` and
    `rung_strict` are themselves assumed, and are the shape the spine's ladder
    would have if it were embedded. Nothing in this proof mentions
    `Ladder.Level`. -/
theorem rank_of_ladder (S : Superposed P) (n : Nat) : HasRankAtLeast S.L n :=
  ⟨S.rung, S.rung_mono, fun i _ => S.rung_strict i⟩

/-- Irreducibility, obtained from superposition by the cited equivalence. This
    is an application of `superposition_iff_irreducible`, which is a declared
    axiom, not a derivation. -/
theorem irreducible_of_superposed (S : Superposed P) : Irreducible S.L :=
  (superposition_iff_irreducible S.L S.complete S.atomistic
    S.orthomodular S.covering).mp S.superposition

/-- **The derivation, lattice form.** -/
theorem hilbert_of_superposed (S : Superposed P) : IsHilbertLattice S.L :=
  piron_soler S.L S.complete S.atomistic S.orthomodular S.covering
    (irreducible_of_superposed S) (rank_of_ladder S 4) S.orthonormal

/-- The spine's own proposition structure does not satisfy the hypothesis: the
    classical bit has no superposition. Cf. `Classical.spine_is_classical`. -/
theorem bit_is_not_superposed (S : Superposed Bit) : S.L ≠ bit := by
  intro h
  exact bit_no_superposition (h ▸ S.superposition)

/-! ## Summary -/

/-- The independence bound, gathered: every clause except superposition is
    satisfied by a classical system, so no subset of the clauses that omits
    superposition can force Hilbert-space structure. -/
theorem superposition_carries_the_content :
    Orthomodular bit ∧ Atomistic bit ∧ CoveringLaw bit ∧ ¬ Superposition bit :=
  ⟨bit_orthomodular, bit_atomistic, bit_covering_law, bit_no_superposition⟩

#print axioms Quantum.Axiom.hilbert_of_orthoframe
#print axioms Quantum.Axiom.spine_is_not_orthoframe
#print axioms Quantum.Axiom.discrete_no_superposition
#print axioms Quantum.Axiom.discrete_is_not_orthoframe
#print axioms Quantum.Axiom.rank_of_ladder
#print axioms Quantum.Axiom.irreducible_of_superposed
#print axioms Quantum.Axiom.hilbert_of_superposed
#print axioms Quantum.Axiom.bit_is_not_superposed
#print axioms Quantum.Axiom.superposition_carries_the_content

end Quantum.Axiom
