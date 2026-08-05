import Ortho

/-!
# Target — what "Hilbert-space structure" means, and what is imported to get it

Fixes the target of the reconstruction and imports the two representation
theorems that reach it. **The representation theorems are not proved here.**
They are declared as named Lean `axiom`s so that `#print axioms` on any
downstream result names them explicitly: the audit then shows exactly which
part of a derivation is Lean-checked and which part is a citation.

Imported, with citations:

* `piron` — C. Piron, *Axiomatique quantique*, Helv. Phys. Acta 37 (1964)
  439–468. A complete, atomistic, orthomodular ortholattice satisfying the
  covering law, irreducible and of rank at least 4, is isomorphic to the
  lattice of `⊥`-closed subspaces of a Hermitian space over a `*`-division
  ring ("generalized Hilbert space").
* `soler` — M. P. Solèr, *Characterization of Hilbert spaces by orthomodular
  spaces*, Comm. Algebra 23 (1995) 219–243. A generalized Hilbert space
  containing an infinite orthonormal sequence has scalars `ℝ`, `ℂ` or `ℍ` and
  is the corresponding Hilbert space. Survey: S. S. Holland Jr., Bull. AMS 32
  (1995) 205–234.

## Why Piron alone is not enough

Piron's conclusion is a Hermitian space over *some* `*`-division ring, and that
is strictly weaker than a Hilbert space: the hypotheses do not pin the ring.
That is precisely the gap Solèr's theorem was introduced to close, and it is
standard — see Holland's survey, cited below, §2.

Rational examples are the obvious illustration, but they need care: the
subspace lattice of a rational quadratic space is orthomodular only when the
form is anisotropic, so "`L(ℚ⁴)` works" is false as a claim about
four-dimensional rational quadratic spaces in general. Nothing below depends on
such an example; the documented separation to rely on is Keller's, in the next
section.

## An honesty note on Solèr's hypothesis

Solèr's condition is that the Hermitian form take **the same value** on each
member of an infinite orthogonal sequence — orthoNORMality. That is a condition
on the form, and it is *not* expressible in the lattice vocabulary of
`Ortho`: H. A. Keller, *Ein nicht-klassischer Hilbertscher Raum*, Math. Z. 172
(1980) 41–49, constructs infinite-dimensional orthomodular spaces over
non-Archimedean fields whose subspace lattices do have infinite orthogonal
sequences of atoms, yet which are not Hilbert spaces. So
`HasInfiniteOrthogonalAtoms` below is **strictly weaker** than Solèr's
hypothesis and is deliberately not used as its premise; the premise
`HasOrthonormalSequence` is left opaque for exactly this reason.
-/
namespace Quantum.Target

open Quantum.Ortho

variable {P : Type}

/-! ## Lattice-level vocabulary -/

/-- Orthogonality: `x` lies below the orthocomplement of `y`. -/
def Orthogonal (L : Ortho P) (x y : P) : Prop := L.le x (L.comp y)

/-- `s` is a least upper bound of the family `S`. -/
def IsLUB (L : Ortho P) (S : P → Prop) (s : P) : Prop :=
  (∀ x, S x → L.le x s) ∧ ∀ t, (∀ x, S x → L.le x t) → L.le s t

/-- Completeness: every family of propositions has a least upper bound. -/
def Complete (L : Ortho P) : Prop :=
  ∀ S : P → Prop, ∃ s, IsLUB L S s

/-- `x` is central when every element splits across `x` and its complement.
    The centre of a proposition lattice is its classical part. -/
def Central (L : Ortho P) (x : P) : Prop :=
  ∀ y, y = L.sup (L.inf y x) (L.inf y (L.comp x))

/-- Irreducibility: the centre is trivial, i.e. the system has no nontrivial
    classical part. This is the lattice form of "one substance". -/
def Irreducible (L : Ortho P) : Prop :=
  ∀ x, Central L x → x = L.bot ∨ x = L.top

/-- A chain `c 0 ≤ c 1 ≤ …` whose first `n` steps are strict. No anchoring at
    `bot` or `top` is imposed; a chain of `n+1` distinct comparable elements
    anywhere in the lattice witnesses height at least `n`, since it extends by
    `bot_le` and `le_top`. -/
def HasRankAtLeast (L : Ortho P) (n : Nat) : Prop :=
  ∃ c : Nat → P, (∀ i, L.le (c i) (c (i + 1))) ∧ ∀ i, i < n → c i ≠ c (i + 1)

/-- An infinite sequence of pairwise orthogonal atoms. Weaker than Solèr's
    condition — see the module docstring. -/
def HasInfiniteOrthogonalAtoms (L : Ortho P) : Prop :=
  ∃ e : Nat → P, (∀ i, IsAtom L (e i)) ∧ ∀ i j, i ≠ j → Orthogonal L (e i) (e j)

/-! ## Imported predicates and theorems

The three predicates below are left without Lean definitions on purpose: their
content is fixed by the cited literature, not by anything provable here.
Declaring them as axioms keeps them visible in every downstream axiom audit.
-/

/-- `L` is the subspace lattice of a Hermitian space over a `*`-division ring
    (Piron's "generalized Hilbert space"). Content fixed by the citation. -/
axiom IsGeneralizedHilbert (L : Ortho P) : Prop

/-- The coordinatising Hermitian space carries an infinite ORTHONORMAL
    sequence: the form takes one and the same value on each member. Content
    fixed by the citation; not expressible in the `Ortho` vocabulary. -/
axiom HasOrthonormalSequence (L : Ortho P) : Prop

/-- `L` is the lattice of closed subspaces of a real, complex or quaternionic
    Hilbert space. The target of the reconstruction. -/
axiom IsHilbertLattice (L : Ortho P) : Prop

/-- **Piron's representation theorem (1964), imported.** -/
axiom piron (L : Ortho P) :
    Complete L → Atomistic L → Orthomodular L → CoveringLaw L →
    Irreducible L → HasRankAtLeast L 4 → IsGeneralizedHilbert L

/-- **Solèr's theorem (1995), imported.** -/
axiom soler (L : Ortho P) :
    IsGeneralizedHilbert L → HasOrthonormalSequence L → IsHilbertLattice L

/-! ## The imported chain, assembled -/

/-- The full imported route: the six Piron hypotheses plus Solèr's orthonormal
    sequence give a real, complex or quaternionic Hilbert lattice. Every step
    here is a citation; the Lean content is only the bookkeeping. -/
theorem piron_soler (L : Ortho P)
    (hc : Complete L) (ha : Atomistic L) (ho : Orthomodular L)
    (hcov : CoveringLaw L) (hirr : Irreducible L) (hr : HasRankAtLeast L 4)
    (hon : HasOrthonormalSequence L) : IsHilbertLattice L :=
  soler L (piron L hc ha ho hcov hirr hr) hon

#print axioms Quantum.Target.piron_soler

end Quantum.Target
