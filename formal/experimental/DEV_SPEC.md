# DEV SPEC — Promote the dynamics arc, reframe the paper, resolve the coupling-flip gauge

Status: ready for implementation. Scope: one Lean promotion pass, one paper
restructure, one bounded research task. The audit discipline governs all
three: Lean 4 pinned toolchain (see `formal/spine/lean-toolchain`), no
Mathlib, no `sorry`, per-declaration `#print axioms`, and `AXIOMS.md`
regenerated via `formal/tools/gen_audit.py` then `formal/tools/audit.sh`
then `VERIFY.sh` after every phase.

Design rule for all prose written under this spec: no em-dashes, and no
antithetical constructions of the form "not X, it's Y"; use compound
sentences that state the positive claim and, where needed, record the
negative claim separately.

---

## Phase 1 — Lean promotion

The experimental package currently holds results that have earned
promotion into the corpus proper. Promotion means: move or re-prove the
declaration in the target package, keep the experimental module as a thin
re-export or delete it, update every lakefile root list and
`gen_audit.py`'s `PACKAGES` table, and confirm footprints after the move.

### 1.1 Promote to the bridge (dynamics layer)

Create `formal/bridge/DynamicsAmbient.lean` from
`formal/experimental/DynamicsAmbient.lean`, namespace
`Bridge.DynamicsAmbient`, with these declarations and their current
footprints preserved:

- `toggle_forces_xor_form` (axiom-free). Any second-order update
  invertible in its previous-layer slot equals `p ^^ G l m r` with
  `G := F false`.
- `collision_of_not_toggling` (propext). Explicit two-history pointwise
  collision on the three-ring when toggling fails.
- `coupling_uniqueness` (axiom-free). Parity, pole invariance, and the
  drawing condition force the coupling into `{xor, !xor}`.
- `survivor_is_wave_coupling` (rfl). The survivor instantiates the ring
  wave coupling.
- `dynamics_ambient_uniqueness` (propext). The package conjunction.

Create `formal/bridge/WaveDynamics.lean` from
`formal/experimental/WaveEquation.lean`, namespace `Bridge.WaveDynamics`,
promoting: `step`, `swap`, `shear`, `xor_cancel`, `swap_involution`,
`shear_involution_pointwise`, `step_eq_two_bounce`,
`reverse_is_swapped_pair`, `reverse_step_pointwise`, `reverse_step`,
`step_lossless`, `ringX`, `wallAt`, `dirichletX`, `iterN`, `pulse4`,
`ring4_period_four`, `dirichlet4_period_ten`. Note the footprint split
and preserve it: the pointwise theorems and `step_eq_two_bounce` are
axiom-free, while `reverse_step` and `step_lossless` use function
extensionality (Quot.sound) and the two decide theorems use
propext/Quot.sound. Do not launder the packaged theorems through the
pointwise ones in a way that hides the funext use; the split is part of
the result.

Promote from `formal/experimental/Frequencies.lean` and
`Overtones.lean` into a single `formal/bridge/PeriodSpectrum.lean`,
namespace `Bridge.PeriodSpectrum`: the general gcd law
(`order_eq_div_gcd`), the closed-form rotation factorisation
(`rotFactor`), `overtone_generation`, and the twelve-carrier exhibits
(`interval_addition`, `harmonics_are_iterates`, `orders_twelve`,
`circle_of_fifths`) kept as decidable instances of the general law.

Promote `formal/experimental/Recurrence.lean` content
(`wave_recurrence_bounded`) into `formal/bridge/Recurrence.lean` only if
the pigeonhole can be made choice-free; attempt a `Fin`-indexed
constructive pigeonhole first (states of `WState n` inject into
`Fin (2 ^ (2 * n))` by the standard bit encoding, and a constructive
pigeonhole on `Fin` avoids `Classical.choice`). If the choice-free proof
fails within reasonable effort, leave the theorem in the experimental
package and record the obstruction in its docstring; a single classical
entry must stay quarantined rather than entering the bridge.

### 1.2 Promote to the spine (foundation), gated

`formal/experimental/CantorBoundary.lean` promotes to
`formal/spine/Boundary.lean`, namespace `Boundary`, only after the Phase
3 framing decision below is made by the author, because `tail_erasing`
changes the corpus's self-description: the arena exclusion of erasure is
henceforth a finite-stage law whose failure at the colimit is a theorem.
The promotion itself carries: `GaugeHistory`, `encode`,
`encode_inj_pointwise`, `rungs_embed`, `encode_separates` (effective
cylinder separation), `boundary_unenumerable`, the lifted pole swap with
its liveness, `boundary_seals_itself`, and `tail_erasing`. All are
currently propext or axiom-free; preserve that.

### 1.3 Stays experimental

`Dispersion.lean` (symmetry-order result) and any module awaiting the
`F2[x]/(x^n - 1)` transfer-matrix algebra remain in
`formal/experimental/` with their docstring targets intact.

### 1.4 Mechanical checklist

1. Add new module names to `formal/bridge/lakefile.toml` roots and to
   the bridge list in `gen_audit.py`; same for `Boundary` in the spine
   if Phase 3 clears it.
2. Remove promoted modules from the experimental lakefile, or convert
   them to one-line re-export files importing the bridge versions, so
   downstream experiments keep compiling.
3. Rebuild all five packages, regenerate `Audit.lean` files, regenerate
   `AXIOMS.md`, run `VERIFY.sh`.
4. Acceptance: no `sorry`, no new axioms, every paper-cited declaration
   at propext or less, `Classical.choice` absent from bridge and spine,
   funext-using declarations confined to the two named wave theorems
   and flagged in `AXIOMS.md`.

---

## Phase 2 — Paper reframe

Target: one paper presenting a complete metaphysics with two eliminative
classifications, static and dynamic, over the same kernel and the same
single Z/2Z. Venue: Journal of Mathematical Philosophy (MCMP). Source of
truth for current text: `docs/paper/jmp_draft.tex`. Present everything as
a single coherent development; the text must contain no reference to
earlier drafts or to material having been moved.

New section order (current section numbers in parentheses):

1. Introduction. Recast the contribution as twofold classification:
   the kernel is forced (current Sections 3 to 4) and its motion is
   forced (new). The dependency diagram gains a second classification
   node feeding the dynamics row.
2. Architecture (2), updated for the promoted modules; the experimental
   annex paragraph shrinks to cover only what remains quarantined.
3. Classification of self-actions (3) and Fundamentality (4), unchanged.
4. Seal (5) and Ladder (6), unchanged.
5. Registration and two-bounce (7), unchanged, then a new section
   "Classification of couplings" directly after it, containing:
   the toggling theorem and its collision converse (losslessness selects
   the second-order xor form), the coupling uniqueness theorem with its
   three ambient conditions stated and defended (parity, pole
   invariance, drawing condition), the inter-site restriction declared
   in daylight as signature, in the exact style of Interpretation 3.8,
   and the identification of the survivor with the wave step. Frame the
   whole section explicitly as the twin of Theorem 3.6.
6. A new section "Wave dynamics" carrying: step equals swap after shear
   definitionally, reversal equals the bounce swap, losslessness for
   every coupling, the period spectrum and gcd law with the
   twelve-carrier as worked instance, boundary conditions selecting the
   spectrum (ring 4 versus fixed ends 10), and recurrence within
   capacity (with its footprint stated per the Phase 1.1 outcome).
7. Archive and capacity (8), Arrow as address (9), updated to
   cross-reference recurrence: within a level time is return, across
   levels time is ascent, duration carries the direction.
8. One underdetermination and gauges (10), revised per Phase 3.
9. The Boundary, a new section before self-articulation: rungs embed
   with effective separation, the boundary seals at its own carrier,
   the pole swap lifts live, and the tail step erases. State the
   reframed law here: losslessness is a finite-stage theorem, and its
   failure at the colimit is itself a theorem, recorded as the system's
   one structural loss. Interpretation block: the completion has the
   form of the system (live symmetric act, self-opaque), and the
   excluded shape returns at infinity.
10. Self-articulation (11), extended: clause (V) now cites the boundary
    section, and the interpretation may note that the consequent's
    dynamics is itself classified.
11. Dictionary (12): keep the meta-problem certificate as first exhibit
    and add a second, now earned, physical certificate identifying the
    classified wave dynamics with reversible lattice computation in the
    Fredkin and Toffoli tradition, admitted through Definition 10.3,
    with the identification confined to the certificate as always.
12. Open, refused, and philosophical (13): move the erasure-at-the-edge
    reframing into the residue accounting; add to refused: closed-form
    period law in general n pending the F2[x] algebra, dispersion
    relations, continuum frequencies; the annex paragraph in the formal
    companion shrinks accordingly.
13. Relation to prior work (14): add reversible cellular automata and
    lattice dynamics literature to the reversible-computation
    paragraph; the coupling classification warrants one added paragraph
    situating it against uniqueness results for cellular automaton
    rules.
14. Conclusion (15) and formal companion: the compression line gains a
    fourth row for the dynamics classification; the declaration list
    adds the Phase 1 bridge names; the audit paragraph updates the
    funext accounting.

Writing constraints as at the head of this spec, plus: every new theorem
statement gets a Status remark with declaration name, package letter,
and footprint; interpretations stay in marked blocks; refusals are
stated with the same prominence as results.

---

## Phase 3 — The coupling-flip gauge question (bounded research task)

The classification produced a finding the gauge inventory does not yet
place. The two surviving couplings, `xor` and `!xor`, form one orbit of
the flip involution `K ↦ fun l r => !(K l r)` on coupling space. Pole
conjugation fixes both survivors, since complement invariance is a
hypothesis of the classification, so the coupling flip is a distinct
involution and its gauge class is currently unassigned. Table 1 protects
a single dictionary Z/2Z; an unclassified involution threatens that
count and must be resolved before the paper claims completeness of the
inventory.

Three candidate resolutions, to be settled by proof, with the author
choosing framing only after the mathematics is in:

- (R1) Fourth face of the one Z/2Z. Seek an explicit equivariant
  identification of the coupling flip with the pole, address, or
  channel face, in the sense of Theorem 10.1. Candidate mechanism: the
  `!xor` step equals the `xor` step composed with a per-tick flip of the
  freshly written layer, which resembles the record gauge of Theorem
  9.1; attempt a conjugacy or a tick-reindexing that realises the flip
  as record gauge, and if it lands there, the flip is packaging and
  Table 1 gains a row citing the new theorem.
- (R2) Content gauge, new row. If no equivariant identification exists,
  attempt the negative result: prove the two dynamics are not conjugate
  by any state-space bijection commuting with the shift (a finite
  search on small n is decisive for a counterexample and suggestive for
  the general claim; the orbit structures on `WState n` for small n can
  be compared by kernel computation). If they are non-conjugate, the
  flip is content, Table 1 gains a content row, and the paper must
  state whether the dictionary Z/2Z count changes or whether the flip
  is exported only inside "up to coupling flip" clauses, mirroring the
  label-swap treatment.
- (R3) Collapse by dynamics. Check whether the two dynamics have equal
  observable structure (identical period spectra on all tested n,
  identical recurrence data); equality everywhere tested supports R1
  and directs effort back to finding the conjugacy, and any spectral
  difference proves R2 immediately.

Concrete first steps for the agent, in order: compute and compare the
full cycle structure of `step ringX` and `step (fun c i => !(ringX c i))`
on `WState n` for n in 2 to 5 by kernel decision; if spectra differ at
any n, formalise that difference as the R2 negative theorem; if spectra
agree at all tested n, attempt the per-tick-flip conjugacy of R1 as a
Lean theorem on general n. Deliverable either way: one new module
`formal/experimental/CouplingGauge.lean` with the decisive theorem, a
short note in the Phase 2 gauge section, and a Table 1 update. The
author signs off on the final gauge classification before the paper
text is written.

---

## Ordering and gates

Phase 1.1 and Phase 3 can run in parallel. Phase 1.2 waits on the
author's sign-off of the boundary framing (drafted in Phase 2 item 9).
Phase 2 writing starts once Phase 3's decisive theorem exists, because
the gauge section and Table 1 depend on it. Final acceptance: all five
packages build clean, `AXIOMS.md` regenerated, paper compiles with zero
unresolved references, and every claim in the paper resolves to a
declaration in the promoted locations.
