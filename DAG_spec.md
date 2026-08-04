# DAG: Diagonal Archive Geometry
## Specification for a hybrid corpus, v0.1-draft

Working name: **DAG** (Diagonal Archive Geometry). The acronym also names a
directed acyclic graph, which is what the causal order of the merged system
provably is (AG §VI acyclicity, DM `asymmetry_is_acyclicity`), so the pun is
load-bearing.

---

## 1. Verdict on the third corpus

The re-entrant engine note (RE) is included, and its role is fixed precisely.
It is neither spine nor ledger; it is the first entry in a **dictionary layer**
of physical instantiations, and it earns its place three ways.

1. It is an existence proof that the kernel symmetry has at least one exact
   physical realisation: swap ≅ ¬, fixed set ≅ w = −1, forced +1 ≅ the second
   channel, with the single-canonical-field no-go playing the Lawvere role.
2. It supplies a concept both formal corpora lack, **dissipation**. Hubble
   friction is what lets re-entry decay, and this is the physical face of AG's
   Registration: contraction in the system must land somewhere, and the
   somewhere is the expansion.
3. Its frictionless limit closes a triangle. At H = 0 the model is two
   undamped oscillators with an exact swap involution and a silent record,
   which is AG's oscillator class (Inj ∧ ¬merge ∧ ¬record), which is DM's
   Fundamental. Three corpora, one object, reached independently. That
   coincidence is the strongest single argument that the hybrid is a system
   and not a concordance.

RE's own boundary discipline (no numbers descend from Bool, the action is an
input) matches the derived/residue/refused ledger of the other two corpora and
transfers into §8 unchanged.

---

## 2. Architecture

Three layers, strict downward dependency. Nothing in a lower layer may import
from a higher one.

```
  Layer 2  DICTIONARY   (RE + future entries)   physical instantiations
              │ imports
  Layer 1  LEDGER       (AG)                    S×E, registration, capacity,
              │ imports                          profile, address
  Layer 0  SPINE        (DM)                    arena, Fund, seal, ladder,
                                                 non-commencement, branch
```

- **Spine** is unconditional mathematics inside the DM arena. Zero axioms,
  no sorry, no external libraries. Unchanged from `formal/spine/`.
- **Ledger** is resource accounting over the spine. The environment E of AG
  is *implemented by* the DM ladder (see interface I-2), so AG's presupposed
  carriers become constructed objects.
- **Dictionary** admits physical models by certificate (§6). Kernel-side
  facts of each entry are Lean; dynamical facts (ODE solutions, numerics)
  are exhibits and are refused as Lean by policy.

---

## 3. Unified carriers and notation

| Symbol | Home | Meaning | Hybrid status |
|---|---|---|---|
| (α, a, z), a∘a = id | DM | pointed unoriented act | primitive (arena) |
| Bool, ¬ | DM | the Fundamental, unique survivor | theorem |
| Lₖ, Lₖ₊₁ = Option(Lₖ) | DM | ladder | theorem |
| U : S×E → S×E | AG | joint microstep | constructed: U bijective is DM losslessness lifted to the product |
| K ≥ 2 | AG | merge rate / blank alphabet | K = 2 minimal, **derived** via `fundamental_two_elements`; K > 2 admissible as alphabet generalisation, flagged non-minimal |
| caps T | AG | capacity at tick T | **identified** with the level-T predicate space, |caps T| = 2^(T+2) |
| prof | AG | capacity profile | committed ladder realises the `expand` constructor |
| address ∈ {fwd, rev} | AG | orientation reading | **identified** with DM pole swap / `two_readings` (ℤ/2) |
| φ, σ, swap | RE | scalar channels, involution | dictionary entry; swap is the image of a under the certificate hom |
| p+ρ = ρ(w+1) | RE | involution observable | the observable on which swap acts as ¬ |

Tick disambiguation (mandatory, see T-2): a **naming tick** is a DM ladder
step; a **microtick** is one application of U. They are identified only where
Theorem T-2 licenses it.

---

## 4. The dictionary (identifications already visible)

| DM | AG | RE |
|---|---|---|
| Fundamental (live 2-cycle) | oscillator class | frictionless quintom, H = 0 |
| `fundamental_forgets_count` | archive silent | undamped: no envelope decay |
| involution / no orientation | undirected bounce profile | swap symmetry of the field equations |
| pole swap, `two_readings` | address ∈ {fwd, rev} | φ↔σ relabelling |
| dodge / forced +1 | blank adjunction (conveyor) | second channel required to cross w = −1 |
| excluded fixed point (void) | (no analogue) | w = −1, the divide |
| `lift_conservative`, stage tags | archive recoverable on ascent | (no analogue) |
| predicate growth 2^(k+2) | c(t+1) = K·c(t), K = 2 | modeCount = \|Channel\|^(T+2) (= caps; doubles @ Kmin) |
| ω flatline vs ancestry | capacity clock vs record | late-time relaxation, envelope → 0 while phase history remains |
| erasure priced out of the base | Registration: merge ⇒ record | Hubble friction registers into expansion |

The one ℤ/2 underdetermination appears three times (pole swap, address,
channel labels) and the hybrid states it once: **T-7**.

---

## 5. Interface contracts

**I-1 Spine → Ledger.** Spine exports: arena, `IsFundamental`, seal, ladder
with `lift_injective` / `lift_conservative`, non-commencement, branch
modality, stage tags. Ledger may not re-postulate any of these.

**I-2 Environment implementation.** AG's E at horizon T is the DM ladder
carrier at level T, with cap slots the `none`-namers and |caps T| the
predicate count. AG's aliveness K^T ≤ |caps T| becomes, at K = 2, the
arithmetic fact 2^T ≤ 2^(T+2), so the committed ladder is eternally alive by
construction. Profiles other than `expand` describe non-committed ladders and
are in scope.

**I-3 Ledger → Dictionary.** Ledger exports: Registration, exhaustion bound,
profile constructors, address, dim = 1, growth law. Dictionary entries
consume these as the vocabulary in which their physical readings are stated.

**I-4 Dictionary admission certificates (two routes).** A physical model
enters the dictionary by filing one of two Lean-checked certificates.
The hybrid has two lower layers; each admits physical instantiation.

**K-certificate (kernel / spine route).** The model exhibits:
  (a) an involution symmetry of its equations of motion (`swap ∘ swap =
      square`, with `square` = id or central negation);
  (b) an observable on which that symmetry acts as exact negation;
  (c) identification of the symmetry's fixed set with a distinguished
      physical locus — nonempty (RE) or provably empty (Kramers / live Fund);
  (d) a no-go showing the level below cannot represent the symmetry alone
      (forced +1).
RE / quintom, BitFlip, and Kramers file K-certificates. Schema written off
the quintom; captures kernel instantiations.

**L-certificate (ledger route).** The model exhibits, on a finite toy:
  (a) a bijective / injective joint step `U`;
  (b) an identified system-side merge;
  (c) the compensating environment record;
  (d) a capacity schedule with its aliveness bound;
  (e) an exhaustion tick with the mute-failure corollary (T-10).
The Page / black-hole-information toy files an L-certificate. Gravitational
BH and QFT remain refused; the toy is finite-dimensional and constructive.
Without the L-route, ledger-flagship instantiations (Registration +
exhaustion) cannot enter through I-4 as written — a defect in the old
schema, not in the candidate.

---

## 6. Theorem obligations

Numbered, with difficulty and acceptance criteria. Lean throughout except
where marked exhibit.

**T-1 Environment universality (keystone).** Define E as the minimal
completion making a merging U_S injective; prove existence and uniqueness up
to iso; recover |E| ≥ K as first corollary. *Difficulty: high, may fail
interestingly.* Acceptance: universal property stated arrow-theoretically in
the DM arena style; AG §I counting becomes a corollary. If it fails, document
the obstruction as residue; the hybrid survives with E as posited structure,
degraded to AG's current status.

**T-2 Tick simulation.** Every AG microstep sequence satisfying Registration
factors through DM naming extensions, and conversely the committed ladder
yields a U with StreamMute at every tick. *Difficulty: medium-high.*
Acceptance: a functor-like translation in both directions with identity
round-trips on the committed path. Failure mode is informative: it locates
where geometry outruns representation, and gets filed as residue, with the
naming-tick/microtick identification then restricted to the proven fragment.

**T-3 Alphabet grounding.** K = 2 is the least admissible merge rate, derived
from `fundamental_two_elements`; K > 2 corresponds to non-minimal blank
alphabets and inherits no uniqueness claim. *Difficulty: low.*

**T-4 Registration on the spine.** A merging reading strictly above the
lossless base forces named compensation at the next level (the
Landauer-shaped theorem: what merges must register). *Status: discharged*
on the spine (`RegistrationSpine`) and as a **derived corollary** of
joint-injectivity / Dil capacity (`Bridge.Dil.registration`) — no longer a
primitive-shaped ledger line. Acceptance: naming-extension fact plus the
Dil fibre separation corollary; erasure lemmas as ingredients.

**T-5 Oscillator triangle.** The H = 0 limit of the RE model realises an
arena object whose act is the swap, whose record is empty, and which is
fundamental in the DM sense on its two-channel labelling. *Difficulty: low
on the kernel side.* The ODE-side statement (undamped ⇒ envelope constant) is
an exhibit.

**T-6 Damping = registration (dictionary-level).** For H > 0, phase-space
contraction of the channel system is compensated by growth of the expansion
record; frictionless ⇔ silent archive. *Status: semi-formal.* The kernel
skeleton (contraction is a merge, merge ⇒ record by T-4) is Lean; the
identification of the register with H is a certificate clause, so an exhibit.

**T-7 One ℤ/2, three faces.** Pole swap ≅ address reversal ≅ channel
relabelling, as a single underdetermination theorem with three named
projections. *Difficulty: near-mechanical.*

**T-8 Fixed-point discipline.** The kernel excludes a(x) = x as a state of
the act. In any certified model with dissipation, the fixed set is attained
only on a measure-zero set of instants and approached asymptotically without
finite-time attainment. *Kernel side Lean; ODE side exhibit.* This resolves
the apparent tension between DM's excluded void and RE's attractor: exclusion
survives instantiation, since the model touches the divide at crossings and
settles onto it only in the limit, and "the engine runs as the transient" is
the licensed gloss.

**T-9 Capacity dictionary.** caps T = 2^(T+2); committed ladder = `expand`
profile; the ω flatline is the limiting statement of the capacity clock, with
ancestry (stage tags) as the surviving record. *Difficulty: arithmetic.*

**T-10 The archive must speak.** Bounded confinement + Inj + sustained
merging jointly force a tick at which StreamMute fails. Contrapositive of
AG eternal mute aliveness ⇒ unbounded capacity; qualitative Page curve.
*Difficulty: near-mechanical (named corollary of existing Provision /
Exhaustion).* Acceptance: bridge theorem packaging
`no_static_eternal_aliveness`, with Page time = exhaustion on bounce
schedules; L-certificate entries cite it as clause (e).

**T-11 Combinatorial second law.** Landauer (T-4: merge ⇒ record) plus
ladder record monotonicity (`lift_injective`, `no_retraction`: archive never
shrinks). Dissipation writes; records accumulate irreversibly; ledger arrow
shadows the thermodynamic arrow. *Near-mechanical reading.* Refused:
temperature, Boltzmann factors, statistical mechanics proper.

**T-12 Outcome selection (measurement shape).** Branch package: ascent
necessary, direction free, ≥2 children, histories diverge, no selection
mechanism in the law. Everett-flavoured object; underdetermination is why
no mechanism appears. Companion dictionary: no-cloning finite support
no-go pairing with losslessness. *Near-mechanical.* Refused: Born rule,
probabilities, preferred basis.

**T-13 Expansion as the price of liveness (conditional).** Named promotions
of E1 (monotone structure) and E2 (exponential capacity forced by
aliveness). Causal-set pedigree: order + number = geometry. Flag postulate
`NumberEqualsVolume` (counted volume := capacity schedule). Then volume
grows as `K^t`; at `K = 2`, one bit per naming tick — counted de Sitter.
*Units caveat:* ticks are naming steps; no seconds; no `H₀` forecast.
E4 (Friedmann + matter) stays refused. E3 (spatial metric) blocked by R-1.

**T-14 Forman–Ricci on the branch tree.** Measure-free combinatorial
curvature: unweighted Forman `Ric_F = (4+#faces) − deg(u) − deg(v)`. On the
`K=2` tree, internal edges are strictly Forman-negative; attaching a
registered 2-cell (recombination) strictly raises Forman quantity on touched
edges — flatness paid by faces (same clause as T-16's discrete `G ~ T`
caricature). Internal edges need ≥2 faces to leave negativity. Companion:
eternal aliveness ⇒ ¬flat(prof) (anti-precludes counted flatness). Ollivier
refused (measures). Riemann unstateable until space+signature (absence ≠
preclusion).

**T-15 Saturation / equation-of-state form.** Alive ⇔ records ≤ caps growth;
saturation := equality; at saturation, record flux is determined by the
capacity schedule. Ledger-balance reading of the Jacobson audit — no
curvature claimed; field equations refused. Packages `Geom.Profile.Alive`,
`Obs.Budget` B1/B2, and capacity step-growth uniqueness.

**T-16 Discrete Einstein / Jacobson skeleton.** Packages every discharged
Jacobson ingredient (capacity, Landauer, seal-horizon, saturation EoS,
Forman) plus the discrete `G ~ T` caricature: unpaid Forman flatness on
an edge is paid by registered 2-cells; at saturation, stress-energy proxy
(record flux) equals consumed capacity; local ledger stalks over branch
loci with overlap compatibility. Continuum field equations **do not fall
out** — O-2 (no Unruh `T`), O-3 (no ledger sheaf), O-4/O-5, R-1 remain.
Refused: `G_{μν} = 8π T_{μν}` as Lean; temperature; continuum metric.

---

## 6½. Expansion taxonomy (E1–E4)

| ID | Meaning | Status |
|---|---|---|
| **E1** | Monotone growth of structure (ladder ascends, namer new, no retraction) | Theorem (`E1_monotone_structure`) |
| **E2** | Exponential capacity at fixed rate; liveness forces it | Theorem (`E2_exponential_capacity`) |
| **E3** | Growth of a spatial metric | Blocked — see R-1 |
| **E4** | Friedmann dynamics with matter | Refused |

Inventory note (Interpretation, not Lean gravity): the corpus holds discrete
skeletons of both Jacobson inputs — capacity bound ≅ Bekenstein-shaped
(`|caps T|`), T-4 ≅ Clausius-shaped (merge ⇒ register) — plus Padmanabhan's
asymptotic shape at ω (magnitude flatlines, ancestry continues; RE `w = −1`
attractor is the same asymptote dynamically). Three limits, one counted
shape. See `docs/INTERPRETATION.md`.

---

## 6¾. Curvature audit

| Register | Curvature status |
|---|---|
| Committed ladder (order dim 1) | **Precluded trivially** — Riemann vacuous on a line (a wire) |
| Capacity profile / counted geometry | **Forced non-flat** — eternal aliveness ⇒ ¬flat(prof); under T-13 number=volume, committed `V=K^T` is de Sitter–shaped (constant relative growth ⇒ constant positive spacetime curvature in FRW reading) |
| Branch tree (coarse) | **Maximal negative** — 0-hyperbolic / ultrametric = curvature → −∞; restates R-1 |
| Branch tree (Forman, T-14) | **Proved sign** — internal edges Forman-negative; recombination ↑ Forman (flatness paid by faces) |

**Inversion.** DAG does not struggle to have curvature; it struggles to
manufacture flatness. R-1 sharpens to: can the framework buy its way from
Forman −∞ / ultrametric to near-flat local geometry, and does the
registration budget (aliveness bound) afford the required recombinations?

**Coincidence (not promoted).** Observed near-flatness of space is also an
unsolved calibration puzzle in cosmology; DAG hits the same embarrassment
from the opposite direction. File as coincidence until a theorem promotes it.

---

## 7. Resolved tensions (design decisions, recorded)

1. **Lossless spine vs lossy ledger.** Resolution: stratification. Global U
   is bijective (DM losslessness on S×E); merges live strictly in U_S above
   the base and are compensated in U_E (T-4). The base itself never merges.
2. **Naming tick vs microtick.** Resolution: T-2, with the identification
   restricted to whatever fragment survives proof.
3. **Excluded fixed point vs attractor.** Resolution: T-8. Combinatorial
   exclusion is a statement about the act; asymptotic relaxation is a
   statement about a damped model; they coexist because the model never
   occupies the fixed point in finite time away from crossing instants.
4. **Eternal aliveness vs liveness.** These are one assumption in two
   vocabularies and the hybrid states it once, as spine liveness, with AG's
   eternal mute aliveness derived along the committed ladder (I-2). The
   facticity beneath it remains residue, listed once.

---

## 8. Residue / refusal ledger (merged)

Canonical detail: `docs/RESIDUE.md`. Summary:

**Tractable open work (Lean-attackable):**
- **O-3** sheaf of local ledgers (glue `LocalLedgerPatch` stalks);
- **R-1 recombination budget** — faces-per-node vs aliveness cost of
  Forman near-flatness (ultrametric obstruction real; counting is Lean);
- combinatorial temperature caricature (counting entropy / period-2 toys;
  not Unruh);
- finite-mode Page–Bogoliubov toy; matter-as-input dictionary;
- finite branch measures (Ollivier trial); area-as-`|caps|` sharpening;
- RE-side growth law (**landed** `re_side_growth_law`); partial Lorentzian
  dictionary; arbitrary-`U_S` UP.

**Structural open (hard walls):**
- **O-2** no boost / Unruh `T` (only ℤ/2) — deepest Einstein gap;
- **R-1** ultrametric ≠ space — attack via recombination budget above;
- **O-4 / O-5** continuum Lorentzian limit; matter from the framework.

**Philosophical residue:** facticity of liveness; ℤ/2 + branch choice;
arena adequacy; blank ontology; RE action inputs.

**Refused (genuine — continuum / mind / overclaim):**
- number or observable `H₀` identified from Bool / naming ticks;
- quintom-as-world; DESI as forecast; premise-free Law of Time;
- continuum spacetime / Einstein / QFT / evaporating BH as Lean
  (finite Page toy admitted);
- continuum Boltzmann; Born rule from underdetermination alone;
- hard problem / qualia / experiential claims;
- matter or Friedmann **derived from Bool alone**
  (matter-as-input and discrete balance caricatures are open work).

---

## 9. Repository layout

```
formal/
  spine/        DM, unchanged                      v-current
  ledger/       AG rebuilt over I-1, I-2           target v2.0.0
  bridge/       T-1 … T-4, T-7, T-9                new
  dictionary/
    certificate.lean                               I-4 K-certificate schema
    LCertificate.lean                              I-4 L-certificate schema
    quintom/    RE kernel (T-5,T-6,T-8) + Growth   new
    Page.lean   Page / BH-info L-certificate       new
exhibits/
  quintom/      ODE integration, figures           refused as Lean
  page/         BH dictionary notes + conjecture   refused as Lean gravity
docs/
  SPINE.md, LEDGER.md, DAG.md (this spec), AXIOMS.md (union, must stay empty)
```

Versioning: dictionary entries are independently versioned; a bridge theorem
may not cite an exhibit.

---

## 10. Milestones

- **M1** (mechanical): T-3, T-7, T-9. Establishes the dictionary skeleton.
- **M2**: T-4 Registration on the spine. First genuinely new theorem.
- **M3**: T-5 + T-8 kernel sides; quintom certificate filed; exhibit pipeline
  reproducible.
- **M4**: T-2 simulation, or its documented failure fragment.
- **M5** (keystone): T-1 environment universality, or its documented
  obstruction. Go/no-go for calling DAG a single system: with T-1 and T-2 the
  claim "representational growth and record accumulation are one process seen
  from inside and outside" is a theorem pair; without them it remains a
  dictionary, which is still worth having.

---

## 11. The one-line version

The spine says why anything ticks, the ledger says what each tick costs and
where it is written down, and the dictionary shows at least one world-shaped
thing in which the ticking, the cost, and the writing are all literally
present. Frictionless, all three collapse to the same two-beat oscillator,
and that is the hybrid's signature fact.
