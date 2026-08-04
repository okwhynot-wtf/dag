# Interpretation notes (hedged)

These are readings, not Lean theorems. They sharpen inventory and point
at R-1; they do not discharge E3 or E4.

## ω / de Sitter / Padmanabhan

Three limits share one counted shape:

| Limit | Source | Shape |
|---|---|---|
| ω-flatline | `OmegaDuration.omega_duration_package` | Magnitude completes (`Option(carrier) ≅ carrier`); ancestry/stage tags continue |
| Counted de Sitter | T-13 under `NumberEqualsVolume` | Volume ~ `K^t` while expanding; flatline at ω = growth of the count completes |
| Padmanabhan emergent space | Physics echo | Expansion from counting imbalance; completes at holographic equipartition → de Sitter |
| RE attractor `w = −1` | Quintom / T-8 | Same asymptote seen dynamically |

**Hedges.** No claim that DAG *is* Padmanabhan's programme. No continuum
metric. No temperature. The echo is asymptotic shape in the counted sense.

## Jacobson inventory (combinatorial skeletons)

Jacobson derived Einstein equations from (i) entropy bound on horizons and
(ii) Clausius: heat crossing a horizon registers as entropy.

| Jacobson input | DAG skeleton |
|---|---|
| Entropy / area bound | Capacity bound; Page entry reads `|caps T|` as Bekenstein-shaped |
| Clausius (heat → entropy) | T-4 Landauer: what merges must register |
| Local balance / EoS | T-15 saturation: alive ⇔ records ≤ caps; equality fixes flux |
| Horizon through every point | seal-per-reading = local horizon; `observers_forced` supplies observers (derived, not postulated) |
| Curvature accounting | T-14 Forman; unpaid flatness paid by registered faces (T-16) |
| Discrete `G ~ T` | T-16: unpaid Forman = faces short of threshold; stress = capacity at saturation |

**T-16 result.** The logical slot of Einstein-as-equation-of-state is occupied
by a discrete skeleton (`Bridge.EinsteinSkeleton.T16_discrete_einstein_skeleton`):
Jacobson inputs discharge; curvature relief costs records; local ledger stalks
exist with crude overlap. Continuum `G_{μν} = 8π T_{μν}` does **not** fall out.

**Still blocking continuum Einstein.**
- **O-2** (structural, deepest): no boosts ⇒ no Unruh `T`
  (cut-shift dead-ended; blindness forced — period global, one ℤ/2 ⇒ one
  flow; O-2 ≈ no continuous 1-param subgroup; same missing object as O-4)
- **O-3** (tractable): stalks + dynamics sections landed; Mathlib sheaf/site still open
- **R-1** (structural obstruction, tractable budget attack): ultrametric;
  recombination counting is Lean
- **O-4 / O-5** (limit / input): continuum Lorentzian (geometric face of the
  same 1-param gap as O-2); matter from framework

Continuum field equations remain refused. Discrete next steps live under
tractable open work in `docs/RESIDUE.md` (sheaf, recombination budget,
combinatorial `T`, finite Page toy).


## Causal-set postulate (T-13)

"Order plus number equals geometry" (Malament + counting). DAG has order
(`dim = 1`) and number (capacity). Flagged identification:
`countedVolume := capacity`. Yields discrete Hubble of one bit per naming
tick at `K = 2`. **Not** a forecast of `H₀`.

## Curvature audit (summary)

- Precluded only on the 1-d line (trivial).
- Forced non-flat on the ledger (`¬flat(prof)`); de Sitter–shaped under T-13.
- Maximal negative coarse curvature on branches (ultrametric / 0-hyperbolic).
- T-14: Forman sign proved; recombination ↑ Forman (flatness paid by faces).

Research question inverted: not “can DAG have curvature?” but “can it buy
near-flatness from Forman −∞ within the registration budget?”

## Matter reading (hypothesis under test)

**H.** Matter is an emergent effective description of record flux that a
bounded lossless ledger is forced to emit at capacity saturation.

**H⊥.** Matter needs a second generator beyond registration / saturation.

Sprint / phase status:
- **A–C2 passed** — `effective_matter_sprint` (flux defs, slack, Forman budget)
- **D passed** — `phase_D_flux_patterns`: ≥2 Bool components; channels/branches
  supply multiplicity; vacuum vs matter onset = oscillator vs registration
- **O-3 partial** — stalk glue + restriction + `o3_dynamics_section_fragment`:
  balanced patches restrict/glue Fin-combinatorially; Mathlib sheaf/site still open
- **E passed (optional)** — `phase_E_continuum_toys`: combinatorial `T_c` /
  Clausius; Finite Page radiation = post-exhaustion speech; discrete
  Friedmann-shaped capacity update (no continuum, no `H₀`)

Stop rules: see `docs/MATTER_FLUX_PLAN.md`. A–E green ⇒ O-5 reframed as
emergent-flux programme; matter-as-input demoted to optional host API.
Continuum `T_{μν}` / SM inventory still refused. Phase E is interpretation
only — familiar names, not load-bearing for H.

## I-2 Fin alphabet-UF (calibration)

At `K = 2` with system carrier `S = Bool`, the letter type *is* the blank
alphabet, so `UniqueFactorization` on `boolCapsArchive` is exactly the
minimal bijection `|E_{T+1}| = K|E_T|`. Rigidity is **base-relative**
(`rigidity_iso_of_base`): `|E₀| = 4`, iso unique once `h₀` is fixed.
Pointed UF characterises the free end; alphabet-UF characterises the
minimal end. Ladder-predicate addressing is witnessed
(`ladder_predicate_addressing_witness`): combinatorial `|Level → Bool|` =
`caps`, realised by the Fin archive — not a second Predicate `Archive`.
Address-uniform `idx` fragment lands for `|S| > K` (`AddressUniform`);
Bool is the trivial `idx = id` case.

## T-2 tick identification (classified — v0.2)

`Bridge.TickSimulation.tick_identification` retires the modelling license.
Eternal UF-archive dynamics factor through naming extensions up to record
gauge; periodic Fund is exempt; obstructed swap proves the dichotomy
exhaustive. Ingredients: straighten (`isoToFreeOnBase`) → append step
(`tick_identification_step`) → namer shape → rate weld → ladder
`NamingExtension`. Fence: not a total functor on carriers. Arc write-up:
`docs/ARC_V02.md`. Historical remnant: `tick_identification_licensed`.

**Time–dissipation corollary** (`time_dissipation_one_property`): Fund is
exempt from tick identification, and Fund is the H=0 oscillator (vacuum
dynamics). Undamped dynamics have no naming ticks; the arrow appears
exactly when registration does. Formal spine/ledger columns: theorem-grade.
Dictionary damping=registration rhyme remains K-certificate (I-4).

## Jacobson quantifier (surfaced)

T-16 discharges the Jacobson *skeleton*, including the quantifier: every
self-reading has a dodge (local horizon / seal-per-reading), and
`Observer.observers_forced` supplies the observers. Horizon
observer-dependence is **derived**, not postulated — easy to miss under
“not residue” in `DAG_SYMBOLIC.txt` §VII.

## Period-2 / KMS and area-as-caps (fence)

- **Period-2/KMS toy** (`Period2KMS`): equilibrium = period-2 under ℤ/2 +
  constant combinatorial `T_c`. Not continuum KMS; not Unruh (O-2).
- **Area-as-caps** (`areaBits`): Bekenstein-shaped `log₂|caps|`. Not
  continuum area / island theorems.

## Partial Lorentzian dictionary (fence)

Order dim-1 + capacity growth + ℤ/2-only underdetermination
(`partial_lorentzian_dictionary`). Not a Lorentz group; not Unruh;
continuum O-4 refused. Separates the countable causal/capacity skeleton
from the structural boost gap (O-2).

## Dictionary adapters (fence)

- **QEC L-cert** (`formal/dictionary/QEC.lean`, `exhibits/qec/`): syndrome
  extraction fills the same Registration / L-certificate schema as Page on a
  Bool swap toy. Not a threshold theorem; not a holographic code claim.
- **DESI / quintom null** (`exhibits/quintom/DESI_NULL.md`): certificate ≠
  DESI prediction. Do not treat residual DESI tension as a DAG forecast.
- **Corpus self-reference** (`SelfReference.corpus_not_universal`): Lawvere
  seal applied at corpus↔corpus; deficit (names ≪ predicates), lag (portrait
  outdated by exponential silence), ω≠rung. Incompleteness now unconditional;
  completeness-in-limit is a `FairSchedule` policy. Observation: the version
  history of `DAG_SYMBOLIC.txt` enacts the theorem in prose — each revision
  says what the previous could not.
- **RE-side growth law** (`Dictionary.Quintom.Growth.re_side_growth_law`):
  `modeCount T = |Channel|^(T+2) = caps T`, doubles at `Kmin`. Combinatorial
  dictionary weld only — not continuum Fourier modes, not `H₀`, not DESI.
  The ODE exhibit (`integrate.py`) is **not** evidence for this law.

## Coincidence: flatness embarrassment (not promoted)

Cosmology's near-flat universe is an unsolved calibration puzzle. DAG's
hard problem is manufacturing flatness (from Forman −∞ / ultrametric),
arriving at the same embarrassment from the opposite direction. Ledger
discipline: file as **coincidence** until a theorem promotes it.
