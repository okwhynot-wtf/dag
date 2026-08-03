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
| Horizon through every point | seal-per-reading = local horizon (not-residue) |
| Curvature accounting | T-14 Forman; unpaid flatness paid by registered faces (T-16) |
| Discrete `G ~ T` | T-16: unpaid Forman = faces short of threshold; stress = capacity at saturation |

**T-16 result.** The logical slot of Einstein-as-equation-of-state is occupied
by a discrete skeleton (`Bridge.EinsteinSkeleton.T16_discrete_einstein_skeleton`):
Jacobson inputs discharge; curvature relief costs records; local ledger stalks
exist with crude overlap. Continuum `G_{μν} = 8π T_{μν}` does **not** fall out.

**Still blocking continuum Einstein.**
- **O-2** (structural, deepest): no boosts ⇒ no Unruh `T`
- **O-3** (tractable): stalks ≠ sheaf — glue programme in open work
- **R-1** (structural obstruction, tractable budget attack): ultrametric;
  recombination counting is Lean
- **O-4 / O-5** (limit / input): continuum Lorentzian; matter from framework

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
- T-14: Forman sign proved; recombination is the cure toward zero.

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
- **O-3 partial** — `o3_stalk_glue_fragment`: same locus ⇒ capacity (and saturated
  effective matter) agree; full sheaf of dynamics still open
- **E passed (optional)** — `phase_E_continuum_toys`: combinatorial `T_c` /
  Clausius; Finite Page radiation = post-exhaustion speech; discrete
  Friedmann-shaped capacity update (no continuum, no `H₀`)

Stop rules: see `docs/MATTER_FLUX_PLAN.md`. A–E green ⇒ O-5 reframed as
emergent-flux programme; matter-as-input demoted to optional host API.
Continuum `T_{μν}` / SM inventory still refused. Phase E is interpretation
only — familiar names, not load-bearing for H.

## Coincidence: flatness embarrassment (not promoted)

Cosmology's near-flat universe is an unsolved calibration puzzle. DAG's
hard problem is manufacturing flatness (from Forman −∞ / ultrametric),
arriving at the same embarrassment from the opposite direction. Ledger
discipline: file as **coincidence** until a theorem promotes it.
