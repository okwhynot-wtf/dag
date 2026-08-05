# Axiom footprints

Generated from `lake build` via each package `Audit.lean`.

```bash
python formal/tools/gen_audit.py
bash formal/tools/audit.sh
```

Legend:

- **clean**: no axioms.
- **propext**: propositional extensionality alone.
- **Quot.sound**: quotient soundness alone; in this corpus it enters
  through `funext`, so a bare `Quot.sound` entry reads as function
  extensionality.
- **propext + Quot.sound**: both kernel axioms together, typically
  propositional reasoning combined with `funext` or kernel-decided
  `Decidable` instances.
- **declared**: declared postulates (the spine declares none).

The spine target is a zero-axiom footprint for every result.

Named funext flagging. Function extensionality is invoked directly by
`Bridge.WaveDynamics.reverse_step` and
`Bridge.Recurrence.wave_recurrence_bounded`;
`Bridge.WaveDynamics.step_lossless`, `Bridge.Recurrence.wave_recurrence`,
and `Bridge.Recurrence.wave_recurrence_pow` inherit that footprint.
Outside the promoted dynamics arc, `Bridge.Dil` applies `funext` in two
internal steps, the experimental `Experimental.Wave.waveFactor`
witness lifts its involution laws with `funext`, and the experimental
`Experimental.CouplingGauge.flip_conjugacy_of_four_dvd` packages its
pointwise conjugacy with `funext`, a footprint inherited by
`coupling_flip_dichotomy` and `flip_conjugate_four`. Every other
`Quot.sound` entry in the tables arrives through library lemmas, `omega`,
or `Decidable` instances; none of those entries makes a direct
`funext` step.

Architectural (non-Lean) audited residue, inventoried in the paper's
status section (Open, refused, and philosophical): existence of a
non-degenerate pointed act. Lean records a Bool *model*
(`Facticity.exists_nondegenerate_pointed_act_model`) and refuses
discharge as world-from-Bool; it does not declare a kernel axiom.

## `formal/spine/`

| Module | results | clean | propext | Quot.sound | propext + Quot.sound | declared |
|---|---:|---:|---:|---:|---:|---:|
| `Orbit` | 23 | 23 |  |  |  |  |
| `TwoCycle` | 13 | 13 |  |  |  |  |
| `Facticity` | 10 | 10 |  |  |  |  |
| `Ambient` | 20 | 16 | 4 |  |  |  |
| `Diagonal` | 12 | 12 |  |  |  |  |
| `Tower` | 25 | 25 |  |  |  |  |
| `Ladder` | 10 | 10 |  |  |  |  |
| `Cause` | 28 | 28 |  |  |  |  |
| `Branch` | 15 | 15 |  |  |  |  |
| `Limit` | 21 | 21 |  |  |  |  |
| `Revision` | 8 | 8 |  |  |  |  |
| `SEM` | 5 | 5 |  |  |  |  |
| `Interior` | 9 | 9 |  |  |  |  |
| `Monism` | 3 | 3 |  |  |  |  |
| `Apophasis` | 11 | 11 |  |  |  |  |
| `Canon` | 24 | 24 |  |  |  |  |
| `Information` | 7 | 7 |  |  |  |  |
| `Observer` | 8 | 8 |  |  |  |  |
| `NoExterior` | 8 | 8 |  |  |  |  |
| `Faces` | 6 | 6 |  |  |  |  |
| `Density` | 31 | 31 |  |  |  |  |
| `NonCommencement` | 11 | 11 |  |  |  |  |
| `OmegaDuration` | 13 | 13 |  |  |  |  |
| `SelfReference` | 31 | 11 | 20 |  |  |  |
| `SelfArticulation` | 1 |  | 1 |  |  |  |

## `formal/ledger/`

| Module | results | clean | propext | Quot.sound | propext + Quot.sound | declared |
|---|---:|---:|---:|---:|---:|---:|
| `Geom.Core` | 3 | 3 |  |  |  |  |
| `Geom.Registration` | 20 | 20 |  |  |  |  |
| `Geom.Ledger` | 13 | 13 |  |  |  |  |
| `Geom.Exhaustion` | 37 | 37 |  |  |  |  |
| `Geom.Provision` | 25 | 25 |  |  |  |  |
| `Geom.Bounce` | 17 | 17 |  |  |  |  |
| `Geom.Profile` | 7 | 7 |  |  |  |  |
| `Geom.Gradient` | 12 | 12 |  |  |  |  |
| `Geom.Totality` | 13 | 13 |  |  |  |  |
| `Geom.Freshness` | 19 | 19 |  |  |  |  |
| `Geom.Arc` | 8 | 8 |  |  |  |  |
| `Obs.AbstractMemory` | 1 | 1 |  |  |  |  |
| `Obs.MergeMonotone` | 10 | 6 |  |  | 4 |  |
| `Obs.EffectiveDynamics` | 15 | 13 | 1 |  | 1 |  |
| `Obs.Unlock` | 6 | 6 |  |  |  |  |
| `Obs.UnlockCompleteness` | 13 | 13 |  |  |  |  |
| `Obs.UnlockPricing` | 6 | 6 |  |  |  |  |
| `Obs.Recovery` | 21 | 19 | 2 |  |  |  |
| `Obs.CausalOrder` | 24 | 22 | 2 |  |  |  |
| `Obs.Dimension` | 15 | 13 | 2 |  |  |  |
| `Obs.Selection` | 69 | 69 |  |  |  |  |
| `Obs.StochasticUnlock` | 54 | 54 |  |  |  |  |
| `Obs.TotalVariationDPI` | 14 | 14 |  |  |  |  |
| `Obs.StochasticDivergence` | 8 | 8 |  |  |  |  |
| `Obs.Budget` | 10 | 10 |  |  |  |  |
| `Obs.ContinuumUnlock` | 5 | 5 |  |  |  |  |
| `Obs.EmbeddedObserver` | 9 | 9 |  |  |  |  |

## `formal/bridge/`

| Module | results | clean | propext | Quot.sound | propext + Quot.sound | declared |
|---|---:|---:|---:|---:|---:|---:|
| `Alphabet` | 7 | 7 |  |  |  |  |
| `Capacity` | 13 | 9 | 4 |  |  |  |
| `OneZ2` | 12 | 12 |  |  |  |  |
| `KernelAdmit` | 6 | 6 |  |  |  |  |
| `RegistrationSpine` | 8 | 8 |  |  |  |  |
| `TickSimulation` | 21 | 17 | 4 |  |  |  |
| `Environment` | 15 | 15 |  |  |  |  |
| `Dil` | 74 | 26 | 40 | 3 | 5 |  |
| `RegistrationFactor` | 11 | 11 |  |  |  |  |
| `ArchiveMustSpeak` | 5 | 5 |  |  |  |  |
| `PageShape` | 11 | 5 | 6 |  |  |  |
| `ArchiveMonotone` | 5 | 5 |  |  |  |  |
| `BranchNondeterminism` | 5 | 5 |  |  |  |  |
| `BranchMeasure` | 14 | 6 | 8 |  |  |  |
| `LadderGrowth` | 14 | 14 |  |  |  |  |
| `Forman` | 21 | 21 |  |  |  |  |
| `Saturation` | 5 | 5 |  |  |  |  |
| `FlatnessDebt` | 14 | 10 | 4 |  |  |  |
| `FiberFlux` | 15 | 15 |  |  |  |  |
| `FluxPattern` | 10 | 10 |  |  |  |  |
| `LedgerPatchGlue` | 19 | 19 |  |  |  |  |
| `RecombinationBudget` | 7 | 2 | 5 |  |  |  |
| `PhaseEToys` | 14 | 5 | 9 |  |  |  |
| `PeriodTwoOrbits` | 7 | 5 | 2 |  |  |  |
| `CutShift` | 8 | 5 | 3 |  |  |  |
| `OrderDimGrowth` | 5 | 5 |  |  |  |  |
| `TwoBounce` | 77 | 69 | 8 |  |  |  |
| `BridgeArc` | 41 | 25 | 14 |  | 2 |  |
| `WaveDynamics` | 10 | 6 |  | 2 | 2 |  |
| `DynamicsAmbient` | 7 | 4 | 3 |  |  |  |
| `PeriodSpectrum` | 16 | 4 | 3 |  | 9 |  |
| `Recurrence` | 14 | 2 | 1 |  | 11 |  |

## `formal/dictionary/`

| Module | results | clean | propext | Quot.sound | propext + Quot.sound | declared |
|---|---:|---:|---:|---:|---:|---:|
| `Certificate` | 8 | 8 |  |  |  |  |
| `LCertificate` | 2 | 2 |  |  |  |  |
| `Quintom.Kernel` | 8 | 8 |  |  |  |  |
| `Quintom.Certificate` | 8 | 8 |  |  |  |  |
| `Quintom.FixedPoint` | 5 | 5 |  |  |  |  |
| `Quintom.Damping` | 3 | 3 |  |  |  |  |
| `Quintom.Growth` | 10 | 1 | 9 |  |  |  |
| `BitFlip` | 10 | 10 |  |  |  |  |
| `Kramers` | 14 | 14 |  |  |  |  |
| `Page` | 10 | 10 |  |  |  |  |
| `QEC` | 7 | 7 |  |  |  |  |
| `NoClone` | 11 | 11 |  |  |  |  |
| `MetaProblem` | 11 | 9 | 2 |  |  |  |

## `formal/experimental/`

Experimental (quarantined): exploratory results, not part of the audited spine/ledger/bridge/dictionary chain.

| Module | results | clean | propext | Quot.sound | propext + Quot.sound | declared |
|---|---:|---:|---:|---:|---:|---:|
| `Overtones` | 13 |  | 10 |  | 3 |  |
| `Frequencies` | 4 | 1 |  |  | 3 |  |
| `WaveEquation` | 21 | 1 | 2 |  | 18 |  |
| `CantorBoundary` | 16 | 16 |  |  |  |  |
| `SpectrumSymmetry` | 12 |  | 1 |  | 11 |  |
| `CouplingGauge` | 35 | 9 | 6 |  | 20 |  |

Totals: 1526 audited results; 1256 clean.

