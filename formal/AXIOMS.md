# Axiom footprints

Generated from `lake build` via each package `Audit.lean`.

```bash
python formal/tools/gen_audit.py
bash formal/tools/audit.sh
```

Legend:

- **clean** — no axioms.
- **propext**, **propext + Quot.sound** — Lean kernel axioms (`funext` / quotients).
- **declared** — declared postulates (the spine declares none).

The spine target is a zero-axiom footprint for every result.

## `formal/spine/`

| Module | results | clean | propext | propext + Quot.sound | declared |
|---|---:|---:|---:|---:|---:|
| `Orbit` | 23 | 23 |  |  |  |
| `TwoCycle` | 13 | 13 |  |  |  |
| `Diagonal` | 12 | 12 |  |  |  |
| `Tower` | 25 | 25 |  |  |  |
| `Ladder` | 10 | 10 |  |  |  |
| `Cause` | 28 | 28 |  |  |  |
| `Branch` | 15 | 15 |  |  |  |
| `Limit` | 21 | 21 |  |  |  |
| `Revision` | 8 | 8 |  |  |  |
| `SEM` | 5 | 5 |  |  |  |
| `Interior` | 9 | 9 |  |  |  |
| `Monism` | 3 | 3 |  |  |  |
| `Apophasis` | 11 | 11 |  |  |  |
| `Canon` | 24 | 24 |  |  |  |
| `Information` | 7 | 7 |  |  |  |
| `Observer` | 8 | 8 |  |  |  |
| `Faces` | 6 | 6 |  |  |  |
| `Density` | 31 | 31 |  |  |  |
| `NonCommencement` | 11 | 11 |  |  |  |
| `OmegaDuration` | 13 | 13 |  |  |  |
| `SelfReference` | 31 | 11 | 20 |  |  |

## `formal/ledger/`

| Module | results | clean | propext | propext + Quot.sound | declared |
|---|---:|---:|---:|---:|---:|
| `Geom.Core` | 3 | 3 |  |  |  |
| `Geom.Registration` | 20 | 20 |  |  |  |
| `Geom.Ledger` | 13 | 13 |  |  |  |
| `Geom.Exhaustion` | 37 | 37 |  |  |  |
| `Geom.Provision` | 25 | 25 |  |  |  |
| `Geom.Bounce` | 17 | 17 |  |  |  |
| `Geom.Profile` | 7 | 7 |  |  |  |
| `Geom.Gradient` | 12 | 12 |  |  |  |
| `Geom.Totality` | 13 | 13 |  |  |  |
| `Geom.Freshness` | 19 | 19 |  |  |  |
| `Geom.Arc` | 8 | 8 |  |  |  |
| `Obs.AbstractMemory` | 1 | 1 |  |  |  |
| `Obs.AbstractThermo` | 10 | 6 |  | 4 |  |
| `Obs.EffectiveDynamics` | 15 | 13 | 1 | 1 |  |
| `Obs.Unlock` | 6 | 6 |  |  |  |
| `Obs.UnlockCompleteness` | 13 | 13 |  |  |  |
| `Obs.UnlockPricing` | 6 | 6 |  |  |  |
| `Obs.Recovery` | 21 | 19 | 2 |  |  |
| `Obs.CausalOrder` | 24 | 22 | 2 |  |  |
| `Obs.Dimension` | 15 | 13 | 2 |  |  |
| `Obs.Selection` | 69 | 69 |  |  |  |
| `Obs.StochasticUnlock` | 54 | 54 |  |  |  |
| `Obs.StochasticThermo` | 14 | 14 |  |  |  |
| `Obs.StochasticDivergence` | 8 | 8 |  |  |  |
| `Obs.Budget` | 10 | 10 |  |  |  |
| `Obs.ContinuumUnlock` | 5 | 5 |  |  |  |
| `Obs.EmbeddedObserver` | 9 | 9 |  |  |  |

## `formal/bridge/`

| Module | results | clean | propext | propext + Quot.sound | declared |
|---|---:|---:|---:|---:|---:|
| `Alphabet` | 7 | 7 |  |  |  |
| `Capacity` | 13 | 9 | 4 |  |  |
| `OneZ2` | 11 | 11 |  |  |  |
| `RegistrationSpine` | 8 | 8 |  |  |  |
| `TickSimulation` | 21 | 17 | 4 |  |  |
| `Environment` | 15 | 15 |  |  |  |
| `Dil` | 74 | 26 | 40 | 5 |  |
| `RegistrationFactor` | 11 | 11 |  |  |  |
| `ArchiveMustSpeak` | 5 | 5 |  |  |  |
| `PageShape` | 11 | 5 | 6 |  |  |
| `SecondLaw` | 5 | 5 |  |  |  |
| `Measurement` | 5 | 5 |  |  |  |
| `BranchMeasure` | 14 | 6 | 8 |  |  |
| `Expansion` | 14 | 14 |  |  |  |
| `Forman` | 21 | 21 |  |  |  |
| `Saturation` | 5 | 5 |  |  |  |
| `EinsteinSkeleton` | 14 | 10 | 4 |  |  |
| `EffectiveMatter` | 15 | 15 |  |  |  |
| `FluxPattern` | 10 | 10 |  |  |  |
| `LedgerSheaf` | 19 | 19 |  |  |  |
| `RecombinationBudget` | 7 | 2 | 5 |  |  |
| `PhaseEToys` | 14 | 5 | 9 |  |  |
| `Period2KMS` | 7 | 5 | 2 |  |  |
| `ModularCut` | 8 | 5 | 3 |  |  |
| `LorentzianDict` | 5 | 5 |  |  |  |
| `TwoBounce` | 54 | 17 | 12 |  |  |
| `BridgeArc` | 41 | 24 | 14 | 2 |  |

## `formal/dictionary/`

| Module | results | clean | propext | propext + Quot.sound | declared |
|---|---:|---:|---:|---:|---:|
| `Certificate` | 4 | 4 |  |  |  |
| `LCertificate` | 2 | 2 |  |  |  |
| `Quintom.Kernel` | 8 | 8 |  |  |  |
| `Quintom.Certificate` | 8 | 8 |  |  |  |
| `Quintom.FixedPoint` | 5 | 5 |  |  |  |
| `Quintom.Damping` | 3 | 3 |  |  |  |
| `Quintom.Growth` | 10 | 1 | 9 |  |  |
| `BitFlip` | 10 | 10 |  |  |  |
| `Kramers` | 14 | 14 |  |  |  |
| `Page` | 10 | 10 |  |  |  |
| `QEC` | 7 | 7 |  |  |  |
| `NoClone` | 11 | 11 |  |  |  |
| `MetaProblem` | 11 | 9 | 2 |  |  |

Totals: 1305 audited results; 1115 clean.

