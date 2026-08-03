# Diagonal Archive Geometry (DAG)

Hybrid corpus: **Diagonal Monism** (spine) + **Archive Geometry** (ledger)
+ dictionary (quintom / BitFlip / Kramers / Page / MetaProblem)
+ measurement companion NoClone.

Spec: [`docs/DAG.md`](docs/DAG.md) (copy of `DAG_spec.md`).

## Layers

```
Layer 2  DICTIONARY   formal/dictionary + exhibits/*
Layer 1  LEDGER       formal/ledger     (AG Geom/Obs)
Layer 0  SPINE        formal/spine      (DM, unchanged)
```

Downward imports only. Bridge theorems live in `formal/bridge/`.

## One-line

The spine says why anything ticks; the ledger says what each tick costs and
where it is written; the dictionary shows at least one world-shaped thing
in which ticking, cost, and writing are all present. Frictionless, all three
collapse to the same two-beat oscillator.

## Verify

```bash
bash VERIFY.sh
```

Or piecemeal:

```bash
(cd formal/spine && lake build)
(cd formal/ledger && lake build)
(cd formal/bridge && lake build)
(cd formal/dictionary && lake build)
python exhibits/quintom/integrate.py
```

## Theorem status

| ID | Content | Status |
|---|---|---|
| T-3 | Alphabet `K = 2` minimal | Discharged |
| T-7 | One ℤ/2, three faces | Discharged |
| T-9 | Capacity dictionary | Discharged |
| T-10 | Archive must speak (Page curve) | Discharged |
| T-11 | Combinatorial second law | Discharged (`SecondLaw.lean`) |
| T-12 | Outcome selection shape | Discharged (`Measurement.lean`) |
| T-13 | Expansion price of liveness (conditional) | Discharged (`Expansion.lean`); E1/E2 named; E3=R-1; E4 refused |
| T-14 | Forman–Ricci on branch tree | Discharged (`Forman.lean`); recombination raises toward flat |
| T-15 | Saturation / equation-of-state | Discharged (`Saturation.lean`); ledger balance fixes flux |
| T-16 | Discrete Einstein / Jacobson skeleton | Discharged skeleton (`EinsteinSkeleton.lean`); continuum GR refused (O-2 deepest) |
| T-4 | Registration on spine | Discharged |
| T-5 | Oscillator triangle (kernel) | Discharged; ODE exhibit |
| T-8 | Fixed-point discipline (kernel) | Discharged; ODE exhibit |
| T-6 | Damping = registration | Kernel skeleton; H-id exhibit |
| T-2 | Tick simulation | Committed path + namer factor; carrier obstructed |
| T-1 | Environment universality | Fiber UP done; arbitrary `U_S` open |

Dictionary (substantive order): Quintom → Kramers → Page → **MetaProblem**;
companions BitFlip, NoClone (measurement).

## Version

DAG hybrid **v0.1.9** — T-16 discrete Einstein / Jacobson skeleton;
realistic residue split (tractable open work vs genuine refusals).
