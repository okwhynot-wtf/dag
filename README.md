# Diagonal Archive Geometry (DAG)

Hybrid corpus: **Diagonal Monism** (spine) + **Archive Geometry** (ledger)
+ **re-entrant / quintom** dictionary entry.

Spec: [`docs/DAG.md`](docs/DAG.md) (copy of `DAG_spec.md`).

## Layers

```
Layer 2  DICTIONARY   formal/dictionary + exhibits/quintom
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
| T-3 | Alphabet `K = 2` minimal | Discharged (`Alphabet.lean`) |
| T-7 | One ℤ/2, three faces | Discharged (`OneZ2.lean`) |
| T-9 | Capacity dictionary | Discharged (`Capacity.lean`) |
| T-4 | Registration on spine | Discharged (`RegistrationSpine.lean`) |
| T-5 | Oscillator triangle (kernel) | Discharged (`Quintom/Kernel.lean`); ODE exhibit |
| T-8 | Fixed-point discipline (kernel) | Discharged (`Quintom/FixedPoint.lean`); ODE exhibit |
| T-6 | Damping = registration | Kernel skeleton (`Quintom/Damping.lean`); H-id exhibit |
| T-2 | Tick simulation | Fragment (`TickSimulation.lean`); full UP open |
| T-1 | Environment universality | Fragment (`Environment.lean`); full UP open |

## Sources

- Spine: `manic_output/absolute` (`formal/spine`)
- Ledger: `xnotx-container/geometry-main` (`lean/Geom`, `lean/Obs`)
- Dictionary RE: specified in `DAG_spec.md`; kernel formalised here

## Version

DAG hybrid **v0.1.0** — M1–M3 filed; M4–M5 fragments + residue documented.
