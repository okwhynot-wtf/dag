# Ledger (Archive Geometry in DAG)

Layer 1. Resource accounting over the spine. Vendored from AG `lean/Geom`
and `lean/Obs` (corpus v1.3.0), package version `2.0.0-dag`.

## Interfaces consumed (I-1)

Spine exports used by the bridge (not re-postulated here):
arena, `IsFundamental`, seal, ladder (`lift_injective` / `lift_conservative`),
non-commencement, branch modality, stage tags.

## Interfaces supplied (I-3)

Registration, exhaustion bound, profile constructors (`flat` / `expand` /
`bounce`), address, order dimension 1, capacity growth law.

## I-2 identification (in bridge, not re-axiomatised here)

- `E` at horizon `T` := `Ladder.Level T`
- `|caps T|` := `Density.predicateCount T = 2^(T+2)`
- committed ladder := `Geom.Profile.expand`
- eternal aliveness at `K = 2` is arithmetic: `2^T ≤ 2^(T+2)`

## Symbolic summary

See `docs/LEDGER_SYMBOLIC.txt`.
