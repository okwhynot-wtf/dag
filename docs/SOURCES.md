# Provenance

| Layer | Source path | Notes |
|---|---|---|
| Spine | `manic_output/absolute/formal/spine` | Copied unchanged (DM) |
| Ledger | `xnotx-container/geometry-main/.../lean/{Geom,Obs}` | AG v1.3.0 port; package `2.0.0-dag` |
| Spec | `hybrid/DAG_spec.md` → `docs/DAG.md` | Authoritative architecture |
| Dictionary RE | Spec §1 + §6 T-5/T-8 | No prior Lean corpus; kernel new here |

Vendored copies are snapshots for the hybrid. Upstream edits should be
re-synced deliberately; bridge/dictionary must not be edited into spine.
