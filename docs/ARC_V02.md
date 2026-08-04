# Arc write-up — Dil → Registration-as-derived → Straightening → Classified T-2

Frozen at **DAG hybrid v0.2**. This is the self-contained story with a
beginning and an end. Later work (Born no-go, O-2 decision, O-3 Mathlib
sheaf, …) sits outside this arc.

## Beginning — Dil keystone

The environment is not an extra substance. Given a merging system map
`u : S → S`, Dil supplies the minimal archive restoring joint injectivity:

- free archive initial;
- capacity step from K-fold fibers;
- registration as corollary (merge forces record separation);
- minimal schedule at `K = 2` realises `|caps T| = 2^(T+2)`.

I-2 Fin closes under alphabet-UF (`boolCapsArchive`, `|E₀| = 4`): unique
factorization is the half-split bijection; rigidity is relative to a base
bijection — the record gauge torsor.

## Middle — Registration derived; straighten

Registration on the spine is no longer primitive-shaped: it falls out of
joint injectivity / Dil. Unique factorization then straightens every UF
archive to append-only form on a frozen base (`isoToFreeOnBase` /
`freeOnBase`). The freedom rigidity could not kill is exactly the freedom
straightening needs.

## End — Classified T-2

`Bridge.TickSimulation.tick_identification`:

- **Positive:** eternal UF-archive dynamics factor through naming extensions
  up to record gauge (straighten → append step → namer shape → rate weld →
  ladder `NamingExtension`).
- **Exempt:** periodic Fund / oscillator never demands a namer.
- **Necessity:** eternal `swapStep` registers forever on fixed `|E|=2` while
  `levelCard` climbs — the dichotomy is exhaustive; the eternal hypothesis
  cannot be dropped.

Fence: not a total functor `Registers U → NamingExtension` on arbitrary
carriers. Naming-tick ↔ microtick is a theorem on the classified remnant,
not a modelling license.

## What changed in the symbolic law

- **§0:** `(identified only where T-2 licenses)` → citation of
  `tick_identification`.
- **§V:** spine/ledger columns proved under that citation; dictionary
  column stays K/L-certificate grade (I-4). Fund ≅ oscillator is the
  exempt pole; pred-growth ≅ caps doubling is the rate weld.
- **Corollary:** `time_dissipation_one_property` — undamped ⇒ no naming
  ticks; arrow iff registration (theorem for formal columns).

## Citations

| Piece | Declaration |
|---|---|
| Dil keystone | `Bridge.Dil.keystone_dil_sprint` |
| Registration derived | `Bridge.Dil.registration` |
| Straightening | `Bridge.Dil.straighten_fragment` / `isoToFreeOnBase` |
| Per-tick glue | `Bridge.TickSimulation.tick_identification_step` |
| Dichotomy | `Bridge.TickSimulation.tick_identification_dichotomy` |
| Classified T-2 | `Bridge.TickSimulation.tick_identification` |
| Arc weld | `Bridge.Arc.milestone_T2_tick_id` |
