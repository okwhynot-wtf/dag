# Plan: matter as saturated record flux

**Hypothesis (H).** Matter is an emergent, effective description of the
record flux that a bounded, lossless ledger is forced to emit at (or
toward) capacity saturation — not an independently generated substance.

**Anti-hypothesis (H⊥).** Matter requires a second generator: stress data
that cannot be recovered from registration / saturation bookkeeping alone.

This plan tests H without claiming electrons-from-Bool or continuum GR.
Pass/fail is combinatorial and Lean-shaped where possible; continuum
identifications stay refused.

Related: T-15 (saturation EoS), T-16 (discrete `G ~ T`), O-3 stalks,
R-1 recombination budget, combinatorial `T` caricature.

---

## 0. Definitions to lock first (Phase A — definitional Lean)

Make the hypothesis *stateable* before arguing it.

| ID | Deliverable | Pass criterion |
|---|---|---|
| A1 | `EffectiveMatter` := saturated (or near-saturated) record flux on a `LocalLedgerPatch` | Definition compiles; equals `stressProxy` at saturation (reuse T-16) |
| A2 | `VacuumPatch` := Inj ∧ ¬Merges ∧ ¬Registers (oscillator / H=0 class) | Proved: stressProxy = 0 / no forced flux |
| A3 | `MatterBearingPatch` := Merges ∧ Registers with `Saturated` (or unpaid capacity debt) | Proved: stressProxy = capacityProxy at saturation |
| A4 | Glossary note in symbolic law: matter-reading vs matter-as-input (two glosses of one skeleton) | Docs only; no theorem renumbering |

**Falsifier at A.** If vacuum and matter-bearing patches are not cleanly
separable in existing Registration/Budget language, H is ill-posed for DAG.

---

## 1. Necessity tests (Phase B — “forced to emit”)

H needs: bounded + lossless + sustained merge ⇒ flux (already near T-10/T-11).
Sharpen toward an effective-matter reading.

| ID | Question | Lean target | Pass / fail |
|---|---|---|---|
| B1 | Does eternal mute merging contradict bounded caps? | Re-export T-10 as `no_bounded_lossless_mute_matterlessness` | Pass if theorem holds (already does); fail only if hypotheses are judged too strong |
| B2 | Is registration the *only* stress channel? | Prove: under Inj, Merges ↔ Registers (Landauer direction already); seek converse fragments or countermodels | Pass if every Registers witness yields nonzero stressProxy on a finite fiber; fail if Registers with empty effective flux exists under the defs |
| B3 | Saturation ⇒ flux fixed by capacity schedule | T-15 / `stress_eq_capacity_at_saturation` | Already green — cite as B3 discharged |
| B4 | Below saturation, is “matter” optional? | Theorem: ¬Saturated → ∃ slack in alphabet unused | Pass if slack lemma holds; supports “matter = pressure at the bound,” not “any record” |

**Falsifier at B.** A bounded lossless mute universe with sustained merges
and zero records would kill H. (T-10 says this cannot happen.)

---

## 2. Geometry couples to flux (Phase C — `G ~ T` as emergence)

If matter *is* flux, curvature bookkeeping must answer to records.

| ID | Question | Lean target | Pass / fail |
|---|---|---|---|
| C1 | Unpaid Forman flatness decreases exactly by registered faces | `face_pays_one` + `curvature_relief_costs_records` (T-16) | Already green |
| C2 | Flatness budget vs aliveness budget | `recombinationsNeeded (degU,degV) ≤ alivenessBudget T` — quantitative R-1 | Pass if inequality stated and checked on Kmin tree; fail if budget systematically insufficient (interesting negative result) |
| C3 | Vacuum patches do not pay faces | Oscillator class ⇒ no registration ⇒ unpaid flatness unchanged by that channel | Pass if formalized; supports “no matter ⇒ no curvature relief” |
| C4 | Local stalks: flux defined per branch locus | Extend `LocalLedgerPatch` with `effectiveMatter := stressProxy` | Pass if natural; prelude to O-3 |

**Falsifier at C.** If geometry’s Forman deficit can be cured without
records/faces, or if saturated flux never couples to the curvature ledger,
H’s geometric half fails.

---

## 3. Effective inventory without a second substance (Phase D)

H does not require a unique particle spectrum. It requires that
*whatever* looks like content be pattern-in-flux.

| ID | Question | Attack | Pass / fail |
|---|---|---|---|
| D1 | Can distinct flux patterns be typed without new ontology? | Define `FluxPattern` from alphabet partitions / fiber labels already in E | Pass if ≥2 nondegenerate patterns exist on finite toys |
| D2 | Does branch width supply “species-like” multiplicity? | Kmin children as channel index; link to OneZ2 faces | Pass if a dictionary lemma ties channels to flux components; fail if forced unique pattern |
| D3 | Quintom damping as flux onset | Exhibit + skeleton: H=0 ↔ vacuum class; H>0 ↔ merge⇒record | Pass if T-5/T-6 reading restated as vacuum/matter onset (mostly docs + existing Lean) |

**Falsifier at D.** If every saturated patch has indistinguishable flux
(no pattern structure), “effective matter” is only a scalar pressure —
still interesting, but weaker than a contents-ontology.

---

## 4. Optional physics toys (Phase E — not required for H)

Only after A–C are green. Still discrete/finite.

| ID | Toy | Aim |
|---|---|---|
| E1 | Combinatorial `T_c := ΔS` with `S = log₂ ‖caps‖` (Nat log caricature) | Clausius-shaped `δQ ~ T ΔS` using record count as heat |
| E2 | Finite-mode Page toy: archive speech = matter/radiation channel | Effective radiation as forced post-exhaustion flux |
| E3 | Discrete Friedmann-shaped update: `capacityOf` evolution sourced by saturated flux | No continuum; no H₀ identification |

**Falsifier at E.** Toys can fail without killing H; they only test whether
H generates familiar *names* (temperature, radiation, expansion).

---

## 5. What we will not test (still refused / structural)

- Continuum `T_{μν}` or Standard Model from Bool
- Observable cosmological numbers / seconds
- Unruh temperature from boosts (O-2) — unless a combinatorial `T` suffices
- Qualia / hard problem (seal/self-opacity may stay as structural reports only)

---

## 6. Suggested order and stop rules

```
A (defs) → B (necessity) → C (geometry) → D (patterns) → E (toys)
```

| Stop rule | Action |
|---|---|
| Fail A | Hypothesis ill-posed; revise defs or drop |
| Fail B | H false in DAG; keep matter-as-input |
| Fail C | H may be thermodynamic but not geometric; split claims |
| Pass A–C, weak D | Promote “matter = saturated flux (scalar)” to not-residue reading; species-structure open |
| Pass A–D | Update RESIDUE: O-5 reframed as emergent-flux programme; matter-as-input demoted to optional host API |
| E results | Interpretation only until Lean toys land |

---

## 7. Doc / ledger updates when phases land

- `docs/RESIDUE.md`: move “matter-as-input” under a dual entry —
  *host API* vs *emergent flux hypothesis (under test)*.
- `docs/INTERPRETATION.md`: short “matter reading” section, hedged until A–C pass.
- `docs/DAG_SYMBOLIC.txt`: gloss line only after B3+C1 cited as package
  (e.g. under T-16 or a new T-17 if a package theorem earns it).
- Do **not** retitle anything “Einstein” or “Standard Model.”

---

## 8. First concrete sprint — **discharged**

Landed in `formal/bridge/EffectiveMatter.lean`:
- **A1–A3** `effectiveMatter`, `VacuumDynamics`, `MatterBearingTick`;
  `vacuum_vs_matter_channel_separable`
- **B4** `slack_below_saturation`
- **C2** `kmin_flatness_within_caps_budget` / `kmin_flatness_within_expand_budget`
- Package: `effective_matter_sprint`; milestone in `BridgeArc`
- INTERPRETATION “Matter reading” section updated

**Result:** H is Lean-testable. A did not fail (defs bear weight). Proceed to
Phase D (flux patterns) and O-3 glue; do not promote H to not-residue until
stop rules say so.
