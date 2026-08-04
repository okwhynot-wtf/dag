# JMP paper draft — internal notes

Target: *Journal of Mathematical Philosophy* (MCMP / LMU, 2026).
Draft source: `jmp_draft.tex` (anonymized for double-anonymous review).

## Journal fit

| Criterion | Status |
|---|---|
| Scope includes formal metaphysics | **Fits** — core of the draft |
| Serious academic philosophy + formal methods | **Fits** — theorems with metaphysical reading |
| Anonymized PDF at submission | Draft has no author/affiliation; strip PDF metadata before submit |
| Open formatting at initial submission | Plain `article` LaTeX OK; JMP template only after acceptance |
| Length: as long as the argument requires | Target ~3500 words (range 2–5k) |
| Diamond OA, no APC | Relevant for later, not structure |

Desk risk if the draft reads as a physics programme or a Lean engineering report.
The draft therefore leads with **formal metaphysics**, treats the ledger/dictionary as a controlled extension, and states refusals explicitly.

## Strengths the structure is built to show

### Individual

1. **Canon / fundamentality** — `(Bool, ¬)` initial among pointed involutive acts; uniqueness up to label swap.
2. **Seal** — Lawvere-style incompleteness on the arena (no point-surjection onto self-readings); no Gödel arithmetisation.
3. **One ℤ/2, three faces** — pole / address / channel as one underdetermination.
4. **Losslessness theorem** — involution ⇒ ¬erase (in-arena).
5. **I-1 two-bounce** — injective finite endomaps factor as two involutions; converse.
6. **Canonicity fails** — essential non-uniqueness of `(φ,σ)` (proved negative).
7. **Channel-swap = reversal** — exchange of factors covers `U ↦ U⁻¹` without canonical factors.
8. **Machine-checked** — Lean 4, no Mathlib, no `sorry`; axiom footprints audited.

### Overall

- A single **relational signature**: absolute channel/pole/direction positions are unreal; exchanges and relations are real.
- A usable **gauge demarcation** (content vs packaging) that protects the one-ℤ/2 claim against gauge-inflation objections.
- Honest **residue**: facticity of liveness and ambient adequacy remain philosophical, not smuggled into theorems.
- Architecture that **separates** a priori arena mathematics from dictionary instantiations (physics as certificate, not coronation).

## Recommended narrative arc (polish)

Classification → fundamentality (UP of survivor) → seal → ladder →
registration (two-bounce) → archive/capacity → arrow → one ℤ/2 + gauges →
dictionary → open/refused/philosophical.

Three layers kept strict: formal / interpretation / dictionary.
Negation presented as unique survivor of eliminative classification, not
an initial assumption.

## Build

```bash
cd paper && pdflatex jmp_draft.tex && pdflatex jmp_draft.tex
```

Before JMP upload: anonymize PDF metadata (`pdfinfo` / ExifTool); do not include this README in the submission zip unless stripped of identity cues.
