# Page toy exhibit (black hole information paradox)

Finite Page-style model for the **L-certificate** dictionary entry.
Gravitational BH, semiclassical QFT, and island theorems remain **refused**
as Lean (`docs/RESIDUE.md`). The Lean kernel is in
`formal/dictionary/Page.lean`.

## Dictionary (physics → DAG)

| Physics | DAG |
|---|---|
| Unitarity of evaporation | `Inj(U)`, global bijectivity on S×E |
| No-hair (microstates → M, J, Q) | K-fold merge in `U_S` |
| Exactly thermal Hawking radiation | `StreamMute` sustained forever |
| Bekenstein–Hawking entropy | `|caps T|` |
| Entropy bound | aliveness, `K^T ≤ |caps T|` |
| Page time | `t_exh`, exhaustion tick |
| Hayden–Preskill decoding | archive recoverable on ascent |

Hawking 1976 = eternal mute merging. Registration + **T-10** ("archive must
speak") = unitarist reply. T-10 is the contrapositive of AG eternal mute ⇒
unbounded capacity: bounded confinement ⇒ mute fails at a finite tick.

## Kernel-side conjecture (not claimed)

Candidate I-4 / K-certificate involution: the **Hawking pair**. Each exterior
quantum has an interior partner; swapping the pair is an involution acting on
Killing frequency as `ω ↦ −ω`. Fixed locus = zero mode at the horizon; forced
+1 = the partner (purification: a single exterior quantum is not pure).

Clauses (a)–(d) have shapes, but making them exact needs Bogoliubov
machinery and drifts into the QFT refusal. Filed here as **conjecture only**.
The dictionary entry stands on its L-certificate without this involution.

## What is Lean vs exhibit

| Item | Status |
|---|---|
| `pageStep` / `swapStep` Inj + merge + record | Lean (`Page.lean`) |
| Bounce Page time = exhaustion | Lean (T-10 / Profile) |
| L-certificate admission | Lean |
| Full GR evaporating BH | Refused |
| Hawking-pair K-certificate | Conjecture only |
