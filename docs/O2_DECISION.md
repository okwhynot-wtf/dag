# O-2 decision — boost / Unruh temperature

**Status:** attempt completed; **feature verdict as finding**
(`Bridge.ModularCut.o2_cut_shift_dead_end`).

## Attempt (KMS / cut-shift route)

Took the period-2 KMS toy and defined a saturated **system/archive cut**
(`SaturatedCut`) with left/right shift as the candidate modular flow /
boost analogue. Tested:

1. **KMS caricature at β = period = 2** — period-2 Bool correlators are
   stationary under `+β` (`kms_caricature_at_period`). Lands.
2. **Unruh test** — does cut position set temperature? **No.**
   `combinatorialTemp T = 1` for every cut; `areaBits T = T+2` depends
   only on the tick. Cut-shift preserves capacity partition but does not
   produce observer-dependent `T(cut)`.

## Finding

Absence of boosts / Unruh `T` is a property of the discrete skeleton
(one ℤ/2; constant combinatorial `T_c`), not a missing lemma. The
"feature, not bug" preference is now an **attempted result**: the natural
modular-flow candidate fails the Unruh coupling test inside the corpus.

Fence: not continuum KMS; not a Lorentz boost; not physical Unruh
temperature. Continuum Lorentzian (O-4) remains a separate open.

## Residual posture

O-2 stays **structural**. Reopening would need new structure (a
cut-dependent temperature or continuous modular parameter) beyond what
the present skeleton supplies — not another rephrasing of period-2.
