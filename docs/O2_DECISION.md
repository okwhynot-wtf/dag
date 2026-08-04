# O-2 decision — boost / Unruh temperature

**Status:** attempt completed; **feature verdict as finding**
(`Bridge.ModularCut.o2_cut_shift_dead_end`, `o2_forced_blindness`).

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

## Finding (forced blindness)

In the period-2 toy the temperature is set by the period, and the period
is a **global** datum of the dynamics; the cut only chooses where you
stand. Cut-dependent temperature would require different observers to see
different modular flows, which requires the flows to form a family, which
requires a one-parameter group. The corpus owns exactly one ℤ/2, so there
is exactly one flow — blindness was forced before the Unruh test began.

Read that way, `o2_cut_shift_dead_end` is close to a proof that **O-2 is
the statement “no continuous one-parameter subgroup exists.”** That is
also the prerequisite for **O-4**’s continuum Lorentzian limit. The two
structural problems are one missing object seen from two sides:

| Face | Missing object as… |
|---|---|
| O-2 | boost seen thermally (Unruh / modular `T`) |
| O-4 | boost seen geometrically (continuum Lorentzian limit) |

Any future attack on either automatically bears on both. Both reopen
conditions amount to the same demand: a continuous (or scale-indexed)
one-parameter family beyond the single ℤ/2.

Fence: not continuum KMS; not a Lorentz boost; not physical Unruh
temperature.

## Modest reopen route (low priority, tractable shape)

Within refusal discipline, one cut-adjacent dependence remains available
to a system with one ℤ/2 and no continuum limits: a **scale-indexed
family of coarse-grainings** over tick windows, asking whether effective
KMS temperature varies with window size — a discrete Tolman analogue
(temperature depending on scale of description, not cut position). That
is the shape any reopening would have to take; stating it makes the
fence around O-2 precise. Not scheduled; see `docs/RESIDUE.md`.
