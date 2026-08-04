# Architecture

The `formal/spine/` package is the formal development. This document
maps modules, the derivation chain, and limits.

## Chain

```
Canon (initial object):
  ambient = pointed SymmetricStep acts with pointed equivariant maps
  (motivated by Orbit.classification_at: intrinsic direction excluded).
  Initiality — (Bool, not, true) is initial (canon_initial)
  Fundamentality — IsFundamental := unoriented + initial-map iso at a seed
                  (equivalent to Draws ∧ SymmetricStep ∧ Generated
                   by isFundamental_iff_clauses)
  Existence   — the initial object is fundamental (canon_is_fundamental)
  Uniqueness  — any two fundamentals correspond uniquely, constructively
                  (fundamental_correspondence); every fundamental reads as the
                  canon (every_fundamental_reads_as_canon)
  Elimination — rival shapes excluded (elimination)
  "The Fundamental" names the initial object (Canon.theFundamental), after
  uniqueness. Liveness, losslessness, Draws, Generated are derived
  (IsFundamental.live, .lossless, .sustains, .exhaustive).
  Contestable: ambient adequacy — whether pointed unoriented acts are
  the right setting for fundamentality.
  Compatibility readings: Monism.FundamentalReading, Apophasis.ApophaticReading,
  Canon.toReading / ofReading.
        │
Classification (Orbit.classification_at, Orbit.two_cycle)
    Pointwise classification — exhaustive and mutually exclusive: at
    every state an act rests (stagnation, rest_is_stagnation), closes
    a two-cycle (two_cycle_at), or carries an arrow
    (arrow_of_not_involutive). Erasure is the pairwise defect
    (erasing_forever); collision-free orbits embed ℕ with successor
  structure (no_collision_forces_arrow). Mixed acts (involutions with
    fixed points) are classified state by state.
    ⇒ order two derived; involutivity = symmetry of the step relation
      (symmetricStep_iff_involutive)
    void_is_excluded_fixed_point / fixed_point_refutes_liveness —
      named restatements of Live as fixed-point-freeness
        │
Reading (TwoCycle)
    canonical Bool coordinates; act reads as ¬ (act_reads_as_not);
    pointed reading unique; exactly two unpointed readings (two models,
    relabelings); witnessed_fundamental; bool_fundamental, coproduct_fundamental
    pole_swap_automorphism / poles_indiscernible — negation is an
      equivariant bijection of the canon; swap-invariant predicates
      cannot separate the poles
        │
Seal (Diagonal.seal_on_fundamental)
    liveness read diagonally (Lawvere): no system point-surjects onto
    its own fundamental-valued predicates; escape exhibited as the act
    applied to the self-reading (dodgeWith); no epistemic axioms
        │
Tower (Tower)
    NamingExtension — names an arbitrary unrepresented escape
      (Lawvere dodge via of_dodge); growth from unrepresentation
    arrow_placement — the fundamental's step returns; no naming extension
      re-enters its level
    no_settling — no final level
    underdetermined_at_two — ≥ 2 Bool escapes on any decidable carrier
      with two points; underdetermined_at_fundamental specialises to Bool
    first_emanation / first_step_underdetermined — default dodge naming
      and two distinct first emanations from underdetermination
        │
Ladder (Ladder)
    ω-tower: Level 0 = the Fundamental; each tick adjoins the namer of the
    previous level's dodge; history embeds injectively and
    conservatively (lift_injective, lift_conservative); no earlier
    level exhausts a later one (ladder_ascends). Underdetermination at
    every level (underdetermined_at_level). Duration = the order-type
    of self-escape, realised as an ω-sequence
        │
Cause (Cause)
    determination (same_cause_same_effect); exact transmission on the
    lossless fundamental (transmission_exact, fundamental_faithful; erasure breaks
    transmission); causal asymmetry = temporal arrow (causal_asymmetry);
    intervention (stepEsc / step); Policy / EscapePolicy varies free
    values and which escape is named (escapeAt, escapes_differ_at,
    escape_policy_changes_history); committed ladder = dodgePolicy
        │
Branch (Branch)
    escape tree; Nec/Poss over children; committed path = dodge ladder;
    ascent_necessary_direction_free; Canon.modal_of_fundamental
        │
Limit (Limit)
    first-appearance ω-colimit (no Quot); limit_sealed; ω+1 naming
    extension; no_ordinal_settling on the ω-tail
        │
Revision / SEM (comparative)
    Revision — liar revision ↔ not-orbit; ladder tick = revision step
    SEM — toy SCM image; intervention_commutes; asymmetry_is_acyclicity
        │
Interior (Interior)
    self_opacity — dodge not articulated by any element
    outdated_portrait — naming extension mismatches prior portraits
    self_modeling_forces_restless — tracked ascription flips under the act
        │
Information + Observer (Information, Observer)
    fundamental is the bit (fundamental_is_one_bit); symmetry is conservation;
    seal is capacity deficit; ascent is information growth. Every ladder
    level self-represents (sealed, self-opaque, outrun); each tick's
    namer holds a determinate portrait of the past (observers_forced).
    Rich observers (memory, agency, unity) are characterized, not derived
        │
Density (Density)
    fundamental count 1 among 4 (fundamental_density, fundamentals_only_at_two);
    combinatorial live/endo counts (live_count_package; no Fintype card,
    no 1/e in Lean); partial articulation closed form
    (articulation_partial_sum, levelCard_eq);
    no_retraction — no injection Level (k+1) → Level k
        │
NonCommencement (NonCommencement)
    iterate_parity / fundamental_forgets_count — involutive iterates depend
      only on parity (recursive mod2; library Nat.mod lemmas carry
      propext in this toolchain)
    no_fundamental_below_two, fundamental_is_least — no rung below Level 0
    ladder_index_recoverable — cardinality recovers the ladder index
        │
OmegaDuration (OmegaDuration)
    optionNat_bijective, optionLevelOmega_bijective — Hilbert hotel on
      Nat and LevelOmega (Option-extension equinumerous with carrier)
    stage_tag_injective, appearsBy_recovers_stage — ancestry survives
    namer_new_at_omega — ω+1 namer still outside prior image
    omega_not_a_rung — colimit admits no injection into any finite level
    omega_duration_package — magnitude flatlines; ancestral clock continues
        │
SelfReference (SelfReference)
    junction: corpus↔corpus only (world / doc / git / host-logic refused)
    Lawvere semantic route; Gödel arithmetisation refused
    seal_self — every SelfReading misses its dodge
    deficit_count / deficit_vanishes — names ≪ predicates (Cantor measure)
    FairSchedule — flagged policy; completeness-in-limit is schedule-relative
    lag_theorem — finishing level-k portrait leaves larger silence ahead
    corpus_not_universal — □(sayable) ∧ ¬□(sayable now); ω ≠ rung
        │
Master (Monism.diagonal_monism) — one theorem; conjuncts from the same
modules. Zero-axiom footprint for the package.

Appendix: Faces — Cantor/Lawvere/temporal readings under three
apophatic namings; zero declared axioms.
```

## Limits

- **Worldly causation.** `Cause` derives determination, transmission,
  asymmetry, and intervention within representational dynamics. Whether
  worldly causation instantiates that structure is an interpretive
  question, parallel to the Fundamental reading; no probabilistic or
  physical claims are made.
- **Phenomenality.** `Interior` proves structural asymmetries
  (self-opacity, outdated portrait, monitored ascription). No claim
  about qualia; phenomenological reading is interpretive.
- **Instantiation.** That the Fundamental is a live, unoriented,
  generating act is `Monism.FundamentalReading` — a structure to
  instantiate, not an axiom. Retorsion defends liveness; regress
  arguments for unorientedness and generation are in prose.
- **Which escape.** Underdetermination exhibits ≥2 escapes at every
  ladder level; `Cause.escapes_differ_at` realises them as distinct
  well-formed histories. The committed ladder selects the dodge; the
  spine does not select a unique world-history.

## Verification

```bash
(cd formal/spine && lake build)     # all results, zero-axiom footprint
python formal/tools/gen_audit.py    # regenerate Audit.lean
bash   formal/tools/audit.sh        # regenerate formal/AXIOMS.md
```
