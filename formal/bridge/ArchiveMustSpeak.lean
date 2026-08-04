import Geom.Provision
import Geom.Exhaustion
import Geom.Profile
import Geom.Bounce
import Alphabet

/-!
# T-10 The archive must speak

Named corollary of AG necessity: bounded confinement + Inj + sustained
merging ⇒ stream muteness fails at a finite tick.

This is the qualitative Page curve. A finite black hole (bounded
`|caps|`) cannot keep radiation informationless forever; past the
exhaustion tick the archive must speak into the stream.

Physics reading (dictionary, not Lean gravity):
  Inj(U)              ↔ unitarity of evaporation
  K-fold merge        ↔ no-hair coarse-graining
  StreamMute forever  ↔ exactly thermal Hawking radiation
  |caps T|            ↔ Bekenstein–Hawking capacity
  aliveness           ↔ entropy bound
  t_exh               ↔ Page time
  archive on ascent   ↔ Hayden–Preskill decoding

Hawking 1976 asserts eternal mute merging; Registration + T-10 is the
unitarist reply. Contrapositive of
`Geom.Provision.eternal_aliveness_needs_expansion`.
-/

namespace Bridge.ArchiveMustSpeak

/-- **T-10.** Bounded capacity, Inj, sustained K-merges, and confinement
    jointly force a tick at which StreamMute fails (the stream
    distinguishes a merged datum). Direct package of
    `Geom.Provision.no_static_eternal_aliveness`. -/
theorem archive_must_speak
    {S Eout Eint : Type} [DecidableEq Eout] [DecidableEq Eint]
    (U : S × Eout × Eint → S × Eout × Eint)
    (σ : Nat → S) (es : Nat → List Eout) (caps : Nat → List Eint)
    (hU : Geom.Exhaustion.Inj U) {K C : Nat} (hK : 2 ≤ K)
    (hm : ∀ t, Geom.Exhaustion.MergesAt U σ es caps t)
    (hc : ∀ t, Geom.Exhaustion.Confined U σ es caps t)
    (hdes : ∀ t, Geom.Exhaustion.Distinct (es t))
    (hKlen : ∀ t, K ≤ (es t).length)
    (hbound : ∀ t, (caps t).length ≤ C)
    (i₀ : Eint) (hi₀ : i₀ ∈ caps 0) :
    ∃ t, t < C ∧ ∃ e, e ∈ es t ∧ ∃ e', e' ∈ es t ∧
      ∃ i, i ∈ caps t ∧ ∃ i', i' ∈ caps t ∧
        (U (σ t, e, i)).2.1 ≠ (U (σ t, e', i')).2.1 :=
  Geom.Provision.no_static_eternal_aliveness
    U σ es caps hU hK hm hc hdes hKlen hbound i₀ hi₀

/-- Profile form: on a bounce, the exhaustion tick is the turnaround —
    Page time of the undirected schedule. -/
theorem page_time_is_exhaustion {K : Nat} (hK : 2 ≤ K) (tTurn : Nat) :
    Geom.Profile.IsExhaustionTick K (Geom.Profile.bounce tTurn) tTurn :=
  Geom.Profile.bounce_exhaustion_tick hK tTurn

/-- Before exhaustion, mute is consistent with aliveness on the bounce;
    at `tTurn`, T-10's horizon is reached (qualitative Page curve). -/
theorem thermal_window_then_speech
    {K : Nat} (hK : 2 ≤ K) (tTurn : Nat) :
    (∀ T, T ≤ tTurn → Geom.Profile.Alive K (Geom.Profile.bounce tTurn) T) ∧
    Geom.Profile.IsExhaustionTick K (Geom.Profile.bounce tTurn) tTurn :=
  ⟨fun T hT => (Geom.Profile.bounce_alive_iff hK tTurn T).mpr hT,
   page_time_is_exhaustion hK tTurn⟩

/-- Contrapositive: eternal mute ⇒ unbounded caps (already AG). -/
theorem eternal_mute_needs_unbounded
    {S Eout Eint : Type} [DecidableEq Eint]
    (U : S × Eout × Eint → S × Eout × Eint)
    (σ : Nat → S) (es : Nat → List Eout) (caps : Nat → List Eint)
    (hU : Geom.Exhaustion.Inj U) {K : Nat} (hK : 2 ≤ K)
    (hm : ∀ t, Geom.Exhaustion.MergesAt U σ es caps t)
    (hf : ∀ t, Geom.Exhaustion.FreshAt U σ es caps t)
    (hc : ∀ t, Geom.Exhaustion.Confined U σ es caps t)
    (hdes : ∀ t, Geom.Exhaustion.Distinct (es t))
    (hKlen : ∀ t, K ≤ (es t).length)
    (i₀ : Eint) (hi₀ : i₀ ∈ caps 0) :
    ∀ C : Nat, C < (caps C).length :=
  Geom.Provision.eternal_aliveness_needs_expansion
    U σ es caps hU hK hm hf hc hdes hKlen i₀ hi₀

/-- **T-10 package.** Archive must speak + Page time = exhaustion + Kmin. -/
theorem T10_archive_must_speak :
    (∀ {K : Nat}, 2 ≤ K → ∀ tTurn,
      Geom.Profile.IsExhaustionTick K (Geom.Profile.bounce tTurn) tTurn) ∧
    (∀ {K : Nat}, 2 ≤ K → ∀ tTurn,
      (∀ T, T ≤ tTurn → Geom.Profile.Alive K (Geom.Profile.bounce tTurn) T) ∧
      Geom.Profile.IsExhaustionTick K (Geom.Profile.bounce tTurn) tTurn) ∧
    Bridge.Alphabet.Kmin = 2 :=
  ⟨fun hK tTurn => page_time_is_exhaustion hK tTurn,
   fun hK tTurn => thermal_window_then_speech hK tTurn,
   Bridge.Alphabet.Kmin_eq⟩

#print axioms archive_must_speak
#print axioms page_time_is_exhaustion
#print axioms thermal_window_then_speech
#print axioms eternal_mute_needs_unbounded
#print axioms T10_archive_must_speak

end Bridge.ArchiveMustSpeak
