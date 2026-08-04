import Quintom.Kernel
import Alphabet
import Capacity
import Dil
import Density

/-!
# RE-side growth law — mode-count ↔ capacity analogue

Discrete Fin caricature on the quintom channel alphabet relating predicate
growth, capacity doubling, and mode-count:

  modeCount(T) := |Channel|^(levelCard T) = 2^(T+2) = caps T
  modeCount(T+1) = Kmin · modeCount(T)

DESI / `w(z)` forecasts, continuum Fourier-mode creation, and
`H₀`-from-Bool are not claimed in this module. ODE envelope numerics in
`exhibits/quintom/integrate.py` illustrate H=0/H>0 damping and are not
evidence for this combinatorial identification. The growth law is
dictionary arithmetic on `Channel` × ladder depth.
-/

namespace Dictionary.Quintom.Growth

open Dictionary.Quintom
open Bridge

/-- Cardinality of the RE two-channel alphabet `{φ, σ}`. -/
def channelCard : Nat := 2

/-- Exhaustive two-element reading of `Kernel.Channel`. -/
theorem channel_is_two :
    (∀ c : Kernel.Channel, c = .phi ∨ c = .sigma) ∧
    Kernel.Channel.phi ≠ Kernel.Channel.sigma :=
  ⟨fun c => by cases c <;> first | exact Or.inl rfl | exact Or.inr rfl, by decide⟩

/-- Channel alphabet size equals the ledger minimal merge rate. -/
theorem channelCard_eq_Kmin : channelCard = Alphabet.Kmin := by
  simp [channelCard, Alphabet.Kmin_eq]

/-- RE mode-count at naming depth `T`: channel assignments on a carrier
    of size `levelCard T = T+2` (Bool base + one namer per tick).
    Discrete Fin stand-in for "modes grow with the arena," not QFT modes. -/
def modeCount (T : Nat) : Nat := channelCard ^ Density.levelCard T

theorem modeCount_eq (T : Nat) : modeCount T = 2 ^ (T + 2) := by
  simp [modeCount, channelCard, Density.levelCard_eq]

/-- Mode-count coincides with predicate / capacity ledger size. -/
theorem modeCount_eq_caps (T : Nat) :
    modeCount T = Capacity.caps T := by
  rw [modeCount_eq, Capacity.caps_eq]

/-- Mode-count coincides with spine predicate growth. -/
theorem modeCount_eq_predicateCount (T : Nat) :
    modeCount T = Density.predicateCount T := by
  rw [modeCount_eq, Density.predicateCount_eq]

/-- One-tick doubling: the RE face of `c(t+1) = K · c(t)` at `K = 2`. -/
theorem modeCount_doubles (T : Nat) :
    modeCount (T + 1) = 2 * modeCount T := by
  simp [modeCount_eq, Nat.pow_succ, Nat.mul_comm]

/-- Same doubling written with `Kmin`. -/
theorem modeCount_doubles_Kmin (T : Nat) :
    modeCount (T + 1) = Alphabet.Kmin * modeCount T := by
  simpa [Alphabet.Kmin_eq] using modeCount_doubles T

/-- Mode-count realises Dil's minimal K=2 schedule (capacity-law shape). -/
theorem modeCount_minimal_schedule :
    Dil.MinimalSchedule Alphabet.Kmin modeCount ∧
    modeCount 0 = 4 ∧
    ∀ T, modeCount T = Alphabet.Kmin ^ T * 4 := by
  refine ⟨?min, ?base, ?closed⟩
  · intro T
    simpa [Alphabet.Kmin_eq] using modeCount_doubles T
  · decide
  · intro T
    have h := (Dil.predicate_minimal_schedule).2.2 T
    -- predicateCount T = 2^T * 4, and modeCount = predicateCount
    simpa [modeCount_eq_predicateCount, Alphabet.Kmin_eq] using h

/-- Rate weld across three columns: pred growth ≅ caps doubling ≅ mode doubling. -/
theorem growth_rate_weld (T : Nat) :
    Density.predicateCount (T + 1) = 2 * Density.predicateCount T ∧
    Capacity.caps (T + 1) = 2 * Capacity.caps T ∧
    modeCount (T + 1) = 2 * modeCount T := by
  refine ⟨?pred, ?caps, modeCount_doubles T⟩
  · simp [Density.predicateCount_eq, Nat.pow_succ, Nat.mul_comm]
  · simp [Capacity.caps_eq, Nat.pow_succ, Nat.mul_comm]

/-- Scope markers: continuum forecast / mode-creation / H₀ claims are
    outside this module (same pattern as LorentzianDict). -/
def desi_forecast_refused : True := True.intro
def continuum_mode_creation_refused : True := True.intro
def H0_from_Bool_refused : True := True.intro

/-- **RE-side growth law.** Quintom mode-count ↔ capacity-law analogue:
    `modeCount T = caps T = 2^(T+2)` and doubles each naming tick at `Kmin`.
    Continuum DESI / Fourier-mode / `H₀` claims are outside this module. -/
theorem re_side_growth_law :
    (∀ T, modeCount T = Capacity.caps T) ∧
    (∀ T, modeCount T = Density.predicateCount T) ∧
    (∀ T, modeCount (T + 1) = Alphabet.Kmin * modeCount T) ∧
    Dil.MinimalSchedule Alphabet.Kmin modeCount ∧
    channelCard = Alphabet.Kmin ∧
    desi_forecast_refused = True.intro ∧
    continuum_mode_creation_refused = True.intro ∧
    H0_from_Bool_refused = True.intro ∧
    Alphabet.Kmin = 2 :=
  ⟨modeCount_eq_caps, modeCount_eq_predicateCount, modeCount_doubles_Kmin,
   modeCount_minimal_schedule.1, channelCard_eq_Kmin, rfl, rfl, rfl,
   Alphabet.Kmin_eq⟩

#print axioms channel_is_two
#print axioms modeCount_eq_caps
#print axioms modeCount_doubles
#print axioms growth_rate_weld
#print axioms re_side_growth_law

end Dictionary.Quintom.Growth
