import Obs.AbstractMemory

/-!
# Obs.EmbeddedObserver

Internal observers: stable kernels, hidden product structure, readout invisibility.
-/

namespace Obs.EmbeddedObserver

open Obs.AbstractMemory

/-- An internal observer is a readout of the same carrier X.
    Readable distinctions are exactly the fibres of `read`. -/
structure InternalObserver (X : Type) (Readout : Type) where
  read : X → Readout

/-- Kernel of the observer: same readable view. -/
def InternalObserver.kernelEq (obs : InternalObserver X Readout)
    (x y : X) : Prop :=
  obs.read x = obs.read y

/-- Kernel equality is reflexive. -/
theorem kernelEq_refl (obs : InternalObserver X Readout) (x : X) :
    obs.kernelEq x x :=
  rfl

/-- Kernel equality is symmetric. -/
theorem kernelEq_symm (obs : InternalObserver X Readout)
    {x y : X} (h : obs.kernelEq x y) : obs.kernelEq y x :=
  Eq.symm h

/-- Kernel equality is transitive. -/
theorem kernelEq_trans (obs : InternalObserver X Readout)
    {x y z : X}
    (hxy : obs.kernelEq x y) (hyz : obs.kernelEq y z) :
    obs.kernelEq x z :=
  Eq.trans hxy hyz

/-- Inscribing a verdict into the state (writing the observation back). -/
structure VerdictWrite (X : Type) (Verdict : Type) where
  write : X → Verdict → X

/-- **Verdict stability** (embedded A7).

    Recording a verdict into X does not change what the observer can
    read. The verdict slot lies outside the readable algebra — the
    mirror does not see its own inscription.

    Formally: `read ∘ write(·,v) = read` for every verdict `v`. -/
structure VerdictStable (X : Type) (Readout : Type) (Verdict : Type)
    (obs : InternalObserver X Readout)
    (vw : VerdictWrite X Verdict) where
  stable :
    ∀ (x : X) (v : Verdict), obs.read (vw.write x v) = obs.read x

/-- Stability preserves kernel equivalence under arbitrary inscription. -/
theorem stable_preserves_kernel
    {X Readout Verdict : Type}
    (obs : InternalObserver X Readout)
    (vw : VerdictWrite X Verdict)
    (vs : VerdictStable X Readout Verdict obs vw)
    {x y : X} (h : obs.kernelEq x y) (v : Verdict) :
    obs.kernelEq (vw.write x v) (vw.write y v) := by
  unfold InternalObserver.kernelEq at *
  calc
    obs.read (vw.write x v) = obs.read x := vs.stable x v
    _ = obs.read y := h
    _ = obs.read (vw.write y v) := Eq.symm (vs.stable y v)

/-- Writing the observer's own readout as verdict. -/
def writeOwnReadout {X Readout : Type}
    (vw : VerdictWrite X Readout) (obs : InternalObserver X Readout)
    (x : X) : X :=
  vw.write x (obs.read x)

/-- Own-readout inscription is invisible when verdict-stable. -/
theorem own_readout_invisible
    {X Readout : Type}
    (obs : InternalObserver X Readout)
    (vw : VerdictWrite X Readout)
    (vs : VerdictStable X Readout Readout obs vw)
    (x : X) :
    obs.read (writeOwnReadout vw obs x) = obs.read x :=
  vs.stable x (obs.read x)

/-- Product splitting: visible × hidden, read = left projection.
    The natural embedded observer when a product structure exists. -/
def productObserver (V H : Type) : InternalObserver (V × H) V where
  read := fun p => p.1

/-- Verdict written into a hidden register (third factor style via H).
    `write (v,h) verdict` updates only the hidden component. -/
def hiddenVerdictWrite (V H Verdict : Type)
    (update : H → Verdict → H) :
    VerdictWrite (V × H) Verdict where
  write := fun p ver => (p.1, update p.2 ver)

/-- Product observers are verdict-stable when the verdict lands in H. -/
theorem product_verdict_stable (V H Verdict : Type)
    (update : H → Verdict → H) :
    VerdictStable (V × H) V Verdict
      (productObserver V H) (hiddenVerdictWrite V H Verdict update) where
  stable := fun _ _ => rfl

/-- Lift an ordinary causal-record readout to an internal observer. -/
def InternalObserver.ofRead {X Readout : Type}
    (read : X → Readout) : InternalObserver X Readout where
  read := read

/-- Causal-record self-blindness supplies an internal observer on X. -/
def InternalObserver.ofCausalRecordSystem {X Content Readout : Type}
    (C : CausalRecordSystem X Content Readout) : InternalObserver X Readout where
  read := C.selfBlind.read

/-!
# Obs.EmbeddedObserver

Internal observers: stable kernels, hidden product structure, readout invisibility.
-/

/-- Read-closure under a step (same Prop as Obs.EffectiveDynamics.ReadClosed). -/
def ReadClosedStep {X Readout : Type}
    (step : X → X) (read : X → Readout) : Prop :=
  ∀ x y : X, read x = read y → read (step x) = read (step y)

/-- ∀-form of micro-factoring through read. -/
def StepFactorsRead {X Readout : Type}
    (step : X → X) (read : X → Readout) : Prop :=
  ∀ x y : X, read x = read y → step x = step y

/-- **Stable internal observer**: internal readout, read-closed under `step`,
    and verdict-stable inscription on the same carrier. -/
structure StableInternalObserver (X : Type) (Readout : Type) (Verdict : Type)
    (step : X → X) where
  obs : InternalObserver X Readout
  vw : VerdictWrite X Verdict
  readClosed : ReadClosedStep step obs.read
  verdictStable : VerdictStable X Readout Verdict obs vw

/-- Product step that updates only the hidden coordinate. -/
def productHiddenStep (V H : Type) (phi : H → H) (p : V × H) : V × H :=
  (p.1, phi p.2)

/-- Product observers are read-closed under hidden-only steps. -/
theorem product_hidden_readClosed (V H : Type) (phi : H → H) :
    ReadClosedStep (productHiddenStep V H phi) (productObserver V H).read := by
  intro x y h
  -- read = π₁; step keeps first component
  simp only [productHiddenStep, productObserver] at *
  exact h

/-- Product splitting yields a stable internal observer. -/
def productStableInternalObserver (V H Verdict : Type)
    (phi : H → H) (update : H → Verdict → H) :
    StableInternalObserver (V × H) V Verdict (productHiddenStep V H phi) where
  obs := productObserver V H
  vw := hiddenVerdictWrite V H Verdict update
  readClosed := product_hidden_readClosed V H phi
  verdictStable := product_verdict_stable V H Verdict update

/-- If `phi` separates two hidden values, the product hidden step does not
    factor through `read = π_V`. -/
theorem product_hidden_step_not_factors
    {V H : Type} (phi : H → H) (v : V)
    {h₁ h₂ : H} (hne : phi h₁ ≠ phi h₂) :
    ¬ StepFactorsRead (productHiddenStep V H phi) (productObserver V H).read := by
  intro hf
  have hs :
      productHiddenStep V H phi (v, h₁) =
        productHiddenStep V H phi (v, h₂) :=
    hf (v, h₁) (v, h₂) rfl
  simp only [productHiddenStep] at hs
  exact hne (congrArg Prod.snd hs)

/-- Existence/separation: a stable internal observer whose step does not
    factor through read (Bool × Bool, phi = not). -/
theorem exists_stable_internal_observer_not_factors :
    ∃ (step : Bool × Bool → Bool × Bool)
      (sio : StableInternalObserver (Bool × Bool) Bool Bool step),
      ¬ StepFactorsRead step sio.obs.read := by
  let phi : Bool → Bool := fun b => !b
  let update : Bool → Bool → Bool := fun _ v => v
  let step := productHiddenStep Bool Bool phi
  let sio := productStableInternalObserver Bool Bool Bool phi update
  refine ⟨step, sio, ?_⟩
  exact product_hidden_step_not_factors phi true (by decide : (!false) ≠ (!true))

end Obs.EmbeddedObserver

/- axiom footprint -/
#print axioms Obs.EmbeddedObserver.stable_preserves_kernel
#print axioms Obs.EmbeddedObserver.own_readout_invisible
#print axioms Obs.EmbeddedObserver.product_verdict_stable
#print axioms Obs.EmbeddedObserver.product_hidden_readClosed
#print axioms Obs.EmbeddedObserver.product_hidden_step_not_factors
#print axioms Obs.EmbeddedObserver.exists_stable_internal_observer_not_factors
