import Obs.AbstractMemory
import Obs.AbstractThermo

/-!
# Obs.EffectiveDynamics

Effective dynamics: ReadClosed, iterate, historical stability.
-/

namespace Obs.EffectiveDynamics

open Obs.AbstractMemory
open Obs.AbstractThermo

/-- Read-closedness: equal readable views stay equal after one step. -/
def ReadClosed {X Readout : Type}
    (step : X → X) (read : X → Readout) : Prop :=
  ∀ x y : X, read x = read y → read (step x) = read (step y)

theorem readClosed_of_readClosure
    {X Readout : Type} (M : System X) (read : X → Readout)
    (rc : ReadClosure X Readout M read) :
    ReadClosed M.step read :=
  rc.closed

/-- Step is a function of the readout: ∃ lift, step = lift ∘ read. -/
structure FactorsThroughRead (X : Type) (Readout : Type)
    (step : X → X) (read : X → Readout) where
  lift : Readout → X
  factors : ∀ x : X, step x = lift (read x)

/-- Factoring ⇒ SelfBlindness.step_factors_read. -/
theorem step_factors_read_of_factors
    {X Readout : Type}
    {step : X → X} {read : X → Readout}
    (fr : FactorsThroughRead X Readout step read) :
    ∀ x y : X, read x = read y → step x = step y := by
  intro x y h
  calc
    step x = fr.lift (read x) := fr.factors x
    _ = fr.lift (read y) := congrArg fr.lift h
    _ = step y := Eq.symm (fr.factors y)

/-- Factoring ⇒ read-closed. -/
theorem readClosed_of_factors
    {X Readout : Type}
    {step : X → X} {read : X → Readout}
    (fr : FactorsThroughRead X Readout step read) :
    ReadClosed step read := by
  intro x y h
  have hs : step x = step y := step_factors_read_of_factors fr x y h
  exact congrArg read hs

/-- Dynamics that factor through `read` (readout protocol). -/
structure ReadoutProtocol (X : Type) (Readout : Type)
    (read : X → Readout) where
  step : X → X
  factors : FactorsThroughRead X Readout step read

/-- Booking + write-unread + readout-protocol step ⇒ NonInjective. -/
theorem protocol_noninjective
    {X Content Readout : Type}
    (bk : Booking X Content)
    (read : X → Readout)
    (proto : ReadoutProtocol X Readout read)
    (write_unread :
      ∃ c₁ c₂ : Content,
        c₁ ≠ c₂ ∧ read (bk.book c₁) = read (bk.book c₂)) :
    NonInjective proto.step := by
  let M : System X := ⟨proto.step⟩
  let sb : SelfBlindness X Content Readout M bk :=
    { read := read
      write_unread := write_unread
      step_factors_read := step_factors_read_of_factors proto.factors }
  exact noninjective_of_booking_selfblind M bk sb

/-- Booking + FactorsThroughRead ⇒ NonInjective. -/
theorem noninjective_of_booking_factors
    {X Content Readout : Type}
    (bk : Booking X Content)
    (read : X → Readout)
    (step : X → X)
    (fr : FactorsThroughRead X Readout step read)
    (write_unread :
      ∃ c₁ c₂ : Content,
        c₁ ≠ c₂ ∧ read (bk.book c₁) = read (bk.book c₂)) :
    NonInjective step :=
  protocol_noninjective bk read ⟨step, fr⟩ write_unread

/-- Write-unread + read-closed ⇒ equal booked successor readouts. -/
theorem observable_merge_of_write_unread_readClosed
    {X Content Readout : Type}
    (bk : Booking X Content)
    (step : X → X)
    (read : X → Readout)
    (hc : ReadClosed step read)
    {c₁ c₂ : Content}
    (_hne : c₁ ≠ c₂)
    (hread : read (bk.book c₁) = read (bk.book c₂)) :
    read (step (bk.book c₁)) = read (step (bk.book c₂)) :=
  hc (bk.book c₁) (bk.book c₂) hread

/-- Booked states remain distinct at write time. -/
theorem booked_states_ne
    {X Content : Type} (bk : Booking X Content)
    {c₁ c₂ : Content} (hne : c₁ ≠ c₂) :
    bk.book c₁ ≠ bk.book c₂ :=
  book_ne_of_ne bk hne

/-! ## Historical distinguishability (H_hist)

  Under read-closure the readout evolves by an induced map `g : R → R`
  (`read ∘ step = g ∘ read`). Then
    read(Fᵗ(book c)) = gᵗ(read(book c)),
  so the historical readout support is the ordinary image-size ledger of
  `g` on the initial booked readouts — hence non-increasing.
-/

/-- Iterate a self-map. -/
def iterate {α : Type} (f : α → α) : Nat → α → α
  | 0, x => x
  | n + 1, x => f (iterate f n x)

/-- Functional witness for read-closure: `read ∘ step = g ∘ read`. -/
structure InducedReadoutMap (X : Type) (Readout : Type)
    (step : X → X) (read : X → Readout) where
  g : Readout → Readout
  factors : ∀ x : X, read (step x) = g (read x)

/-- Induced readout map ⇒ read-closed (congruence / well-defined quotient). -/
theorem readClosed_of_induced
    {X Readout : Type}
    {step : X → X} {read : X → Readout}
    (ind : InducedReadoutMap X Readout step read) :
    ReadClosed step read := by
  intro x y h
  calc
    read (step x) = ind.g (read x) := ind.factors x
    _ = ind.g (read y) := congrArg ind.g h
    _ = read (step y) := Eq.symm (ind.factors y)

/-- Factoring through read supplies an induced readout map. -/
def induced_of_factors
    {X Readout : Type}
    {step : X → X} {read : X → Readout}
    (fr : FactorsThroughRead X Readout step read) :
    InducedReadoutMap X Readout step read where
  g := fun r => read (fr.lift r)
  factors := fun x => by
    rw [fr.factors x]

/-- Read-closure supplies an induced readout map, given a section of the
    readout (a representative state per readout value): set
    `g = read ∘ step ∘ sec`. In the finite models the section is a
    concrete table. -/
def induced_of_readClosed
    {X Readout : Type}
    {step : X → X} {read : X → Readout}
    (hc : ReadClosed step read)
    (sec : Readout → X) (hsec : ∀ r : Readout, read (sec r) = r) :
    InducedReadoutMap X Readout step read where
  g := fun r => read (step (sec r))
  factors := fun x => hc x (sec (read x)) (Eq.symm (hsec (read x)))

/-- **Quotient dynamics.** Given a section of the readout, read-closure
    is equivalent to the existence of an induced readout map: the cut is
    closed exactly when the readout is an autonomous dynamical system.
    Breaking closure therefore destroys the quotient dynamics, not merely
    one convenient map. -/
theorem readClosed_iff_induced
    {X Readout : Type}
    {step : X → X} {read : X → Readout}
    (sec : Readout → X) (hsec : ∀ r : Readout, read (sec r) = r) :
    ReadClosed step read ↔
      Nonempty (InducedReadoutMap X Readout step read) :=
  ⟨fun hc => ⟨induced_of_readClosed hc sec hsec⟩,
   fun ⟨ind⟩ => readClosed_of_induced ind⟩

/-- `read` after `t` micro-steps equals `g^t` on the initial readout. -/
theorem read_iterate_eq
    {X Readout : Type}
    {step : X → X} {read : X → Readout}
    (ind : InducedReadoutMap X Readout step read)
    (x : X) :
    ∀ t : Nat, read (iterate step t x) = iterate ind.g t (read x)
  | 0 => rfl
  | t + 1 => by
    rw [iterate, iterate, ind.factors, read_iterate_eq ind x t]

/-- Initial booked readout seed for the historical ledger. -/
def historicalSeed {X Content Readout : Type}
    (read : X → Readout) (book : Content → X)
    (contents : List Content) : List Readout :=
  contents.map fun c => read (book c)

/-- Counting carrier for \(H_{\mathrm{hist}}\): image sizes of the induced
    readout map on booked readouts. By `read_iterate_eq` this enumerates
    \(\{\mathsf{read}(F^t(\mathsf{book}(c)))\}\). -/
def historicalImageSizes {X Content Readout : Type} [BEq Readout]
    {step : X → X} {read : X → Readout}
    (ind : InducedReadoutMap X Readout step read)
    (book : Content → X) (contents : List Content) (t : Nat) : Nat :=
  (imageSizes ind.g (historicalSeed read book contents) t).length

/-- **Historical distinguishability monotonicity** (counting form).

    Given an induced readout map (functional read-closure),
    \(H_{\mathrm{hist}}\) support sizes are non-increasing. -/
theorem historical_image_monotone_of_induced
    {X Content Readout : Type} [BEq Readout]
    {step : X → X} {read : X → Readout}
    (ind : InducedReadoutMap X Readout step read)
    (book : Content → X) (contents : List Content) (t : Nat) :
    historicalImageSizes ind book contents (t + 1) ≤
      historicalImageSizes ind book contents t :=
  image_size_monotone_step ind.g (historicalSeed read book contents) t

/-- Equal historical readouts remain equal after one more step (stability). -/
theorem historical_reads_stable
    {X Content Readout : Type}
    (step : X → X) (read : X → Readout) (book : Content → X)
    (hc : ReadClosed step read)
    {c₁ c₂ : Content} (t : Nat)
    (h : read (iterate step t (book c₁)) =
      read (iterate step t (book c₂))) :
    read (iterate step (t + 1) (book c₁)) =
      read (iterate step (t + 1) (book c₂)) :=
  hc _ _ h

/-- Semantic link: the `t`-step historical readout of a booking is `g^t`
    of its initial readout. -/
theorem historical_read_of_book
    {X Content Readout : Type}
    {step : X → X} {read : X → Readout}
    (ind : InducedReadoutMap X Readout step read)
    (book : Content → X) (c : Content) (t : Nat) :
    read (iterate step t (book c)) =
      iterate ind.g t (read (book c)) :=
  read_iterate_eq ind (book c) t

/-!
# Obs.EffectiveDynamics

Effective dynamics: ReadClosed, iterate, historical stability.
-/

/-- Stochastic read-closure on kernel supports. -/
def StochasticReadClosed {X Readout : Type} [BEq Readout]
    (poss : X → List X) (read : X → Readout) : Prop :=
  ∀ x y : X, read x = read y →
    ((poss x).map read).eraseDups = ((poss y).map read).eraseDups

/-- Dirac kernel support of a deterministic step. -/
def diracPoss {X : Type} (step : X → X) (x : X) : List X :=
  [step x]

/-- Deterministic read-closure ⇒ stochastic read-closure for Dirac supports. -/
theorem stochasticReadClosed_of_readClosed
    {X Readout : Type} [BEq Readout]
    {step : X → X} {read : X → Readout}
    (hc : ReadClosed step read) :
    StochasticReadClosed (diracPoss step) read := by
  intro x y h
  have : read (step x) = read (step y) := hc x y h
  simp only [diracPoss, List.map_cons, List.map_nil, List.eraseDups]
  simp [this]

/-- Induced successor-read support map on the readout. -/
structure InducedReadoutSupports (X : Type) (Readout : Type) [BEq Readout]
    (poss : X → List X) (read : X → Readout) where
  g : Readout → List Readout
  factors :
    ∀ x : X, ((poss x).map read).eraseDups = (g (read x)).eraseDups

/-- Induced supports ⇒ stochastic read-closure. -/
theorem stochasticReadClosed_of_inducedSupports
    {X Readout : Type} [BEq Readout]
    {poss : X → List X} {read : X → Readout}
    (ind : InducedReadoutSupports X Readout poss read) :
    StochasticReadClosed poss read := by
  intro x y h
  calc
    ((poss x).map read).eraseDups = (ind.g (read x)).eraseDups := ind.factors x
    _ = (ind.g (read y)).eraseDups := by rw [h]
    _ = ((poss y).map read).eraseDups := Eq.symm (ind.factors y)

end Obs.EffectiveDynamics

/- axiom footprint -/
#print axioms Obs.EffectiveDynamics.step_factors_read_of_factors
#print axioms Obs.EffectiveDynamics.readClosed_of_factors
#print axioms Obs.EffectiveDynamics.protocol_noninjective
#print axioms Obs.EffectiveDynamics.observable_merge_of_write_unread_readClosed
#print axioms Obs.EffectiveDynamics.readClosed_of_induced
#print axioms Obs.EffectiveDynamics.readClosed_iff_induced
#print axioms Obs.EffectiveDynamics.read_iterate_eq
#print axioms Obs.EffectiveDynamics.historical_image_monotone_of_induced
#print axioms Obs.EffectiveDynamics.historical_reads_stable
#print axioms Obs.EffectiveDynamics.historical_read_of_book
#print axioms Obs.EffectiveDynamics.stochasticReadClosed_of_readClosed
#print axioms Obs.EffectiveDynamics.stochasticReadClosed_of_inducedSupports
