/-!
# Obs.AbstractMemory

Record interface: Booking, SelfBlindness, ReadClosure.
-/

namespace Obs.AbstractMemory

/-- One-step dynamics on an abstract state space. -/
structure System (X : Type) where
  step : X → X

/-- Record embodiment: stationary substrate or propagating channel. -/
inductive RecordKind where
  | stationary   : RecordKind
  | propagating  : RecordKind

/-! ## Causal-record vocabulary -/

/-- Causal record channel: book → step → read. -/
structure RecordChannel (X : Type) (Content : Type) (Readout : Type) where
  kind : RecordKind
  system : System X
  book : Content → X
  read : X → Readout

/-! ## Booking -/

/-- Booking: a prior distinction is imprinted injectively into the record
    channel at write time. -/
structure Booking (X : Type) (Content : Type) where
  book : Content → X
  injective : ∀ c₁ c₂ : Content, book c₁ = book c₂ → c₁ = c₂
  nontrivial : ∃ c₁ c₂ : Content, c₁ ≠ c₂

theorem book_ne_of_ne {X Content : Type} (bk : Booking X Content)
    {c₁ c₂ : Content} (h : c₁ ≠ c₂) : bk.book c₁ ≠ bk.book c₂ := by
  intro heq
  exact h (bk.injective c₁ c₂ heq)

/-! ## Finite reference support (counting structure) -/

/-- Finite reference support: domain of enumeration for image sizes /
    H_reach / H_hist. Not a dynamical condition. -/
structure FiniteReferenceSupport (X : Type) where
  /-- Finite support of accessible histories. -/
  support : List X
  nonempty : support ≠ []

/-- Cardinality of the reference support. -/
def FiniteReferenceSupport.size {X : Type}
    (S : FiniteReferenceSupport X) : Nat :=
  S.support.length

/-- Uniform reference weight on the support (v1 μ_ref). -/
def FiniteReferenceSupport.uniformWeight {X : Type}
    (S : FiniteReferenceSupport X) : Nat :=
  S.size

/-! ## Write-unread + factoring (self-blindness package) -/

/-- Write-unread together with step factoring through read. -/
structure SelfBlindness (X : Type) (Content : Type) (Readout : Type)
    (M : System X) (bk : Booking X Content) where
  read : X → Readout
  /-- Distinct booked contents are indistinguishable to the reader. -/
  write_unread :
    ∃ c₁ c₂ : Content, c₁ ≠ c₂ ∧ read (bk.book c₁) = read (bk.book c₂)
  /-- Step factors through the readable view. -/
  step_factors_read :
    ∀ x y : X, read x = read y → M.step x = M.step y

/-! ## Read-closure -/

/-- Read-closure: equal readable views stay equal after a step. -/
structure ReadClosure (X : Type) (Readout : Type)
    (M : System X) (read : X → Readout) where
  closed :
    ∀ x y : X, read x = read y → read (M.step x) = read (M.step y)

/-! ## Causal-record system bundle -/

/-- A causal-record system: dynamical conditions plus finite reference support. -/
structure CausalRecordSystem (X : Type) (Content : Type) (Readout : Type) where
  system : System X
  booking : Booking X Content
  referenceSupport : FiniteReferenceSupport X
  selfBlind : SelfBlindness X Content Readout system booking
  readClosure : ReadClosure X Readout system selfBlind.read
  /-- Stationary or propagating; does not change the conditions. -/
  kind : RecordKind := RecordKind.stationary

/-- Project the bundle as a record channel. -/
def CausalRecordSystem.toChannel {X Content Readout : Type}
    (C : CausalRecordSystem X Content Readout) :
    RecordChannel X Content Readout where
  kind := C.kind
  system := C.system
  book := C.booking.book
  read := C.selfBlind.read

end Obs.AbstractMemory

/- axiom footprint -/
#print Obs.AbstractMemory.RecordKind
#print Obs.AbstractMemory.RecordChannel
#print Obs.AbstractMemory.Booking
#print Obs.AbstractMemory.FiniteReferenceSupport
#print Obs.AbstractMemory.SelfBlindness
#print Obs.AbstractMemory.ReadClosure
#print Obs.AbstractMemory.CausalRecordSystem
