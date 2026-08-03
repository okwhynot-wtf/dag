import Certificate
import TwoCycle
import Orbit
import Canon
import Geom.Registration

/-!
# BitFlip — second dictionary entry (information / Szilard caricature)

Non-cosmological I-4 instance: two-state memory with bit-flip involution.
**Empty** fixed-set mode (live). Forced +1: single-cell no-go.
-/

namespace Dictionary.BitFlip

open Dictionary.Certificate

inductive Cell where
  | zero
  | one
  deriving DecidableEq, Repr

def flip : Cell → Cell
  | Cell.zero => Cell.one
  | Cell.one => Cell.zero

theorem flip_involutive (c : Cell) : flip (flip c) = c := by
  cases c <;> rfl

def bit : Cell → Bool
  | Cell.zero => false
  | Cell.one => true

def ofBit : Bool → Cell
  | false => Cell.zero
  | true => Cell.one

theorem bit_flip_as_not (c : Cell) : bit (flip c) = !(bit c) := by
  cases c <;> rfl

theorem ofBit_bit (c : Cell) : ofBit (bit c) = c := by
  cases c <;> rfl

theorem bit_ofBit (b : Bool) : bit (ofBit b) = b := by
  cases b <;> rfl

def divide : Cell → Prop := fun c => flip c = c

theorem divide_empty (c : Cell) : ¬ divide c := by
  cases c with
  | zero => intro h; cases h
  | one => intro h; cases h

theorem single_cell_nogo :
    ¬ ∃ act : Unit → Unit, Orbit.Live act := by
  intro ⟨act, hl⟩
  exact hl () (Subsingleton.elim (act ()) ())

def memoryStep : Bool × Unit → Bool × Unit :=
  Geom.Registration.oscStep

theorem memory_silent :
    Geom.Registration.Inj memoryStep ∧
    ¬ Geom.Registration.Merges memoryStep ∧
    ¬ Geom.Registration.Registers memoryStep :=
  Geom.Registration.osc_never_registers

theorem flip_reads_as_not :
    (∀ c, flip c = ofBit (!(bit c))) ∧
    Canon.IsFundamental (not : Bool → Bool) := by
  refine ⟨fun c => by cases c <;> rfl, Canon.canon_is_fundamental⟩

def bitFlipCert : KernelCert Cell Bool where
  swap := flip
  square := id
  swap_sq := flip_involutive
  square_involutive := fun _ => rfl
  observe := bit
  obsNeg := not
  swap_as_not := bit_flip_as_not
  Fixed := divide
  fixed_iff := fun _ => Iff.rfl
  fixedMode := FixedMode.empty
  noSoloCross := fun c h => (divide_empty c) h.1

theorem bitFlip_admitted :
    (∀ c, bitFlipCert.swap (bitFlipCert.swap c) = bitFlipCert.square c) ∧
    (∀ c, bitFlipCert.square c = c) ∧
    (∀ c, bitFlipCert.observe (bitFlipCert.swap c) =
      bitFlipCert.obsNeg (bitFlipCert.observe c)) ∧
    (∀ c, ¬ bitFlipCert.Fixed c) ∧
    bitFlipCert.fixedMode = FixedMode.empty ∧
    (¬ ∃ act : Unit → Unit, Orbit.Live act) ∧
    (Geom.Registration.Inj memoryStep ∧
      ¬ Geom.Registration.Merges memoryStep) :=
  ⟨bitFlipCert.swap_sq, fun _ => rfl, bitFlipCert.swap_as_not, divide_empty,
   rfl, single_cell_nogo, ⟨memory_silent.1, memory_silent.2.1⟩⟩

theorem dictionary_extensible :
    boolCert.fixedMode = FixedMode.empty ∧
    bitFlipCert.fixedMode = FixedMode.empty ∧
    (∀ c, ¬ bitFlipCert.Fixed c) :=
  ⟨rfl, rfl, divide_empty⟩

#print axioms bitFlip_admitted
#print axioms flip_involutive
#print axioms single_cell_nogo
#print axioms dictionary_extensible

end Dictionary.BitFlip
