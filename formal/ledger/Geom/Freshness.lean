import Geom.Exhaustion
import Geom.Totality
import Geom.Provision

/-!
# Geom.Freshness

Product freshness and stream muteness are distinct predicates. This module
names them, proves independence, and records stream muteness of the
expanding conveyor.

Aliases: `StreamMuteAt` for `Geom.Exhaustion.FreshAt`;
`ProductFreshAt` for `Geom.Totality.FreshAt`.
-/

namespace Geom.Freshness

/-- Outgoing stream constant across a merge block. -/
abbrev StreamMuteAt {S Eout Eint : Type}
    (U : S × Eout × Eint → S × Eout × Eint)
    (σ : Nat → S) (es : Nat → List Eout) (caps : Nat → List Eint) :
    Nat → Prop :=
  Geom.Exhaustion.FreshAt (S := S) (Eout := Eout) (Eint := Eint) U σ es caps

/-- Slice support is a product set. -/
abbrev ProductFreshAt {S E : Type} [DecidableEq S] [DecidableEq E]
    (H : Geom.Totality.Totality S E) (c : Nat) : Prop :=
  Geom.Totality.FreshAt (S := S) (E := E) H c

/-- Product support on a finite list of pairs (classical stand-in). -/
abbrev ProductSupport {S E : Type} [DecidableEq S] [DecidableEq E]
    (pairs : List (S × E)) : Prop :=
  Geom.Totality.ProductSlice (S := S) (E := E) pairs

/-! ## The slice a step files

`StreamMuteAt` is a predicate on a joint step; `ProductFreshAt` is a
predicate on a slice of system–environment pairs. `archiveSlice` builds
the slice a step files; `oneTick` / `productFresh_oneTick` relate a bare
slice to `ProductFreshAt`. -/

/-- The archive slice a step induces on a list of inputs: each input's system
value paired with the buffer letter the step files for it. -/
def archiveSlice {S Eout Eint : Type}
    (U : S × Eout × Eint → S × Eout × Eint)
    (e : Eout) (ins : List (S × Eint)) : List (S × Eint) :=
  ins.map (fun p => (p.1, (U (p.1, e, p.2)).2.2))

/-- The one-tick totality whose only clock reading is the given slice. -/
def oneTick {S E : Type} (pairs : List (S × E)) : Geom.Totality.Totality S E :=
  pairs.map (fun x => [x])

theorem slice_oneTick {S E : Type} (pairs : List (S × E)) :
    Geom.Totality.slice (oneTick pairs) 0 = pairs := by
  induction pairs with
  | nil => rfl
  | cons x xs ih =>
    show x :: Geom.Totality.slice (oneTick xs) 0 = x :: xs
    rw [ih]

/-- Bridge: product freshness of the one-tick totality built from a slice is
exactly product-ness of that slice. Lets the countermodels below be stated in
the named predicate `ProductFreshAt`. -/
theorem productFresh_oneTick {S E : Type} [DecidableEq S] [DecidableEq E]
    (pairs : List (S × E)) :
    ProductFreshAt (oneTick pairs) 0 ↔ ProductSupport pairs := by
  show Geom.Totality.ProductSlice (Geom.Totality.slice (oneTick pairs) 0)
       ↔ Geom.Totality.ProductSlice pairs
  rw [slice_oneTick]

/-! ## Stream mute does not imply product fresh -/

/-- Mute merger: system collapses to `false`, stream ships `false`,
buffer files the prior system bit. -/
def muteU : Bool × Bool × Bool → Bool × Bool × Bool :=
  fun p => (false, false, p.1)

/-- Two inputs differing in the system bit, each with a blank buffer. -/
def muteInputs : List (Bool × Bool) :=
  [(true, false), (false, false)]

/-- Correlated (non-product) support on `Bool × Bool`. -/
def correlatedSupport : List (Bool × Bool) :=
  [(true, true), (false, false)]

/-- The mute merger's *own* archive slice is the correlated one: filing the
prior system bit couples system and buffer perfectly. -/
theorem muteU_slice :
    archiveSlice muteU false muteInputs = correlatedSupport := rfl

/-- Stream muteness holds for `muteU` at every schedule. -/
theorem muteU_stream_mute (σ : Nat → Bool)
    (es : Nat → List Bool) (caps : Nat → List Bool) (t : Nat) :
    StreamMuteAt muteU σ es caps t := by
  intro e _he e' _he' i _hi i' _hi'
  rfl

theorem mem_tt : (true, true) ∈ correlatedSupport :=
  List.Mem.head _

theorem mem_ff : (false, false) ∈ correlatedSupport :=
  List.Mem.tail _ (List.Mem.head _)

theorem not_mem_tf : ¬ (true, false) ∈ correlatedSupport := by
  intro h
  -- `List.Mem.head` is impossible unless the element is definitionally the
  -- list head; neither `(true,true)` nor `(false,false)` matches `(true,false)`.
  cases h with
  | tail _ h' =>
    cases h' with
    | tail _ h'' =>
      cases h''

/-- The correlated support is not a product set. -/
theorem correlated_not_product :
    ¬ ProductSupport (S := Bool) (E := Bool) correlatedSupport := by
  intro h
  exact not_mem_tf (h true false ⟨true, mem_tt⟩ ⟨false, mem_ff⟩)

/-- **Stream muteness does not imply product freshness.** One and the same
step, `muteU`, is stream-mute at every schedule *and* files an archive slice
that is not product. Both predicates are evaluated on `muteU` here; the
countermodel is a single object, not two unrelated ones. -/
theorem stream_mute_not_imply_product :
    (∀ σ es caps t, StreamMuteAt muteU σ es caps t)
    ∧ ¬ ProductFreshAt (oneTick (archiveSlice muteU false muteInputs)) 0 := by
  refine ⟨muteU_stream_mute, ?_⟩
  intro h
  exact correlated_not_product
    (muteU_slice ▸ (productFresh_oneTick
      (archiveSlice muteU false muteInputs)).mp h)

/-! ## Product fresh does not imply stream mute -/

/-- Reveal merger: system collapses to `false`, stream ships the scheduled
unit (not mute), buffer unchanged. -/
def revealU : Bool × Bool × Bool → Bool × Bool × Bool :=
  fun p => (false, p.2.1, p.2.2)

/-- Full product support on `Bool × Bool`. -/
def fullProductSupport : List (Bool × Bool) :=
  [(false, false), (false, true), (true, false), (true, true)]

/-- Inputs ranging over the whole `system × buffer` square. -/
def revealInputs : List (Bool × Bool) := fullProductSupport

/-- The reveal merger's *own* archive slice is the full product: it leaves the
buffer alone, so system and buffer stay independent. -/
theorem revealU_slice :
    archiveSlice revealU false revealInputs = fullProductSupport := rfl

theorem mem_full (s e : Bool) : (s, e) ∈ fullProductSupport := by
  cases s <;> cases e
  · exact List.Mem.head _
  · exact List.Mem.tail _ (List.Mem.head _)
  · exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))
  · exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem full_is_product :
    ProductSupport (S := Bool) (E := Bool) fullProductSupport :=
  fun s e _ _ => mem_full s e

theorem false_mem_es : false ∈ ([false, true] : List Bool) := List.Mem.head _
theorem true_mem_es : true ∈ ([false, true] : List Bool) :=
  List.Mem.tail _ (List.Mem.head _)
theorem false_mem_caps : false ∈ ([false] : List Bool) := List.Mem.head _

/-- With two scheduled units, `revealU` fails stream muteness. -/
theorem revealU_not_stream_mute :
    ¬ StreamMuteAt revealU (fun _ => false)
        (fun _ => [false, true]) (fun _ => [false]) 0 := by
  intro h
  have hEq : false = true :=
    h false false_mem_es true true_mem_es false false_mem_caps false false_mem_caps
  cases hEq

/-- **Product freshness does not imply stream muteness.** One and the same
step, `revealU`, files a product archive slice *and* fails stream muteness. -/
theorem product_not_imply_stream_mute :
    ProductFreshAt (oneTick (archiveSlice revealU false revealInputs)) 0
    ∧ ¬ StreamMuteAt revealU (fun _ => false)
        (fun _ => [false, true]) (fun _ => [false]) 0 := by
  refine ⟨?_, revealU_not_stream_mute⟩
  exact (productFresh_oneTick (archiveSlice revealU false revealInputs)).mpr
    (revealU_slice ▸ full_is_product)

/-! ## Conveyor: both predicates by construction, without identifying them -/

/-- Expanding conveyor is stream-mute at every tick. -/
theorem expand_bridge_stream_mute {S Eout : Type}
    (g : S → S) (blank : Eout) (s0 : S) (A : List Eout) (t : Nat) :
    StreamMuteAt (Geom.Provision.expandStep g blank)
      (Geom.Provision.gIter g s0) (fun _ => A)
      (Geom.Provision.expandCaps A) t :=
  Geom.Provision.expand_fresh_at g blank s0 A t

/-- Independence countermodels and conveyor stream muteness.

Each countermodel is a *single* step carrying both properties: `muteU` is mute
with a non-product slice, `revealU` is product with a non-mute stream. -/
theorem freshness_hygiene {S Eout : Type}
    (g : S → S) (blank : Eout) (s0 : S) (A : List Eout) (t : Nat) :
    (∀ σ es caps u, StreamMuteAt muteU σ es caps u)
    ∧ ¬ ProductFreshAt (oneTick (archiveSlice muteU false muteInputs)) 0
    ∧ ProductFreshAt (oneTick (archiveSlice revealU false revealInputs)) 0
    ∧ ¬ StreamMuteAt revealU (fun _ => false)
        (fun _ => [false, true]) (fun _ => [false]) 0
    ∧ StreamMuteAt (Geom.Provision.expandStep g blank)
        (Geom.Provision.gIter g s0) (fun _ => A)
        (Geom.Provision.expandCaps A) t :=
  ⟨stream_mute_not_imply_product.1,
   stream_mute_not_imply_product.2,
   product_not_imply_stream_mute.1,
   product_not_imply_stream_mute.2,
   expand_bridge_stream_mute g blank s0 A t⟩

end Geom.Freshness

#print axioms Geom.Freshness.slice_oneTick
#print axioms Geom.Freshness.productFresh_oneTick
#print axioms Geom.Freshness.muteU_slice
#print axioms Geom.Freshness.revealU_slice
#print axioms Geom.Freshness.muteU_stream_mute
#print axioms Geom.Freshness.correlated_not_product
#print axioms Geom.Freshness.stream_mute_not_imply_product
#print axioms Geom.Freshness.full_is_product
#print axioms Geom.Freshness.revealU_not_stream_mute
#print axioms Geom.Freshness.product_not_imply_stream_mute
#print axioms Geom.Freshness.expand_bridge_stream_mute
#print axioms Geom.Freshness.freshness_hygiene
