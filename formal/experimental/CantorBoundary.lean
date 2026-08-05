import Diagonal
import Ladder

/-!
# CantorBoundary (EXPERIMENTAL — quarantined; exports nothing to the paper)

Probe: what object at the edge of the ladder outruns every
enumeration without any new axiom? Answer: the space of complete
gauge histories, one pole choice at every level forever, which is
`Nat → Bool` (Cantor space); no cardinality claim beyond the seal is
made or needed. Facts proved here; no proof uses function
extensionality — function-equality hypotheses are consumed via
`congrFun` or hold definitionally — and every theorem below
(including the rung embedding, whose base cases close by
`Bool.noConfusion` rather than `simp`) has an empty `#print axioms`
footprint, as the audit block at the file bottom verifies:

* every rung embeds in the boundary (`encode_inj_pointwise`,
  `rungs_embed`), and the fundamental embeds as the constant
  histories (`fundamental_embeds`);
* the boundary outruns every enumeration, by the corpus's own seal
  specialised to `Nat` (`boundary_unenumerable`);
* the fundamental lifts to the boundary: the pole swap `flip` acts at
  every level forever, is a pointwise involution
  (`flip_flip_pointwise`), and liveness survives the passage to the
  boundary (`flip_live`);
* the boundary seals in its own right (`boundary_seals_itself`):
  `seal_on_fundamental` applied to `flip` shows no
  `f : A → A → GaugeHistory` is point-surjective, for any carrier
  `A`. This strengthens `boundary_unenumerable`, which merely
  specialises `seal_bool` at carrier `Nat`: here the boundary is
  itself a live arena, sealed at its own carrier by its own act;
* the one Z/2 acts at infinite depth: every `mask m` is a pointwise
  involution (`mask_mask_pointwise`), and masking by the all-true
  history agrees pointwise with `flip` (`mask_top_eq_flip`);
* losslessness fails at the boundary: inside the arena involutivity
  forbids erasure, but at the boundary the `tail` step erases
  (`tail_erasing`, with a definitional witness) — the boundary
  poverty extends to dynamics, and that poverty remains part of the
  record. Still, `tail` has a section per pole (`tail_cons`): the
  blank-adjunction shape reappears at the boundary;
* the ladder step is carried at the boundary: the blank rung encodes
  as the all-true history (`encode_succ_none`), climbing one rung is
  `cons false` coordinatewise (`encode_succ_some`), and climbing then
  dropping the first coordinate is the identity (`tail_encode_some`)
  — the `(+1)/some` step of the ladder is carried by `cons/tail` on
  histories as a section/retraction pair (the blank-adjunction
  shape), definitionally per coordinate case;
* injectivity is effective: depth-`(k+1)` cylinders separate rung
  `k`. Distinct inhabitants of `Ladder.Level k` differ at some
  coordinate `m ≤ k` of their encodings (`encode_separates`), the
  finite-approximation structure of the boundary with an
  explicit bound; `encode_inj_pointwise` is its contrapositive
  restated (`encode_inj_of_separates`).

What the boundary lacks is everything physics would need
(metric, order, group action); its poverty is part of the record.
-/
namespace Experimental.CantorBoundary

/-- The boundary object: complete gauge histories, one pole choice at
    every level forever. -/
abbrev GaugeHistory : Type := Nat → Bool

/-! ## The boundary outruns every enumeration -/

/-- No enumeration reaches the boundary: the corpus seal, specialised
    to carrier `Nat`. -/
theorem boundary_unenumerable (r : Nat → GaugeHistory) :
    ¬ Diagonal.PointSurjective r :=
  Diagonal.seal_bool r

/-! ## Every rung embeds in the boundary -/

/-- Encode a rung inhabitant as a gauge history. -/
def encode : (k : Nat) → Ladder.Level k → GaugeHistory
  | 0, b => fun _ => b
  | _ + 1, none => fun _ => true
  | k + 1, some a => fun n =>
      match n with
      | 0 => false
      | m + 1 => encode k a m

/-- Pointwise injectivity of the encoding, with no appeal to function
    extensionality. -/
theorem encode_inj_pointwise :
    ∀ (k : Nat) (x y : Ladder.Level k),
      (∀ n, encode k x n = encode k y n) → x = y := by
  intro k
  induction k with
  | zero =>
    intro x y h
    exact h 0
  | succ k ih =>
    intro x y h
    cases x with
    | none =>
      cases y with
      | none => rfl
      | some b => exact Bool.noConfusion (h 0)
    | some a =>
      cases y with
      | none => exact Bool.noConfusion (h 0)
      | some b =>
        have htail : ∀ n, encode k a n = encode k b n := fun n => h (n + 1)
        rw [ih a b htail]

/-- Every rung embeds in the boundary. -/
theorem rungs_embed (k : Nat) (x y : Ladder.Level k)
    (h : encode k x = encode k y) : x = y :=
  encode_inj_pointwise k x y (fun n => congrFun h n)

/-- The fundamental embeds as the two constant histories. -/
theorem fundamental_embeds (b b' : Bool)
    (h : encode 0 b = encode 0 b') : b = b' :=
  rungs_embed 0 b b' h

/-! ## The fundamental lifts to the boundary -/

/-- The pole swap lifted to the boundary: negate the pole choice at
    every level forever. -/
def flip : GaugeHistory → GaugeHistory := fun x n => !(x n)

/-- `flip` is a pointwise involution: swapping every pole twice
    restores every coordinate. Stated pointwise, so no function
    extensionality is needed. -/
theorem flip_flip_pointwise (x : GaugeHistory) (n : Nat) :
    flip (flip x) n = x n :=
  Bool.not_not (x n)

/-- Liveness survives the passage to the boundary: `flip` moves every
    history. From an alleged fixed point, coordinate `0` would give
    `!(x 0) = x 0`, impossible for either pole. -/
theorem flip_live : Orbit.Live flip := by
  intro x h
  have h0 : (!(x 0)) = x 0 := congrFun h 0
  cases hx : x 0 with
  | false => rw [hx] at h0; exact Bool.noConfusion h0
  | true => rw [hx] at h0; exact Bool.noConfusion h0

/-! ## The boundary seals in its own right -/

/-- The boundary is itself a live arena, sealed at its own carrier:
    for every `f : A → A → GaugeHistory`, `f` is not
    point-surjective. This is `seal_on_fundamental` applied to `flip`
    and its liveness, and it strengthens `boundary_unenumerable`:
    that theorem specialises `seal_bool` at carrier `Nat`, while here
    the sealing act lives on the boundary itself and the carrier `A`
    is arbitrary. -/
theorem boundary_seals_itself {A : Type} (f : A → A → GaugeHistory) :
    ¬ Diagonal.PointSurjective f :=
  Diagonal.seal_on_fundamental flip flip_live f

/-! ## The one Z/2 at infinite depth -/

/-- Mask a history by another: XOR the pole choices level by level.
    Each mask is the one Z/2 acting coordinatewise at infinite
    depth. -/
def mask (m : GaugeHistory) : GaugeHistory → GaugeHistory :=
  fun x n => x n ^^ m n

/-- Every mask is a pointwise involution: XOR by the same history
    twice restores every coordinate. -/
theorem mask_mask_pointwise (m x : GaugeHistory) (n : Nat) :
    mask m (mask m x) n = x n := by
  show ((x n ^^ m n) ^^ m n) = x n
  cases x n <;> cases m n <;> rfl

/-- Masking by the all-true history agrees pointwise with the lifted
    pole swap: `flip` is the mask at the top. -/
theorem mask_top_eq_flip (x : GaugeHistory) (n : Nat) :
    mask (fun _ => true) x n = flip x n := by
  show (x n ^^ true) = !(x n)
  cases x n <;> rfl

/-! ## Losslessness fails at the boundary -/

/-- Drop the first pole choice and shift the history down one
    level. -/
def tail (x : GaugeHistory) : GaugeHistory := fun n => x (n + 1)

/-- A history that spikes at coordinate `0` and is blank ever after.
    Defined by a match so that `tail spike` reduces definitionally to
    the constantly-false history. -/
def spike : GaugeHistory := fun n =>
  match n with
  | 0 => true
  | _ + 1 => false

/-- Inside the arena, involutivity forbids erasure; at the boundary,
    the tail step erases. The constantly-false history and `spike`
    differ at coordinate `0`, yet their tails are definitionally
    equal — the boundary poverty extends to dynamics, and that
    poverty remains part of the record. -/
theorem tail_erasing : Orbit.Erasing tail := by
  refine ⟨(fun _ => false), spike, ?_, rfl⟩
  intro h
  exact Bool.noConfusion (congrFun h 0)

/-- Prepend a pole choice to a history. -/
def cons (b : Bool) (x : GaugeHistory) : GaugeHistory := fun n =>
  match n with
  | 0 => b
  | m + 1 => x m

/-- `tail` has a section per pole: prepending either pole choice and
    then taking the tail restores every coordinate (the
    blank-adjunction shape at the boundary). Definitional. -/
theorem tail_cons (b : Bool) (x : GaugeHistory) (n : Nat) :
    tail (cons b x) n = x n :=
  rfl

/-! ## The ladder step at the boundary (section/retraction) -/

/-- The blank rung encodes as the all-true history. Definitional. -/
theorem encode_succ_none (k : Nat) (n : Nat) :
    encode (k + 1) none n = true :=
  rfl

/-- Climbing one rung is `cons false` coordinatewise: the encoding of
    `some a` at level `k + 1` agrees at every coordinate with `false`
    prepended to the encoding of `a` at level `k`. Both sides match on
    `n` identically, so each case closes by `rfl`. -/
theorem encode_succ_some (k : Nat) (a : Ladder.Level k) (n : Nat) :
    encode (k + 1) (some a) n = cons false (encode k a) n := by
  cases n with
  | zero => rfl
  | succ m => rfl

/-- Climbing one rung and then dropping the first coordinate is the
    identity: the section/retraction half of the ladder's
    blank-adjunction shape, carried at the boundary by `cons/tail`.
    Definitional. -/
theorem tail_encode_some (k : Nat) (a : Ladder.Level k) (n : Nat) :
    tail (encode (k + 1) (some a)) n = encode k a n :=
  rfl

/-! ## Finite approximation: cylinders separate rungs -/

/-- Effective injectivity of the encoding: distinct inhabitants of
    rung `k` differ at some coordinate `m ≤ k` of their encodings, so
    depth-`(k + 1)` cylinders separate rung `k`. Induction on `k`: at
    level `0` the coordinate is `0`; at a successor, a `none/some`
    disagreement shows at coordinate `0`, and a `some/some`
    disagreement lifts the inductive witness `m` to `m + 1`. This is
    the finite-approximation structure of the boundary,
    with an explicit bound. -/
theorem encode_separates :
    ∀ (k : Nat) (x y : Ladder.Level k), x ≠ y →
      ∃ m, m ≤ k ∧ encode k x m ≠ encode k y m := by
  intro k
  induction k with
  | zero =>
    intro x y hxy
    exact ⟨0, Nat.le_refl 0, fun h => hxy h⟩
  | succ k ih =>
    intro x y hxy
    cases x with
    | none =>
      cases y with
      | none => exact absurd rfl hxy
      | some b =>
        exact ⟨0, Nat.zero_le _, fun h => Bool.noConfusion h⟩
    | some a =>
      cases y with
      | none =>
        exact ⟨0, Nat.zero_le _, fun h => Bool.noConfusion h⟩
      | some b =>
        have hab : a ≠ b := fun h => hxy (congrArg some h)
        obtain ⟨m, hm, hne⟩ := ih a b hab
        exact ⟨m + 1, Nat.succ_le_succ hm, hne⟩

/-- Pointwise injectivity restated as the contrapositive of
    `encode_separates`: histories that agree at every coordinate came
    from the same rung inhabitant. -/
theorem encode_inj_of_separates (k : Nat) (x y : Ladder.Level k)
    (h : ∀ n, encode k x n = encode k y n) : x = y := by
  by_cases hxy : x = y
  · exact hxy
  · obtain ⟨m, _, hne⟩ := encode_separates k x y hxy
    exact absurd (h m) hne

#print axioms Experimental.CantorBoundary.boundary_unenumerable
#print axioms Experimental.CantorBoundary.encode_inj_pointwise
#print axioms Experimental.CantorBoundary.rungs_embed
#print axioms Experimental.CantorBoundary.fundamental_embeds
#print axioms Experimental.CantorBoundary.flip_flip_pointwise
#print axioms Experimental.CantorBoundary.flip_live
#print axioms Experimental.CantorBoundary.boundary_seals_itself
#print axioms Experimental.CantorBoundary.mask_mask_pointwise
#print axioms Experimental.CantorBoundary.mask_top_eq_flip
#print axioms Experimental.CantorBoundary.tail_erasing
#print axioms Experimental.CantorBoundary.tail_cons
#print axioms Experimental.CantorBoundary.encode_succ_none
#print axioms Experimental.CantorBoundary.encode_succ_some
#print axioms Experimental.CantorBoundary.tail_encode_some
#print axioms Experimental.CantorBoundary.encode_separates
#print axioms Experimental.CantorBoundary.encode_inj_of_separates

end Experimental.CantorBoundary
