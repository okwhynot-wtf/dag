import Ladder

/-!
# Cause — causal structure on the ladder

Names and proves causal structure already present in `Ladder`: caused
content at a naming step is the named escape of the predecessor; on the
committed ladder this is the Lawvere dodge (`effectOf`).

* **Determination** (`same_cause_same_effect`): equal diagonals force equal
  dodge-effects.
* **Transmission** (`difference_transmitted`, `transmission_exact`):
  on a lossless act, effects differ exactly where diagonals differ.
* **Faithful fundamental** (`fundamental_faithful`, `erasure_breaks_transmission`):
  symmetric step yields losslessness; erasing acts break transmission.
* **Asymmetry** (`causal_asymmetry`): forward effect is definitional;
  backward readings are conserved under `Ladder.lift`.
* **Intervention** (`step`, `stepEsc`, `intervention_changes_effect`,
  `intervention_preserves_past`): replace a level's reading and continue;
  downstream names change with the chosen escape; upstream unchanged.
* **Policy** (`Policy`, `repP`): parameterises free values and, at each
  tick, which unrepresented escape is named; the committed ladder is the
  dodge policy; distinct escape choices yield distinct histories
  (`escapes_really_differ`, `escapes_differ_at`).

Causation is stated within representational dynamics; no probabilistic or
physical claims. No declared axioms.
-/
namespace Cause

open Diagonal

variable {α : Type}

/-- Caused content of a naming step: the dodge of the present reading. -/
def effectOf (act : α → α) {A : Type} (f : A → A → α) : A → α :=
  dodgeWith act f

/-! ## Determination and transmission -/

/-- Equal diagonals imply equal effects. -/
theorem same_cause_same_effect {A : Type} (act : α → α)
    (f f' : A → A → α) (h : ∀ x, f x x = f' x x) :
    ∀ a, effectOf act f a = effectOf act f' a := by
  intro a
  show act (f a a) = act (f' a a)
  rw [h a]

/-- On a lossless act, diagonal inequality transmits to effect inequality. -/
theorem difference_transmitted {A : Type} (act : α → α)
    (hL : Orbit.Lossless act) (f f' : A → A → α) (a : A)
    (h : f a a ≠ f' a a) :
    effectOf act f a ≠ effectOf act f' a :=
  fun he => h (hL _ _ he)

/-- Effects differ at a point iff diagonals differ there (lossless act). -/
theorem transmission_exact {A : Type} (act : α → α)
    (hL : Orbit.Lossless act) (f f' : A → A → α) (a : A) :
    effectOf act f a ≠ effectOf act f' a ↔ f a a ≠ f' a a := by
  constructor
  · intro hne heq
    exact hne (by show act (f a a) = act (f' a a); rw [heq])
  · exact difference_transmitted act hL f f' a

/-- Under a symmetric step, transmission is exact (`Orbit.symmetric_lossless`). -/
theorem fundamental_faithful {A : Type} (act : α → α)
    (hs : Orbit.SymmetricStep act) (f f' : A → A → α) (a : A) :
    effectOf act f a ≠ effectOf act f' a ↔ f a a ≠ f' a a :=
  transmission_exact act (Orbit.symmetric_lossless act hs) f f' a

/-- An erasing act admits distinct diagonals with identical effects. -/
theorem erasure_breaks_transmission :
    ∃ (act : Bool → Bool) (f f' : Bool → Bool → Bool) (a : Bool),
      Orbit.Erasing act ∧
      f a a ≠ f' a a ∧ effectOf act f a = effectOf act f' a :=
  ⟨fun _ => true, fun _ _ => true, fun _ _ => false, true,
   ⟨false, true, by decide, rfl⟩, by decide, rfl⟩

/-! ## Asymmetry -/

/-- Forward: `none` names the negated diagonal; backward: lifts are
    conservative (`Ladder.lift_conservative`). -/
theorem causal_asymmetry (k : Nat) :
    (∀ a : Ladder.Level k,
      Ladder.rep (k + 1) none (some a) = !(Ladder.rep k a a)) ∧
    (∀ j, ∀ x y : Ladder.Level k,
      Ladder.rep (k + j) (Ladder.lift k j x) (Ladder.lift k j y) =
        Ladder.rep k x y) :=
  ⟨fun _ => rfl, fun j x y => Ladder.lift_conservative k j x y⟩

/-! ## Intervention -/

/-- One naming step from an arbitrary present reading, naming a chosen
    escape `e`. -/
def stepEsc {A : Type} (f : A → A → Bool) (e : A → Bool) :
    Option A → Option A → Bool
  | some a, some x => f a x
  | none, some x => e x
  | _, none => false

/-- Default intervention: name the Lawvere dodge. -/
def step {A : Type} (f : A → A → Bool) : Option A → Option A → Bool :=
  stepEsc f (fun x => !(f x x))

/-- `stepEsc f e` is a naming extension when `e` misses every row of `f`. -/
theorem stepEsc_naming {A : Type} (f : A → A → Bool) (e : A → Bool)
    (hm : ∀ a, ∃ x, f a x ≠ e x) :
    Tower.NamingExtension f (stepEsc f e) some e :=
  ⟨fun _ _ => rfl, hm, ⟨none, fun _ => rfl⟩⟩

/-- `step f` is a naming extension of `f` naming the dodge. -/
theorem step_naming {A : Type} (f : A → A → Bool) :
    Tower.NamingExtension f (step f) some (fun x => !(f x x)) :=
  Tower.of_dodge not TwoCycle.bool_fundamental.1
    (fun _ _ => rfl) ⟨none, fun _ => rfl⟩

/-- `Ladder.rep (k+1)` equals `step (Ladder.rep k)`. -/
theorem ladder_is_iterated_step (k : Nat) :
    ∀ x y : Ladder.Level (k + 1),
      Ladder.rep (k + 1) x y = step (Ladder.rep k) x y := by
  intro x y
  cases x with
  | some a =>
    cases y with
    | some x' => rfl
    | none => rfl
  | none =>
    cases y with
    | some x' => rfl
    | none => rfl

/-- Distinct escapes yield distinct names at `none`. -/
theorem intervention_changes_effect {A : Type} (f : A → A → Bool)
    (e e' : A → Bool) (a : A) (h : e a ≠ e' a) :
    stepEsc f e none (some a) ≠ stepEsc f e' none (some a) :=
  h

/-- On the dodge step, distinct diagonals yield distinct names at `none`. -/
theorem intervention_changes_dodge {A : Type} (f f' : A → A → Bool)
    (a : A) (h : f a a ≠ f' a a) :
    step f none (some a) ≠ step f' none (some a) := by
  show (!(f a a)) ≠ (!(f' a a))
  intro he
  exact h (Tower.not_inj he)

/-- On embedded old points, `stepEsc f e` agrees with `f`. -/
theorem intervention_preserves_past {A : Type} (f : A → A → Bool)
    (e : A → Bool) : ∀ a x : A, stepEsc f e (some a) (some x) = f a x :=
  fun _ _ => rfl

/-! ## Policies — free values and escape choice -/

/-- Policy: free values per tick, and at each tick a choice of which
    escape of the present reading to name at `none`. This is the
    escape-parameterised policy of the branching ladder: when frees are
    held at the default, it is a path in the escape tree (`Branch.Path`). -/
structure Policy where
  oldOnNew : (k : Nat) → Ladder.Level k → Bool
  selfVal : Nat → Bool
  /-- `escape k f` is the predicate named at tick `k` when the present
      reading is `f`. -/
  escape : (k : Nat) → (Ladder.Level k → Ladder.Level k → Bool) →
    (Ladder.Level k → Bool)

/-- Escape-only policy: free values fixed `false`; only which escape is
    named varies. Same type as `Policy`; well-formed instances with default
    frees are paths in the escape tree. -/
abbrev EscapePolicy := Policy

/-- Ladder readings under policy `π`. -/
def repP (π : Policy) : (k : Nat) → Ladder.Level k → Ladder.Level k → Bool
  | 0 => Tower.f₀
  | k + 1 => fun b x =>
    match b, x with
    | some a, some x' => repP π k a x'
    | none, some x' => π.escape k (repP π k) x'
    | some a, none => π.oldOnNew k a
    | none, none => π.selfVal k

/-- A policy is well-formed when each chosen escape misses every row of
    the induced reading. -/
def Policy.WF (π : Policy) : Prop :=
  ∀ k a, ∃ x, repP π k a x ≠ π.escape k (repP π k) x

/-- Default policy: free values `false`, name the dodge at every tick. -/
def dodgePolicy : Policy where
  oldOnNew := fun _ _ => false
  selfVal := fun _ => false
  escape := fun _ f x => !(f x x)

/-- The committed escape policy (all dodge, false frees). -/
def EscapePolicy.committed : EscapePolicy := dodgePolicy

theorem dodgePolicy_wf : dodgePolicy.WF := by
  intro k a
  refine ⟨a, ?_⟩
  intro he
  exact Diagonal.not_restless (repP dodgePolicy k a a) he.symm

/-- Every well-formed policy tick is a naming extension. -/
theorem repP_step (π : Policy) (hwf : π.WF) (k : Nat) :
    Tower.NamingExtension (repP π k) (repP π (k + 1)) some
      (π.escape k (repP π k)) :=
  ⟨fun _ _ => rfl, hwf k, ⟨none, fun _ => rfl⟩⟩

/-- `Ladder.rep` is `repP dodgePolicy`. -/
theorem ladder_is_default (k : Nat) :
    ∀ x y : Ladder.Level k,
      Ladder.rep k x y = repP dodgePolicy k x y := by
  induction k with
  | zero => intro x y; rfl
  | succ n ih =>
    intro x y
    cases x with
    | some a =>
      cases y with
      | some x' => exact ih a x'
      | none => rfl
    | none =>
      cases y with
      | some x' =>
        show (!(Ladder.rep n x' x')) = (!(repP dodgePolicy n x' x'))
        rw [ih x' x']
      | none => rfl

/-- Distinct free `selfVal` can yield distinct histories. -/
theorem policies_really_differ :
    ∃ π π' : Policy, ∃ k, ∃ x y : Ladder.Level k,
      repP π k x y ≠ repP π' k x y := by
  refine ⟨dodgePolicy,
    { dodgePolicy with selfVal := fun _ => true }, 1, none, none, ?_⟩
  show false ≠ true
  decide

/-- Equal chosen escapes at `k` force equal names at `none` in tick `k+1`. -/
theorem named_policy_independent (π π' : Policy) (k : Nat)
    (h : ∀ x : Ladder.Level k,
      π.escape k (repP π k) x = π'.escape k (repP π' k) x) :
    ∀ a : Ladder.Level k,
      repP π (k + 1) none (some a) = repP π' (k + 1) none (some a) :=
  fun a => h a

/-- Distinct `selfVal` under dodge-naming yields distinct content two ticks
    later. -/
theorem freedom_becomes_cause (k : Nat) :
    repP dodgePolicy (k + 2) none (some none) ≠
      repP { dodgePolicy with selfVal := fun _ => true }
        (k + 2) none (some none) := by
  show (!false) ≠ (!true)
  decide

/-- Policy naming a fixed escape `e` at tick `k` and the dodge elsewhere,
    with free values `false`. -/
def escapeAt (k : Nat) (e : Ladder.Level k → Bool) : Policy where
  oldOnNew := fun _ _ => false
  selfVal := fun _ => false
  escape := fun j f y =>
    match decEq j k with
    | isTrue h => e (h.symm ▸ y)
    | isFalse _ => !(f y y)

/-- If `j ≠ k`, then `escapeAt k e` names the dodge at tick `j`. -/
theorem escapeAt_ne (k j : Nat) (e : Ladder.Level k → Bool) (hne : j ≠ k)
    (f : Ladder.Level j → Ladder.Level j → Bool) (y : Ladder.Level j) :
    (escapeAt k e).escape j f y = !(f y y) := by
  dsimp [escapeAt]
  cases h : decEq j k with
  | isTrue heq => exact absurd heq hne
  | isFalse _ => rfl

/-- If `j < k`, then `escapeAt k e` names the dodge at tick `j`. -/
theorem escapeAt_lt (k j : Nat) (e : Ladder.Level k → Bool) (hj : j < k)
    (f : Ladder.Level j → Ladder.Level j → Bool) (y : Ladder.Level j) :
    (escapeAt k e).escape j f y = !(f y y) :=
  escapeAt_ne k j e (Nat.ne_of_lt hj) f y

/-- At tick `k`, `escapeAt k e` names `e`. -/
theorem escapeAt_eq (k : Nat) (e : Ladder.Level k → Bool)
    (f : Ladder.Level k → Ladder.Level k → Bool) (y : Ladder.Level k) :
    (escapeAt k e).escape k f y = e y := by
  dsimp [escapeAt]
  cases h : decEq k k with
  | isTrue _ => rfl
  | isFalse n => exact absurd rfl n

/-- `escapeAt k e` agrees with the committed ladder through level `k`. -/
theorem escapeAt_rep_le (k m : Nat) (e : Ladder.Level k → Bool)
    (hm : m ≤ k) :
    ∀ x y, repP (escapeAt k e) m x y = Ladder.rep m x y := by
  induction m with
  | zero => intro x y; rfl
  | succ n ih =>
    have hn : n < k := Nat.lt_of_succ_le hm
    have ih' := ih (Nat.le_of_lt hn)
    intro x y
    cases x with
    | some a =>
      cases y with
      | some x' => exact ih' a x'
      | none => rfl
    | none =>
      cases y with
      | some x' =>
        show (escapeAt k e).escape n (repP (escapeAt k e) n) x' =
          !(Ladder.rep n x' x')
        rw [escapeAt_lt k n e hn, ih' x' x']
      | none => rfl

/-- Well-formedness of `escapeAt` when `e` misses every row of
    `Ladder.rep k`. -/
theorem escapeAt_wf (k : Nat) (e : Ladder.Level k → Bool)
    (hm : ∀ a, ∃ x, Ladder.rep k a x ≠ e x) :
    (escapeAt k e).WF := by
  intro j a
  cases hd : decEq j k with
  | isTrue heq =>
    -- reduce the goal to level `k` by rewriting along `j = k`
    revert a
    show ∀ a, ∃ x, repP (escapeAt k e) j a x ≠
      (escapeAt k e).escape j (repP (escapeAt k e) j) x
    rw [heq]
    intro a
    obtain ⟨x, hx⟩ := hm a
    refine ⟨x, ?_⟩
    have hrep := escapeAt_rep_le k k e (Nat.le_refl k)
    show repP (escapeAt k e) k a x ≠
      (escapeAt k e).escape k (repP (escapeAt k e) k) x
    rw [escapeAt_eq, hrep a x]
    exact hx
  | isFalse hne =>
    refine ⟨a, ?_⟩
    have hesc := escapeAt_ne k j e hne (repP (escapeAt k e) j) a
    intro h
    have : repP (escapeAt k e) j a a = !(repP (escapeAt k e) j a a) :=
      h.trans hesc
    exact Diagonal.not_restless _ this.symm

/-- Escape choice at level `k`: two well-formed policies with distinct
    named content at tick `k+1`. -/
theorem escapes_differ_at (k : Nat) :
    ∃ π π' : Policy, π.WF ∧ π'.WF ∧
      ∃ x : Ladder.Level k,
        repP π (k + 1) none (some x) ≠
          repP π' (k + 1) none (some x) := by
  obtain ⟨e, e', ⟨x, hx⟩, he, he'⟩ :=
    Ladder.underdetermined_at_level k (Ladder.rep k)
  refine ⟨escapeAt k e, escapeAt k e', escapeAt_wf k e he,
    escapeAt_wf k e' he', x, ?_⟩
  show (escapeAt k e).escape k (repP (escapeAt k e) k) x ≠
    (escapeAt k e').escape k (repP (escapeAt k e') k) x
  rw [escapeAt_eq, escapeAt_eq]
  exact hx

/-- Distinct well-formed escape policies produce histories that disagree
    at the first tick where their named escapes differ. -/
theorem escape_policy_changes_history (k : Nat) :
    ∃ π π' : EscapePolicy, π.WF ∧ π'.WF ∧
      ∃ x : Ladder.Level k,
        repP π (k + 1) none (some x) ≠ repP π' (k + 1) none (some x) :=
  escapes_differ_at k

/-- Specialisation: two well-formed fundamental escape policies differ at the
    first naming. -/
theorem escapes_really_differ :
    ∃ π π' : Policy, π.WF ∧ π'.WF ∧
      ∃ x : Ladder.Level 0,
        repP π 1 none (some x) ≠ repP π' 1 none (some x) :=
  escapes_differ_at 0

/-- Underdetermination at the fundamental yields two well-formed first-step
    escape policies (rephrasing `escapes_really_differ`). -/
theorem escape_policies_from_underdetermination :
    ∃ π π' : Policy, π.WF ∧ π'.WF ∧
      ∃ x : Ladder.Level 0,
        repP π 1 none (some x) ≠ repP π' 1 none (some x) :=
  escapes_really_differ

/-! ## Summary -/

/-- Summary: determination, exact transmission, asymmetry, intervention,
    escape-parameterised policies, and delayed free-value effects. -/
theorem cause_package (act : α → α) (hs : Orbit.SymmetricStep act) :
    (∀ (A : Type) (f f' : A → A → α),
      (∀ x, f x x = f' x x) → ∀ a, effectOf act f a = effectOf act f' a) ∧
    (∀ (A : Type) (f f' : A → A → α) (a : A),
      effectOf act f a ≠ effectOf act f' a ↔ f a a ≠ f' a a) ∧
    (∀ k, (∀ a : Ladder.Level k,
      Ladder.rep (k + 1) none (some a) = !(Ladder.rep k a a)) ∧
      (∀ j, ∀ x y : Ladder.Level k,
        Ladder.rep (k + j) (Ladder.lift k j x) (Ladder.lift k j y) =
          Ladder.rep k x y)) ∧
    (∀ (A : Type) (f : A → A → Bool),
      Tower.NamingExtension f (step f) some (fun x => !(f x x))) ∧
    (∀ k, ∃ π π' : Policy, π.WF ∧ π'.WF ∧
      ∃ x : Ladder.Level k,
        repP π (k + 1) none (some x) ≠
          repP π' (k + 1) none (some x)) :=
  ⟨fun _ f f' h => same_cause_same_effect act f f' h,
   fun _ f f' a => fundamental_faithful act hs f f' a,
   causal_asymmetry,
   fun _ f => step_naming f,
   escapes_differ_at⟩

#print axioms Cause.same_cause_same_effect
#print axioms Cause.difference_transmitted
#print axioms Cause.transmission_exact
#print axioms Cause.fundamental_faithful
#print axioms Cause.erasure_breaks_transmission
#print axioms Cause.causal_asymmetry
#print axioms Cause.stepEsc_naming
#print axioms Cause.step_naming
#print axioms Cause.ladder_is_iterated_step
#print axioms Cause.intervention_changes_effect
#print axioms Cause.intervention_changes_dodge
#print axioms Cause.intervention_preserves_past
#print axioms Cause.dodgePolicy_wf
#print axioms Cause.repP_step
#print axioms Cause.ladder_is_default
#print axioms Cause.policies_really_differ
#print axioms Cause.named_policy_independent
#print axioms Cause.freedom_becomes_cause
#print axioms Cause.escapeAt_wf
#print axioms Cause.escapes_differ_at
#print axioms Cause.escape_policy_changes_history
#print axioms Cause.escapes_really_differ
#print axioms Cause.escape_policies_from_underdetermination
#print axioms Cause.cause_package

end Cause
