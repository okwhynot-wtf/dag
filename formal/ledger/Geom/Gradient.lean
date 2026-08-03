import Geom.Bounce
import Geom.Provision

/-!
# Geom.Gradient

Eternal alive schedules force a non-flat capacity profile. The bounce profile
is reversal-symmetric; each ascent carries expanding-conveyor capacity.
-/


namespace Geom.Gradient

open Geom.Bounce

/-! ### Arithmetic helpers -/

/-- `a + b - b = a`, from the prelude by induction. -/
theorem add_sub_self : ∀ a b : Nat, a + b - b = a := by
  intro a b
  induction b with
  | zero => rfl
  | succ n ih =>
    show a + n + 1 - (n + 1) = a
    rw [Nat.succ_sub_succ]
    exact ih

/-- `a + b - a = b`, via commutativity. -/
theorem add_sub_self_left (a b : Nat) : a + b - a = b := by
  rw [Nat.add_comm]
  exact add_sub_self b a

/-- `b <= a -> (a - b) + b = a`, from the prelude by induction. -/
theorem sub_add_self : ∀ a b : Nat, b ≤ a → (a - b) + b = a := by
  intro a b
  induction b generalizing a with
  | zero => intro _; rfl
  | succ n ih =>
    intro h
    cases a with
    | zero => cases h
    | succ m =>
      show (m + 1 - (n + 1)) + (n + 1) = m + 1
      rw [Nat.succ_sub_succ]
      show ((m - n) + n) + 1 = m + 1
      rw [ih m (Nat.le_of_succ_le_succ h)]

/-- Left cancellation for `<=`, from the prelude by induction. -/
theorem le_cancel_left : ∀ a b c : Nat, a + b ≤ a + c → b ≤ c := by
  intro a
  induction a with
  | zero =>
    intro b c h
    rw [Nat.zero_add, Nat.zero_add] at h
    exact h
  | succ n ih =>
    intro b c h
    rw [Nat.succ_add, Nat.succ_add] at h
    exact ih b c (Nat.le_of_succ_le_succ h)

/-- Right cancellation for `=`, from the prelude by induction. -/
theorem add_cancel_right : ∀ a b c : Nat, a + c = b + c → a = b := by
  intro a b c
  induction c with
  | zero => intro h; exact h
  | succ n ih =>
    intro h
    exact ih (Nat.succ.inj h)

/-! ### Flatness forbids eternal aliveness -/

/-- **Eternal aliveness needs a gradient.** If every horizon is alive
against the profile (`K^T <= K^(prof T)`, `K >= 2`), no constant
profile works: the profile must dominate the diagonal, and a flat
profile at height `C` dies at horizon `C+1`. Non-flatness is derived
from eternal aliveness, not assumed. -/
theorem eternal_aliveness_needs_gradient {K : Nat} (hK : 2 ≤ K)
    (prof : Nat → Nat)
    (halive : ∀ T : Nat, K ^ T ≤ K ^ prof T) :
    ∀ C : Nat, ¬ (∀ t : Nat, prof t = C) := by
  intro C hflat
  have h1 : C + 1 ≤ prof (C + 1) :=
    (pow_le_pow_iff_le hK (C + 1) (prof (C + 1))).mp (halive (C + 1))
  rw [hflat (C + 1)] at h1
  exact Nat.not_succ_le_self C h1

/-! ### The gradient carries no orientation -/

/-- Auxiliary: `(T+1) + (T+1) = (T+T) + 2`. -/
theorem succ_add_succ (T : Nat) : (T + 1) + (T + 1) = (T + T) + 2 := by
  rw [Nat.succ_add]
  rfl

/-- **Reversal symmetry of the bounce.** Indices summing to `2*tTurn`
share their depth: the profile read backwards is the profile. The
gradient is undirected. -/
theorem bounce_symm (tTurn : Nat) :
    ∀ a b : Nat, a + b = 2 * tTurn →
      bounceDepth tTurn a = bounceDepth tTurn b := by
  intro a b h
  have h2 : a + b = tTurn + tTurn := by rw [h, two_mul_eq_add]
  cases Nat.decLe a tTurn with
  | isTrue ha =>
    cases Nat.decLe b tTurn with
    | isTrue hb =>
      -- both at or below the turnaround: forces a = b = tTurn
      have hbT : tTurn ≤ b := by
        have hle : a + b ≤ tTurn + b := Nat.add_le_add ha (Nat.le_refl b)
        rw [h2] at hle
        exact le_cancel_left tTurn tTurn b hle
      have hbeq : b = tTurn := Nat.le_antisymm hb hbT
      have haeq : a = tTurn := by
        have hh : a + b = tTurn + tTurn := h2
        rw [hbeq] at hh
        exact add_cancel_right a tTurn tTurn hh
      rw [haeq, hbeq]
    | isFalse hb =>
      have hbgt : tTurn < b := lt_of_not_le hb
      have hb2 : b ≤ 2 * tTurn := h ▸ Nat.le_add_left b a
      rw [bounceDepth_asc ha, bounceDepth_desc hbgt hb2, ← h,
          add_sub_self a b]
  | isFalse ha =>
    have hagt : tTurn < a := lt_of_not_le ha
    have ha2 : a ≤ 2 * tTurn := h ▸ Nat.le_add_right a b
    cases Nat.decLe b tTurn with
    | isTrue hb =>
      rw [bounceDepth_asc hb, bounceDepth_desc hagt ha2, ← h,
          add_sub_self_left a b]
    | isFalse hb =>
      -- both above the turnaround: impossible
      have hbgt : tTurn < b := lt_of_not_le hb
      have hs : (tTurn + 1) + (tTurn + 1) ≤ a + b :=
        Nat.add_le_add (Nat.succ_le_of_lt hagt) (Nat.succ_le_of_lt hbgt)
      rw [h2, succ_add_succ] at hs
      exact absurd (Nat.le_of_succ_le hs)
        (Nat.not_succ_le_self (tTurn + tTurn))

/-- The reversed reading's profile: depth at its own elapsed horizon
`τ` is the forward depth at absolute index `2*tTurn − τ`. -/
def revDepth (tTurn τ : Nat) : Nat := bounceDepth tTurn (2 * tTurn - τ)

/-- **The two readings see one profile.** Within the window, the
reversed reading's capacity profile equals the forward one, horizon by
horizon. -/
theorem rev_depth_eq (tTurn τ : Nat) (h : τ ≤ 2 * tTurn) :
    revDepth tTurn τ = bounceDepth tTurn τ :=
  bounce_symm tTurn (2 * tTurn - τ) τ (sub_add_self (2 * tTurn) τ h)

/-- **Both readings share the alive window.** Alive in the reversed
reading iff alive in the forward one; both windows are `{0..tTurn}` and
exhaustion is the shared turnaround. Two opposed readings, one
undirected gradient. -/
theorem readings_share_window {K : Nat} (hK : 2 ≤ K)
    (tTurn τ : Nat) (h : τ ≤ 2 * tTurn) :
    (K ^ τ ≤ K ^ revDepth tTurn τ ↔ Alive K tTurn τ)
    ∧ (Alive K tTurn τ ↔ τ ≤ tTurn) := by
  refine ⟨?_, exhaustion_tick_eq_turnaround hK tTurn τ⟩
  rw [rev_depth_eq tTurn τ h]
  exact Iff.rfl

/-!
# Geom.Gradient

Eternal alive schedules force a non-flat capacity profile. The bounce profile
is reversal-symmetric; each ascent carries expanding-conveyor capacity.
-/

/-- **Ascending branch is Provision (weld).** Within its ascent, each
reading's capacity is exactly the expanding conveyor's:
`|expandCaps A t| = |A| ^ depth t`. The directed Expansion Hypothesis
holds locally, per reading, as a theorem; orientation is supplied per
observer by the Janus and selection theorems. -/
theorem ascending_is_provision {Eout : Type} (A : List Eout)
    (tTurn t : Nat) (h : t ≤ tTurn) :
    (Geom.Provision.expandCaps (Eout := Eout) A t).length
      = A.length ^ Geom.Bounce.bounceDepth tTurn t := by
  rw [bounceDepth_asc h]
  exact Geom.Provision.expand_capacity (Eout := Eout) (A := A) t

/-- Orientation-free package: eternal alive ⇒ non-flat profile; bounce
symmetry; shared alive window; ascent capacity equals the expanding
conveyor. -/
theorem orientation_free {Eout : Type} (A : List Eout) {K : Nat}
    (hK : 2 ≤ K) (tTurn τ t : Nat) (hτ : τ ≤ 2 * tTurn) (ht : t ≤ tTurn) :
    (∀ prof : Nat → Nat, (∀ T : Nat, K ^ T ≤ K ^ prof T) →
        ∀ C : Nat, ¬ (∀ u : Nat, prof u = C))
    ∧ revDepth tTurn τ = bounceDepth tTurn τ
    ∧ (Alive K tTurn τ ↔ τ ≤ tTurn)
    ∧ (Geom.Provision.expandCaps (Eout := Eout) A t).length
        = A.length ^ Geom.Bounce.bounceDepth tTurn t :=
  ⟨fun prof halive => eternal_aliveness_needs_gradient hK prof halive,
   rev_depth_eq tTurn τ hτ,
   exhaustion_tick_eq_turnaround hK tTurn τ,
   ascending_is_provision A tTurn t ht⟩

end Geom.Gradient

-- #print axioms
#print axioms Geom.Gradient.add_sub_self
#print axioms Geom.Gradient.add_sub_self_left
#print axioms Geom.Gradient.sub_add_self
#print axioms Geom.Gradient.le_cancel_left
#print axioms Geom.Gradient.add_cancel_right
#print axioms Geom.Gradient.eternal_aliveness_needs_gradient
#print axioms Geom.Gradient.succ_add_succ
#print axioms Geom.Gradient.bounce_symm
#print axioms Geom.Gradient.rev_depth_eq
#print axioms Geom.Gradient.readings_share_window
#print axioms Geom.Gradient.ascending_is_provision
#print axioms Geom.Gradient.orientation_free
