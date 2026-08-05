import WaveEquation

/-!
# DynamicsAmbient (EXPERIMENTAL) — classification of couplings

The dynamics-layer twin of the ambient-uniqueness theorem. The static
half of the system earns its kernel by elimination; this module earns
the equation of motion the same way, in two stages.

**Stage one — reversibility forces the xor form.** A general
second-order nearest-neighbour update is
`next i = F (prev i) (cur (i-1)) (cur i) (cur (i+1))` for an arbitrary
`F : Bool⁴ → Bool`. If `F` fails to toggle in its previous-layer slot
at even one neighbourhood, an explicit two-history collision exists on
the three-ring: the step erases, pointwise and axiom-free
(`collision_of_not_toggling`). If `F` toggles everywhere, then `F` *is*
the xor form `F p l m r = p ^^ G l m r` with `G := F false`
(`toggle_forces_xor_form`), and every xor-form step is lossless with an
explicit two-bounce factorisation and swap-reversal, by the general
theorems of `WaveEquation`. Losslessness therefore selects the
second-order xor structure; it is derived, never chosen.

**Stage two — the ambient selects the coupling.** The residual freedom
is the coupling `G`. Declaring the coupling *inter-site* (it relates
the neighbours; the site's own influence is already carried, exactly
once, by the toggling slot) leaves `K : Bool → Bool → Bool`. The
ambient conditions mirror the static classification: parity
(`K l r = K r l`, no smuggled spatial arrow), pole invariance
(`K (¬l) (¬r) = K l r`, the label gauge is respected), and a drawing
condition (`K` takes two values; a coupling that draws no distinction
couples nothing). The survivors are exactly `xor` and its pointwise
flip `¬xor` (`coupling_uniqueness`), a single orbit of the flip
involution on couplings — one live coupling up to the label gauge,
the same `Z/2Z` as everywhere else. The survivor's dynamics is the
wave step of `WaveEquation` on the nose
(`survivor_is_wave_coupling`), so the classified dynamics inherits,
definitionally, the two-bounce form and swap-reversal.

Status: quarantined; candidate for promotion as the second eliminative
classification of a complete system.
-/
namespace Experimental.DynamicsAmbient

open Experimental.Wave

/-! ## Stage one: reversibility forces the xor form -/

/-- If the update toggles in the previous-layer slot at every
    neighbourhood, it is the xor form: `F p l m r = p ^^ F false l m r`. -/
theorem toggle_forces_xor_form
    (F : Bool → Bool → Bool → Bool → Bool)
    (h : ∀ l m r, F true l m r ≠ F false l m r) :
    ∀ p l m r, F p l m r = (p ^^ F false l m r) := by
  intro p l m r
  cases p with
  | false =>
    show F false l m r = (false ^^ F false l m r)
    rw [Bool.false_xor]
  | true =>
    have hne := h l m r
    show F true l m r = (true ^^ F false l m r)
    rw [Bool.true_xor]
    cases hT : F true l m r <;> cases hF : F false l m r
    · rw [hT, hF] at hne; exact absurd rfl hne
    · rfl
    · rfl
    · rw [hT, hF] at hne; exact absurd rfl hne

/-- The general second-order nearest-neighbour step on the three-ring. -/
def gstep (F : Bool → Bool → Bool → Bool → Bool) (s : WState 3) :
    WState 3 :=
  (s.2, fun i => F (s.1 i) (s.2 (i - 1)) (s.2 i) (s.2 (i + 1)))

/-- Neighbourhood configuration realising `(l, m, r)` at site 1. -/
def cfg (l m r : Bool) : Field 3 := fun i =>
  if i.val = 0 then l else if i.val = 1 then m else r

/-- If the update fails to toggle at some neighbourhood, two histories
    on the three-ring agree after one step at every site while
    differing at site 1: the step erases. Pointwise and axiom-free. -/
theorem collision_of_not_toggling
    (F : Bool → Bool → Bool → Bool → Bool) (l m r : Bool)
    (h : F true l m r = F false l m r) :
    (∀ i, (gstep F (fun _ => false, cfg l m r)).1 i =
      (gstep F (fun i => decide (i.val = 1), cfg l m r)).1 i) ∧
    (∀ i, (gstep F (fun _ => false, cfg l m r)).2 i =
      (gstep F (fun i => decide (i.val = 1), cfg l m r)).2 i) ∧
    ((fun _ => false) : Fin 3 → Bool) 1 ≠
      (fun i : Fin 3 => decide (i.val = 1)) 1 := by
  refine ⟨fun _ => rfl, ?_, fun hcontra => Bool.noConfusion hcontra⟩
  intro i
  match i with
  | ⟨0, _⟩ => rfl
  | ⟨1, _⟩ =>
    show F false l m r = F (decide ((1 : Nat) = 1)) l m r
    rw [show decide ((1 : Nat) = 1) = true from rfl, h]
  | ⟨2, _⟩ => rfl
  | ⟨n + 3, hn⟩ =>
    exact absurd hn (Nat.not_lt.mpr (Nat.le_add_left 3 n))

/-! ## Stage two: the ambient selects the coupling -/

/-- **Coupling uniqueness.** Under parity, pole invariance, and the
    drawing condition, the coupling is `xor` or its pointwise flip:
    one live coupling, one orbit of the flip involution, the same
    `Z/2Z` as the label gauge. -/
theorem coupling_uniqueness (K : Bool → Bool → Bool)
    (hpar : ∀ l r, K l r = K r l)
    (hcomp : ∀ l r, K (!l) (!r) = K l r)
    (hdraw : ∃ l r l' r', K l r ≠ K l' r') :
    (∀ l r, K l r = (l ^^ r)) ∨ (∀ l r, K l r = !(l ^^ r)) := by
  have hTF : K true false = K false true := (hpar false true).symm
  have hTT : K true true = K false false := hcomp false false
  cases ha : K false false <;> cases hb : K false true
  · -- all four values false: the coupling draws nothing
    exfalso
    have hall : ∀ l r, K l r = false := by
      intro l r
      cases l <;> cases r
      · exact ha
      · exact hb
      · exact hTF.trans hb
      · exact hTT.trans ha
    obtain ⟨l, r, l', r', hne⟩ := hdraw
    rw [hall l r, hall l' r'] at hne
    exact hne rfl
  · -- values (false, true): the coupling is xor
    left
    intro l r
    cases l <;> cases r
    · exact ha
    · exact hb
    · exact hTF.trans hb
    · exact hTT.trans ha
  · -- values (true, false): the coupling is the flipped xor
    right
    intro l r
    cases l <;> cases r
    · exact ha
    · exact hb
    · exact hTF.trans hb
    · exact hTT.trans ha
  · -- all four values true: the coupling draws nothing
    exfalso
    have hall : ∀ l r, K l r = true := by
      intro l r
      cases l <;> cases r
      · exact ha
      · exact hb
      · exact hTF.trans hb
      · exact hTT.trans ha
    obtain ⟨l, r, l', r', hne⟩ := hdraw
    rw [hall l r, hall l' r'] at hne
    exact hne rfl

/-- The flip is an involution on couplings, pointwise. -/
theorem flip_involution (K : Bool → Bool → Bool) :
    ∀ l r, (!(!(K l r))) = K l r := by
  intro l r
  cases K l r <;> rfl

/-- The two survivors are one orbit of the flip, pointwise. -/
theorem survivors_one_orbit :
    ∀ l r : Bool, (!(l ^^ r)) = (!(l ^^ r)) ∧
      (!(!(l ^^ r))) = (l ^^ r) := by
  intro l r
  exact ⟨rfl, by cases l <;> cases r <;> rfl⟩

/-- The surviving coupling instantiated on the ring is the wave
    coupling of `WaveEquation`, definitionally. -/
theorem survivor_is_wave_coupling {m : Nat} (c : Field (m + 1))
    (i : Fin (m + 1)) :
    (c (i - 1) ^^ c (i + 1)) = ringX c i := rfl

/-! ## The package -/

/-- **Dynamics-ambient uniqueness.** (I) Toggling forces the xor form.
    (II) A non-toggling update erases on the three-ring, exhibited
    pointwise. (III) Parity, pole invariance, and the drawing
    condition force the coupling into the single flip-orbit
    `{xor, ¬xor}`. (IV) The survivor's ring dynamics is the wave step,
    hence two-bounce with swap-reversal by the general theorems of
    `WaveEquation`. -/
theorem dynamics_ambient_uniqueness :
    (∀ (F : Bool → Bool → Bool → Bool → Bool),
      (∀ l m r, F true l m r ≠ F false l m r) →
      ∀ p l m r, F p l m r = (p ^^ F false l m r)) ∧
    (∀ (F : Bool → Bool → Bool → Bool → Bool) (l m r : Bool),
      F true l m r = F false l m r →
      (∀ i, (gstep F (fun _ => false, cfg l m r)).2 i =
        (gstep F (fun i => decide (i.val = 1), cfg l m r)).2 i)) ∧
    (∀ (K : Bool → Bool → Bool),
      (∀ l r, K l r = K r l) →
      (∀ l r, K (!l) (!r) = K l r) →
      (∃ l r l' r', K l r ≠ K l' r') →
      (∀ l r, K l r = (l ^^ r)) ∨ (∀ l r, K l r = !(l ^^ r))) ∧
    (∀ {m : Nat} (c : Field (m + 1)) (i : Fin (m + 1)),
      (c (i - 1) ^^ c (i + 1)) = ringX c i) :=
  ⟨toggle_forces_xor_form,
   fun F l m r h => (collision_of_not_toggling F l m r h).2.1,
   coupling_uniqueness,
   fun c i => survivor_is_wave_coupling c i⟩

#print axioms Experimental.DynamicsAmbient.toggle_forces_xor_form
#print axioms Experimental.DynamicsAmbient.collision_of_not_toggling
#print axioms Experimental.DynamicsAmbient.coupling_uniqueness
#print axioms Experimental.DynamicsAmbient.dynamics_ambient_uniqueness

end Experimental.DynamicsAmbient
