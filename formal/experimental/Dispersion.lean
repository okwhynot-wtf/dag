import Frequencies
import WaveEquation

/-!
# Dispersion (EXPERIMENTAL — quarantined; exports nothing to the paper)

Probe: the marriage of `Frequencies` and `WaveEquation`. The ring
wave's translation symmetry — rotation by one site — is itself a
shift on the index carrier `Fin (m + 1)`: rotation reads site
`i - 1`, and subtracting one is adding the top element `wIdx m` of
value `m` (`sub_one_eq_shift`, `rotF_eq_shift`). Iterated rotation
therefore transports to the iterated harmonic shift
(`iterN_rotF_eq_iterN_shift`), and the frequency gcd law computes
the exact order of the wave's cyclic symmetry group: consecutive
numbers are coprime (`gcd_succ_self`), so the law's predicted order
`(m + 1) / gcd (m + 1) m` is exactly `m + 1` (`predicted_order`).
Both halves are realised on the wave side: `m + 1` rotations restore
every field at every site (`rotF_order_returns`), and every smaller
positive rotation count moves some field at some site — an indicator
field witnesses it (`rotF_order_minimal`). The rotation lifts to
states componentwise (`iterN_rotS_components`), giving the state
symmetry the same order — return half `rotS_order_returns`,
minimality half `rotS_order_minimal`. Finally the
boundary-selected spectrum is constant on rotation orbits: a state
returns at time `T` exactly when any rotation power of it does
(`returns_iff_rot_pow_returns`, by induction from the single-step
invariance `Wave.return_iff_rot_return`). The headline bundle is
`symmetry_order_is_frequency_law`: the cyclic symmetry of the ring
wave has order exactly `m + 1 = (m + 1) / gcd (m + 1) m`, and
temporal periods are functions of the rotation orbit alone.

All statements are pointwise on sites and layers; no function
extensionality is used in this module. Stated honestly: this is the
discrete seed of a dispersion relation and no more — the order of
the spatial symmetry group and the orbit-invariance of the return
spectrum. There are no real frequencies, no dispersion relation over
the reals, and no continuum limit.
-/
namespace Experimental.Dispersion

/-! ## The rotation is a shift -/

/-- The top element of `Fin (m + 1)`, of value `m`. Adding it is
    subtracting one, so it presents the ring rotation as the `m`-th
    harmonic shift of `Frequencies`. -/
def wIdx (m : Nat) : Fin (m + 1) := ⟨m, Nat.lt_succ_self m⟩

/-- Subtracting one on `Fin (m + 1)` is shifting by the top element:
    `i - 1 = i + m` modulo `m + 1`, at value level. -/
theorem sub_one_eq_shift {m : Nat} (i : Fin (m + 1)) :
    i - 1 = Frequencies.shift (wIdx m) i := by
  cases m with
  | zero =>
    apply Fin.ext
    have h1 := (i - 1).isLt
    have h2 := (Frequencies.shift (wIdx 0) i).isLt
    omega
  | succ k =>
    apply Fin.ext
    rw [Fin.sub_def, Frequencies.shift_val]
    show (k + 1 + 1 - 1 % (k + 1 + 1) + i.val) % (k + 1 + 1)
        = (i.val + (k + 1)) % (k + 1 + 1)
    have h1 : 1 % (k + 1 + 1) = 1 := Nat.mod_eq_of_lt (by omega)
    rw [h1]
    have h2 : k + 1 + 1 - 1 + i.val = i.val + (k + 1) := by omega
    rw [h2]

/-- Index bridge: the ring rotation on fields reads through the
    harmonic shift by the top element, pointwise. -/
theorem rotF_eq_shift {m : Nat} (c : Wave.Field (m + 1))
    (i : Fin (m + 1)) :
    Wave.rotF c i = c (Frequencies.shift (wIdx m) i) :=
  congrArg c (sub_one_eq_shift i)

/-- Transport: iterated rotation of a field is the field read through
    the iterated shift, pointwise. Head-first folds on both sides;
    proved by induction on the iterate with the field generalised. -/
theorem iterN_rotF_eq_iterN_shift {m : Nat} (j : Nat)
    (c : Wave.Field (m + 1)) (i : Fin (m + 1)) :
    Wave.iterN Wave.rotF j c i
      = c (Frequencies.iterN (Frequencies.shift (wIdx m)) j i) := by
  induction j generalizing c with
  | zero => rfl
  | succ j ih =>
    show Wave.iterN Wave.rotF j (Wave.rotF c) i
        = c (Frequencies.iterN (Frequencies.shift (wIdx m)) (j + 1) i)
    rw [Frequencies.iterN_succ, ih (Wave.rotF c)]
    exact rotF_eq_shift c _

/-! ## Consecutive coprimality and the predicted order -/

/-- Consecutive numbers are coprime: the gcd divides both `m + 1`
    and `m`, hence their difference `1`. -/
theorem gcd_succ_self (m : Nat) : Nat.gcd (m + 1) m = 1 := by
  have h1 : Nat.gcd (m + 1) m ∣ m + 1 := Nat.gcd_dvd_left _ _
  have h2 : Nat.gcd (m + 1) m ∣ m := Nat.gcd_dvd_right _ _
  have h3 : Nat.gcd (m + 1) m ∣ m + 1 - m := Nat.dvd_sub h1 h2
  have h4 : m + 1 - m = 1 := by omega
  rw [h4] at h3
  exact Nat.dvd_one.mp h3

/-- The gcd law's predicted order for the rotation shift is the full
    carrier size: `(m + 1) / gcd (m + 1) m = m + 1`. -/
theorem predicted_order (m : Nat) :
    (m + 1) / Nat.gcd (m + 1) m = m + 1 := by
  rw [gcd_succ_self, Nat.div_one]

/-! ## The symmetry order, both halves -/

/-- Return half: `m + 1` rotations restore every field at every
    site — the transport lemma composed with the return half of the
    gcd law (`Frequencies.shift_order_returns`). -/
theorem rotF_order_returns {m : Nat} (c : Wave.Field (m + 1))
    (i : Fin (m + 1)) :
    Wave.iterN Wave.rotF (m + 1) c i = c i := by
  have h := Frequencies.shift_order_returns (wIdx m) i
  have hd : (m + 1) / Nat.gcd (m + 1) (wIdx m).val = m + 1 :=
    predicted_order m
  rw [hd] at h
  exact (iterN_rotF_eq_iterN_shift (m + 1) c i).trans (congrArg c h)

/-- Minimality half: every positive rotation count below `m + 1`
    moves some field at some site. The witness is the indicator field
    of site `0`, moved because the underlying shift iterate moves the
    site (`Frequencies.shift_order_minimal`). -/
theorem rotF_order_minimal {m j : Nat} (hj : 0 < j)
    (hlt : j < m + 1) :
    ∃ (c : Wave.Field (m + 1)) (i0 : Fin (m + 1)),
      Wave.iterN Wave.rotF j c i0 ≠ c i0 := by
  have hg : Nat.gcd (m + 1) (wIdx m).val = 1 := gcd_succ_self m
  have hlt' : j < (m + 1) / Nat.gcd (m + 1) (wIdx m).val := by
    rw [hg, Nat.div_one]; exact hlt
  have hne : Frequencies.iterN (Frequencies.shift (wIdx m)) j
      (0 : Fin (m + 1)) ≠ 0 :=
    Frequencies.shift_order_minimal (wIdx m) hj hlt' 0
  refine ⟨fun t => decide (t = (0 : Fin (m + 1))), 0, ?_⟩
  rw [iterN_rotF_eq_iterN_shift]
  show decide (Frequencies.iterN (Frequencies.shift (wIdx m)) j
        (0 : Fin (m + 1)) = 0)
      ≠ decide ((0 : Fin (m + 1)) = 0)
  intro h
  apply hne
  apply of_decide_eq_true
  rw [h]
  exact decide_eq_true rfl

/-! ## The state-level symmetry -/

/-- The state rotation iterates componentwise: each layer of the
    `j`-fold state rotation is the `j`-fold field rotation of that
    layer, pointwise. -/
theorem iterN_rotS_components {m : Nat} (j : Nat)
    (s : Wave.WState (m + 1)) :
    (∀ i, (Wave.iterN Wave.rotS j s).1 i
        = Wave.iterN Wave.rotF j s.1 i) ∧
    (∀ i, (Wave.iterN Wave.rotS j s).2 i
        = Wave.iterN Wave.rotF j s.2 i) := by
  induction j generalizing s with
  | zero => exact ⟨fun _ => rfl, fun _ => rfl⟩
  | succ j ih => exact ih (Wave.rotS s)

/-- Return half at state level: `m + 1` state rotations restore
    every state, pointwise on both layers. Minimality at state level
    is `rotS_order_minimal`. -/
theorem rotS_order_returns {m : Nat} (s : Wave.WState (m + 1)) :
    (∀ i, (Wave.iterN Wave.rotS (m + 1) s).1 i = s.1 i) ∧
    (∀ i, (Wave.iterN Wave.rotS (m + 1) s).2 i = s.2 i) :=
  ⟨fun i => ((iterN_rotS_components (m + 1) s).1 i).trans
      (rotF_order_returns s.1 i),
   fun i => ((iterN_rotS_components (m + 1) s).2 i).trans
      (rotF_order_returns s.2 i)⟩

/-- Minimality half at state level: every positive rotation count
    below `m + 1` moves some state on its first layer — the moved
    indicator field paired with itself. -/
theorem rotS_order_minimal {m j : Nat} (hj : 0 < j)
    (hlt : j < m + 1) :
    ∃ (s : Wave.WState (m + 1)) (i0 : Fin (m + 1)),
      (Wave.iterN Wave.rotS j s).1 i0 ≠ s.1 i0 := by
  obtain ⟨c, i0, hc⟩ := rotF_order_minimal (m := m) hj hlt
  refine ⟨(c, c), i0, ?_⟩
  rw [(iterN_rotS_components j (c, c)).1 i0]
  exact hc

/-! ## The spectrum is constant on rotation orbits -/

/-- Return of a state at time `T` under the ring wave, pointwise on
    both layers — the return notion of
    `Wave.return_iff_rot_return`. -/
def Returns {m : Nat} (T : Nat) (s : Wave.WState (m + 1)) : Prop :=
  (∀ i, (Wave.iterN (Wave.step Wave.ringX) T s).1 i = s.1 i) ∧
  (∀ i, (Wave.iterN (Wave.step Wave.ringX) T s).2 i = s.2 i)

/-- The return spectrum is constant on rotation orbits: a state
    returns at time `T` exactly when any rotation power of it does.
    Induction on the power from the single-step invariance
    (`Wave.return_iff_rot_return`). -/
theorem returns_iff_rot_pow_returns {m : Nat} (T j : Nat)
    (s : Wave.WState (m + 1)) :
    Returns T s ↔ Returns T (Wave.iterN Wave.rotS j s) := by
  induction j generalizing s with
  | zero => exact Iff.rfl
  | succ j ih =>
    exact (Wave.return_iff_rot_return T s).trans (ih (Wave.rotS s))

/-! ## Headline -/

/-- **The symmetry order is the frequency law.** The gcd law of
    `Frequencies` predicts order `(m + 1) / gcd (m + 1) m = m + 1`
    for the ring rotation, and the ring wave realises it exactly:
    `m + 1` rotations restore every field, every smaller positive
    count moves some field, and temporal periods are functions of
    the rotation orbit alone. -/
theorem symmetry_order_is_frequency_law {m : Nat} :
    (m + 1) / Nat.gcd (m + 1) m = m + 1 ∧
    (∀ (c : Wave.Field (m + 1)) (i : Fin (m + 1)),
      Wave.iterN Wave.rotF (m + 1) c i = c i) ∧
    (∀ j, 0 < j → j < m + 1 →
      ∃ (c : Wave.Field (m + 1)) (i0 : Fin (m + 1)),
        Wave.iterN Wave.rotF j c i0 ≠ c i0) ∧
    (∀ (T j : Nat) (s : Wave.WState (m + 1)),
      Returns T s ↔ Returns T (Wave.iterN Wave.rotS j s)) :=
  ⟨predicted_order m, rotF_order_returns,
    fun _j hj hlt => rotF_order_minimal hj hlt,
    fun T j s => returns_iff_rot_pow_returns T j s⟩

#print axioms Experimental.Dispersion.sub_one_eq_shift
#print axioms Experimental.Dispersion.rotF_eq_shift
#print axioms Experimental.Dispersion.iterN_rotF_eq_iterN_shift
#print axioms Experimental.Dispersion.gcd_succ_self
#print axioms Experimental.Dispersion.predicted_order
#print axioms Experimental.Dispersion.rotF_order_returns
#print axioms Experimental.Dispersion.rotF_order_minimal
#print axioms Experimental.Dispersion.iterN_rotS_components
#print axioms Experimental.Dispersion.rotS_order_returns
#print axioms Experimental.Dispersion.rotS_order_minimal
#print axioms Experimental.Dispersion.returns_iff_rot_pow_returns
#print axioms Experimental.Dispersion.symmetry_order_is_frequency_law

end Experimental.Dispersion
