import Orbit
import Density
import Geom.Registration

/-!
# TwoBounce — I-1 losslessness as two arena bounces

Classical fact (finite carriers): a self-map is bijective iff it factors as
a composition of two involutions. Spine acts are involutions
(`SymmetricStep`); ledger joint steps `U` are forward-composing.

Landed here:
* involution ⇒ lossless ⇒ ¬Erasing (spine packaging)
* two-bounce ⇒ `Lossless` / product-`Inj` (converse half)
* existence when `U` is already an involution (`U = U ∘ id`)
* existence on `Bool` (every injection is an involution)
* existence for ledger `swapStep`
* existence for every injection on `Fin n` (cycle-wise reflect)

Settled:
* canonicity fails (essential non-uniqueness of `(φ, σ)`)
* involutive reordering is T-7-shaped; Fin-3 axis choice is a larger
  factorization gauge, not a second dictionary ℤ/2 face
* channel identification with dictionary `φ`, `σ` stays suggestive

No Mathlib; no `sorry`; no declared axioms.
-/
namespace Bridge.TwoBounce

open Orbit

/-! ## Involutions -/

/-- An involution: `f ∘ f = id`. Spine `SymmetricStep` is this shape. -/
def IsInvolution {α : Type} (f : α → α) : Prop :=
  ∀ x, f (f x) = x

theorem involution_of_symmetric {α : Type} (act : α → α)
    (hs : SymmetricStep act) : IsInvolution act :=
  (symmetricStep_iff_involutive act).mp hs

theorem symmetric_of_involution {α : Type} (act : α → α)
    (h : IsInvolution act) : SymmetricStep act :=
  (symmetricStep_iff_involutive act).mpr h

/-- Involutions are injective (= lossless). -/
theorem involution_injective {α : Type} (f : α → α) (h : IsInvolution f) :
    Lossless f := by
  intro x y heq
  have := congrArg f heq
  rw [h x, h y] at this
  exact this

/-- Involutive acts cannot erase. -/
theorem involution_not_erasing {α : Type} (f : α → α) (h : IsInvolution f) :
    ¬ Erasing f := by
  intro ⟨x, y, hne, heq⟩
  exact hne (involution_injective f h x y heq)

/-- Spine packaging: `SymmetricStep` excludes `Erasing`. -/
theorem symmetric_excludes_erase {α : Type} (act : α → α)
    (hs : SymmetricStep act) : ¬ Erasing act :=
  involution_not_erasing act (involution_of_symmetric act hs)

/-! ## Two-bounce factorisation -/

/-- Witness that `U` factors as `σ ∘ φ` with both factors involutions. -/
structure TwoBounceFactor {α : Type} (U : α → α) where
  /-- First bounce. -/
  φ : α → α
  /-- Second bounce. -/
  σ : α → α
  φ_inv : IsInvolution φ
  σ_inv : IsInvolution σ
  factor : ∀ x, U x = σ (φ x)

/-- Converse: two-bounce form ⇒ lossless. -/
theorem lossless_of_two_bounce {α : Type} (U : α → α)
    (f : TwoBounceFactor U) : Lossless U := by
  intro a b h
  have hσ : f.σ (f.φ a) = f.σ (f.φ b) := by
    rw [← f.factor a, ← f.factor b, h]
  have hφ : f.φ a = f.φ b := involution_injective f.σ f.σ_inv _ _ hσ
  exact involution_injective f.φ f.φ_inv _ _ hφ

/-- On a product carrier, two-bounce ⇒ ledger `Inj`. -/
theorem inj_of_two_bounce {S E : Type} (U : S × E → S × E)
    (f : TwoBounceFactor U) : Geom.Registration.Inj U :=
  lossless_of_two_bounce U f

/-- Any involution is already a two-bounce (`U = U ∘ id`). -/
def factor_involution {α : Type} (U : α → α) (h : IsInvolution U) :
    TwoBounceFactor U where
  φ := id
  σ := U
  φ_inv := fun _ => rfl
  σ_inv := h
  factor := fun _ => rfl

/-- Reverse packing of an involution (`U = id ∘ U`). -/
def factor_involution_rev {α : Type} (U : α → α) (h : IsInvolution U) :
    TwoBounceFactor U where
  φ := U
  σ := id
  φ_inv := h
  σ_inv := fun _ => rfl
  factor := fun _ => rfl

/-! ## `Bool` and ledger toys -/

/-- Endomap injectivity (carrier-agnostic). -/
def EndoInj {α : Type} (U : α → α) : Prop :=
  ∀ a b, U a = U b → a = b

theorem bool_inj_involution (U : Bool → Bool) (h : EndoInj U) :
    IsInvolution U := by
  intro x
  cases hf : U false with
  | false =>
    cases ht : U true with
    | false =>
      have : false = true := h false true (hf.trans ht.symm)
      cases this
    | true => cases x <;> simp [hf, ht]
  | true =>
    cases ht : U true with
    | false => cases x <;> simp [hf, ht]
    | true =>
      have : false = true := h false true (hf.trans ht.symm)
      cases this

def factor_bool (U : Bool → Bool) (h : EndoInj U) :
    TwoBounceFactor U :=
  factor_involution U (bool_inj_involution U h)

theorem swapStep_involution :
    IsInvolution Geom.Registration.swapStep := by
  intro p; cases p; rfl

def factor_swapStep : TwoBounceFactor Geom.Registration.swapStep :=
  factor_involution _ swapStep_involution

/-! ## `Fin n`: cycle-wise reflect -/

/-- On a finite carrier every orbit collides (pigeon on iterates `0..n`). -/
theorem fin_collides {n : Nat} (U : Fin n → Fin n) (z : Fin n) :
    Collides U z := by
  let f : Nat → Nat := fun i => (iter U i z).val
  have hb : ∀ i, i < n + 1 → f i < n := fun i _ => (iter U i z).isLt
  refine Classical.byContradiction fun hnc => ?_
  have hinj : ∀ i j, i < n + 1 → j < n + 1 → f i = f j → i = j := by
    intro i j _hi _hj heq
    have he : iter U i z = iter U j z := Fin.eq_of_val_eq heq
    cases Nat.lt_trichotomy i j with
    | inl hlt => exact absurd ⟨i, j, hlt, he⟩ hnc
    | inr hrest =>
      cases hrest with
      | inl heqij => exact heqij
      | inr hgt => exact absurd ⟨j, i, hgt, he.symm⟩ hnc
  exact Density.no_distinct_large n f hb hinj

/-- Injectivity + finitude ⇒ every seed returns. -/
theorem fin_returns {n : Nat} (U : Fin n → Fin n) (h : EndoInj U) (z : Fin n) :
    ∃ p : Nat, 0 < p ∧ iter U p z = z :=
  collision_returns U h z (fin_collides U z)

/-- Among return times, a least positive period exists. -/
theorem exists_min_period {n : Nat} (U : Fin n → Fin n) (h : EndoInj U)
    (z : Fin n) :
    ∃ p : Nat, 0 < p ∧ iter U p z = z ∧
      ∀ k, 0 < k → k < p → iter U k z ≠ z := by
  obtain ⟨p0, hp0, hret0⟩ := fin_returns U h z
  have go : ∀ p : Nat, 0 < p → iter U p z = z →
      ∃ q, 0 < q ∧ q ≤ p ∧ iter U q z = z ∧
        ∀ k, 0 < k → k < q → iter U k z ≠ z := by
    intro p
    refine Nat.strongRecOn p ?_
    intro p ih hp hret
    if hmin : ∀ k, 0 < k → k < p → iter U k z ≠ z then
      exact ⟨p, hp, Nat.le_refl p, hret, hmin⟩
    else
      have hex : ∃ k, 0 < k ∧ k < p ∧ iter U k z = z := by
        refine Classical.byContradiction fun hx => ?_
        exact hmin (fun k hk0 hkp heq => hx ⟨k, hk0, hkp, heq⟩)
      obtain ⟨k, hk0, hkp, hkret⟩ := hex
      obtain ⟨q, hq0, hqp, hqret, hqmin⟩ := ih k hkp hk0 hkret
      exact ⟨q, hq0, Nat.le_trans hqp (Nat.le_of_lt hkp), hqret, hqmin⟩
  obtain ⟨q, hq0, _, hqret, hqmin⟩ := go p0 hp0 hret0
  exact ⟨q, hq0, hqret, hqmin⟩

/-- Least positive return time at `z`. -/
noncomputable def minPeriod {n : Nat} (U : Fin n → Fin n) (h : EndoInj U)
    (z : Fin n) : Nat :=
  Classical.choose (exists_min_period U h z)

theorem minPeriod_pos {n : Nat} (U : Fin n → Fin n) (h : EndoInj U)
    (z : Fin n) : 0 < minPeriod U h z :=
  (Classical.choose_spec (exists_min_period U h z)).1

theorem minPeriod_return {n : Nat} (U : Fin n → Fin n) (h : EndoInj U)
    (z : Fin n) : iter U (minPeriod U h z) z = z :=
  (Classical.choose_spec (exists_min_period U h z)).2.1

theorem minPeriod_least {n : Nat} (U : Fin n → Fin n) (h : EndoInj U)
    (z : Fin n) : ∀ k, 0 < k → k < minPeriod U h z → iter U k z ≠ z :=
  (Classical.choose_spec (exists_min_period U h z)).2.2

/-- First `p` iterates from a least-period seed are pairwise distinct. -/
theorem orbit_distinct {n : Nat} (U : Fin n → Fin n) (h : EndoInj U)
    (z : Fin n) :
    ∀ i j, i < minPeriod U h z → j < minPeriod U h z →
      iter U i z = iter U j z → i = j := by
  intro i j hi hj heq
  cases Nat.lt_trichotomy i j with
  | inl hlt =>
    have hdpos : 0 < j - i := Nat.sub_pos_of_lt hlt
    have hdlt : j - i < minPeriod U h z :=
      Nat.lt_of_le_of_lt (Nat.sub_le j i) hj
    have hsum : i + (j - i) = j := Nat.add_sub_of_le (Nat.le_of_lt hlt)
    have hstep : iter U i (iter U (j - i) z) = iter U i z := by
      rw [← iter_add, hsum, heq]
    have key : iter U (j - i) z = z := iter_lossless U h i _ _ hstep
    exact absurd key (minPeriod_least U h z (j - i) hdpos hdlt)
  | inr hrest =>
    cases hrest with
    | inl heqij => exact heqij
    | inr hgt =>
      have hdpos : 0 < i - j := Nat.sub_pos_of_lt hgt
      have hdlt : i - j < minPeriod U h z :=
        Nat.lt_of_le_of_lt (Nat.sub_le i j) hi
      have hsum : j + (i - j) = i := Nat.add_sub_of_le (Nat.le_of_lt hgt)
      have hstep : iter U j (iter U (i - j) z) = iter U j z := by
        rw [← iter_add, hsum, heq.symm]
      have key : iter U (i - j) z = z := iter_lossless U h j _ _ hstep
      exact absurd key (minPeriod_least U h z (i - j) hdpos hdlt)

/-- Period is invariant under moving along the orbit. -/
theorem minPeriod_iter {n : Nat} (U : Fin n → Fin n) (h : EndoInj U)
    (z : Fin n) (t : Nat) :
    minPeriod U h (iter U t z) = minPeriod U h z := by
  let p := minPeriod U h z
  let q := minPeriod U h (iter U t z)
  have hp : 0 < p := minPeriod_pos U h z
  have hq : 0 < q := minPeriod_pos U h (iter U t z)
  have hret_p : iter U p z = z := minPeriod_return U h z
  have hret_q : iter U q (iter U t z) = iter U t z :=
    minPeriod_return U h (iter U t z)
  have hret_p' : iter U p (iter U t z) = iter U t z := by
    rw [← iter_add, Nat.add_comm, iter_add, hret_p]
  have hret_q_z : iter U q z = z := by
    have : iter U t (iter U q z) = iter U t z := by
      have h := hret_q
      rw [← iter_add, Nat.add_comm q t, iter_add] at h
      exact h
    exact iter_lossless U h t _ _ this
  have hle_qp : q ≤ p := by
    refine Classical.byContradiction fun hnp => ?_
    exact minPeriod_least U h (iter U t z) p hp (Nat.lt_of_not_ge hnp) hret_p'
  have hle_pq : p ≤ q := by
    refine Classical.byContradiction fun hnp => ?_
    exact minPeriod_least U h z q hq (Nat.lt_of_not_ge hnp) hret_q_z
  exact Nat.le_antisymm hle_qp hle_pq

theorem iter_mul_period {n : Nat} (U : Fin n → Fin n) (h : EndoInj U)
    (z : Fin n) : ∀ q : Nat, iter U (minPeriod U h z * q) z = z
  | 0 => rfl
  | q + 1 => by
    have hret := minPeriod_return U h z
    rw [Nat.mul_succ, Nat.add_comm, iter_add, iter_mul_period U h z q, hret]

theorem iter_mod_period {n : Nat} (U : Fin n → Fin n) (h : EndoInj U)
    (z : Fin n) (i : Nat) :
    iter U i z = iter U (i % minPeriod U h z) z := by
  let p := minPeriod U h z
  have hp : 0 < p := minPeriod_pos U h z
  have hdiv : p * (i / p) + i % p = i := Nat.div_add_mod i p
  rw [← hdiv]
  have hmod : (p * (i / p) + i % p) % p = i % p := by
    rw [Nat.mul_add_mod_self_left, Nat.mod_eq_of_lt (Nat.mod_lt i hp)]
  rw [hmod, Nat.add_comm (p * (i / p)), iter_add, iter_mul_period U h z]

/-- Argmin of `f` on `{0, …, p-1}`. -/
theorem exists_argmin :
    ∀ (p : Nat) (_hp : 0 < p) (f : Nat → Nat),
      ∃ k, k < p ∧ ∀ j, j < p → f k ≤ f j
  | 0, hp, _f => absurd hp (Nat.lt_irrefl 0)
  | 1, _hp, f => by
    refine ⟨0, Nat.zero_lt_one, ?_⟩
    intro j hj
    have : j = 0 := Nat.lt_one_iff.mp hj
    subst this
    exact Nat.le_refl _
  | p' + 2, _hp, f => by
    obtain ⟨k, hk, hmin⟩ :=
      exists_argmin (p' + 1) (Nat.zero_lt_succ p') f
    cases Nat.lt_or_ge (f (p' + 1)) (f k) with
    | inl hlt =>
      refine ⟨p' + 1, Nat.lt_succ_self _, ?_⟩
      intro j hj
      cases Nat.lt_succ_iff_lt_or_eq.mp hj with
      | inl hj' => exact Nat.le_trans (Nat.le_of_lt hlt) (hmin j hj')
      | inr hj' => subst hj'; exact Nat.le_refl _
    | inr hge =>
      refine ⟨k, Nat.lt_succ_of_lt hk, ?_⟩
      intro j hj
      cases Nat.lt_succ_iff_lt_or_eq.mp hj with
      | inl hj' => exact hmin j hj'
      | inr hj' => subst hj'; exact hge

/-- Least-`val` point on the cycle of `z`. -/
theorem exists_orbit_base {n : Nat} (U : Fin n → Fin n) (h : EndoInj U)
    (z : Fin n) :
    ∃ (b : Fin n),
      (∃ t, t < minPeriod U h z ∧ iter U t z = b) ∧
      ∀ j, j < minPeriod U h z → b.val ≤ (iter U j z).val := by
  let p := minPeriod U h z
  have hp : 0 < p := minPeriod_pos U h z
  obtain ⟨t, ht, hmin⟩ := exists_argmin p hp (fun k => (iter U k z).val)
  exact ⟨iter U t z, ⟨t, ht, rfl⟩, hmin⟩

/-- Canonical basepoint of the cycle through `z`. -/
noncomputable def orbitBase {n : Nat} (U : Fin n → Fin n) (h : EndoInj U)
    (z : Fin n) : Fin n :=
  Classical.choose (exists_orbit_base U h z)

theorem orbitBase_mem {n : Nat} (U : Fin n → Fin n) (h : EndoInj U)
    (z : Fin n) :
    ∃ t, t < minPeriod U h z ∧ iter U t z = orbitBase U h z :=
  (Classical.choose_spec (exists_orbit_base U h z)).1

theorem orbitBase_min {n : Nat} (U : Fin n → Fin n) (h : EndoInj U)
    (z : Fin n) :
    ∀ j, j < minPeriod U h z →
      (orbitBase U h z).val ≤ (iter U j z).val :=
  (Classical.choose_spec (exists_orbit_base U h z)).2

/-- Arithmetic identity for wrapping around a cycle. -/
theorem cycle_add_id (p r s : Nat) (hsr : s ≤ r) (hrp : r ≤ p) :
    p - (r - s) + r = p + s := by
  have hle : r - s ≤ p := Nat.le_trans (Nat.sub_le r s) hrp
  have h1 : p - (r - s) + (r - s) = p := Nat.sub_add_cancel hle
  suffices h : p - (r - s) + ((r - s) + s) = p + s by
    simpa [Nat.sub_add_cancel hsr] using h
  rw [← Nat.add_assoc, h1]

/-- Reach any cycle point from any other by a forward step of length `< p`. -/
theorem cycle_reach {n : Nat} (U : Fin n → Fin n) (h : EndoInj U)
    (z : Fin n) (t s : Nat) (hs : s < minPeriod U h z) :
    ∃ k, k < minPeriod U h z ∧
      iter U k (iter U t z) = iter U s z := by
  let p := minPeriod U h z
  have hp : 0 < p := minPeriod_pos U h z
  have ht_eq : iter U t z = iter U (t % p) z := iter_mod_period U h z t
  rw [ht_eq]
  let r := t % p
  have hr : r < p := Nat.mod_lt t hp
  cases Nat.le_total r s with
  | inl hrs =>
    refine ⟨s - r, Nat.lt_of_le_of_lt (Nat.sub_le s r) hs, ?_⟩
    rw [← iter_add, Nat.sub_add_cancel hrs]
  | inr hsr =>
    if heq : r = s then
      refine ⟨0, hp, ?_⟩
      change iter U r z = iter U s z
      rw [heq]
    else
      have hrs_lt : s < r := Nat.lt_of_le_of_ne hsr (Ne.symm heq)
      have hdiff : 0 < r - s := Nat.sub_pos_of_lt hrs_lt
      let k := p - (r - s)
      have hklt : k < p := Nat.sub_lt hp hdiff
      refine ⟨k, hklt, ?_⟩
      have hsum : k + r = p + s :=
        cycle_add_id p r s (Nat.le_of_lt hrs_lt) (Nat.le_of_lt hr)
      have hiter : iter U k (iter U r z) = iter U (k + r) z := by
        rw [← iter_add]
      rw [hiter, hsum, Nat.add_comm p s, iter_add]
      have hret : iter U p z = z := minPeriod_return U h z
      rw [hret]

/-- The cycle basepoint is invariant under moving along the orbit. -/
theorem orbitBase_iter {n : Nat} (U : Fin n → Fin n) (h : EndoInj U)
    (z : Fin n) (t : Nat) :
    orbitBase U h (iter U t z) = orbitBase U h z := by
  apply Fin.eq_of_val_eq
  apply Nat.le_antisymm
  · -- val(orbitBase (iter t z)) ≤ val(orbitBase z)
    obtain ⟨t0, ht0, hiter0⟩ := orbitBase_mem U h z
    obtain ⟨k, hk, hkiter⟩ := cycle_reach U h z t t0 ht0
    have hp_eq : minPeriod U h (iter U t z) = minPeriod U h z :=
      minPeriod_iter U h z t
    have hb : orbitBase U h z = iter U k (iter U t z) :=
      (hkiter.trans hiter0).symm
    have hk' : k < minPeriod U h (iter U t z) := by
      rw [hp_eq]; exact hk
    have hle := orbitBase_min U h (iter U t z) k hk'
    rw [← hb] at hle
    exact hle
  · -- val(orbitBase z) ≤ val(orbitBase (iter t z))
    obtain ⟨t1, _ht1, hiter1⟩ := orbitBase_mem U h (iter U t z)
    have h1 : orbitBase U h (iter U t z) = iter U t1 (iter U t z) :=
      Eq.symm hiter1
    have h2 : iter U t1 (iter U t z) = iter U (t1 + t) z := by
      rw [← iter_add]
    have h3 : iter U (t1 + t) z =
        iter U ((t1 + t) % minPeriod U h z) z :=
      iter_mod_period U h z (t1 + t)
    have hb' : orbitBase U h (iter U t z) =
        iter U ((t1 + t) % minPeriod U h z) z :=
      h1.trans (h2.trans h3)
    have hmod : (t1 + t) % minPeriod U h z < minPeriod U h z :=
      Nat.mod_lt (t1 + t) (minPeriod_pos U h z)
    have hle := orbitBase_min U h z ((t1 + t) % minPeriod U h z) hmod
    rw [← hb'] at hle
    exact hle

theorem orbitBase_idem {n : Nat} (U : Fin n → Fin n) (h : EndoInj U)
    (z : Fin n) : orbitBase U h (orbitBase U h z) = orbitBase U h z := by
  obtain ⟨t, _, ht⟩ := orbitBase_mem U h z
  calc
    orbitBase U h (orbitBase U h z)
        = orbitBase U h (iter U t z) := by rw [ht]
      _ = orbitBase U h z := orbitBase_iter U h z t

/-- Index of `x` on its cycle, measured from `orbitBase`. -/
theorem exists_index {n : Nat} (U : Fin n → Fin n) (h : EndoInj U)
    (x : Fin n) :
    ∃ k, k < minPeriod U h (orbitBase U h x) ∧
      iter U k (orbitBase U h x) = x := by
  obtain ⟨t, ht, hiter⟩ := orbitBase_mem U h x
  have hp_eq : minPeriod U h (orbitBase U h x) = minPeriod U h x := by
    rw [← hiter, minPeriod_iter]
  obtain ⟨k, hk, hkiter⟩ :=
    cycle_reach U h x t 0 (minPeriod_pos U h x)
  refine ⟨k, ?_, ?_⟩
  · rw [hp_eq]; exact hk
  · have : iter U k (orbitBase U h x) = iter U 0 x := by
      rw [← hiter]; exact hkiter
    simpa [iter] using this

/-- Least index of `x` from its cycle basepoint. -/
noncomputable def indexOf {n : Nat} (U : Fin n → Fin n) (h : EndoInj U)
    (x : Fin n) : Nat :=
  Classical.choose (exists_index U h x)

theorem indexOf_lt {n : Nat} (U : Fin n → Fin n) (h : EndoInj U)
    (x : Fin n) : indexOf U h x < minPeriod U h (orbitBase U h x) :=
  (Classical.choose_spec (exists_index U h x)).1

theorem indexOf_iter {n : Nat} (U : Fin n → Fin n) (h : EndoInj U)
    (x : Fin n) : iter U (indexOf U h x) (orbitBase U h x) = x :=
  (Classical.choose_spec (exists_index U h x)).2

/-- Reflect index: `k ↦ p - 1 - k` on a period-`p` cycle. -/
theorem reflect_idx (p k : Nat) (hk : k < p) : p - 1 - k < p := by
  have hp : 0 < p := Nat.zero_lt_of_lt hk
  exact Nat.lt_of_le_of_lt (Nat.sub_le (p - 1) k) (Nat.pred_lt_of_lt hp)

theorem reflect_idx_involutive (p k : Nat) (hk : k < p) :
    p - 1 - (p - 1 - k) = k := by
  have hk' : k ≤ p - 1 := Nat.le_pred_of_lt hk
  simpa [Nat.sub_sub] using Nat.sub_sub_self hk'

theorem succ_pred_idx (p k : Nat) (hk : k < p) :
    (p - 1 - k) + 1 = p - k := by
  have hp : 0 < p := Nat.zero_lt_of_lt hk
  have hk' : k ≤ p - 1 := Nat.le_pred_of_lt hk
  have h1 : p - 1 - k + 1 = p - 1 + 1 - k := (Nat.sub_add_comm hk').symm
  have h2 : p - 1 + 1 = p := Nat.sub_add_cancel (Nat.succ_le_of_lt hp)
  rw [h1, h2]

/-- Cycle-wise reflect: first bounce. -/
noncomputable def bounceφ {n : Nat} (U : Fin n → Fin n) (h : EndoInj U) :
    Fin n → Fin n :=
  fun x =>
    iter U (minPeriod U h (orbitBase U h x) - 1 - indexOf U h x)
      (orbitBase U h x)

/-- Second bounce: `U ∘ φ`. -/
noncomputable def bounceσ {n : Nat} (U : Fin n → Fin n) (h : EndoInj U) :
    Fin n → Fin n :=
  fun x => U (bounceφ U h x)

theorem orbitBase_of_bounceφ {n : Nat} (U : Fin n → Fin n) (h : EndoInj U)
    (x : Fin n) :
    orbitBase U h (bounceφ U h x) = orbitBase U h x := by
  dsimp [bounceφ]
  rw [orbitBase_iter, orbitBase_idem]

theorem indexOf_bounceφ {n : Nat} (U : Fin n → Fin n) (h : EndoInj U)
    (x : Fin n) :
    indexOf U h (bounceφ U h x) =
      minPeriod U h (orbitBase U h x) - 1 - indexOf U h x := by
  let b := orbitBase U h x
  let p := minPeriod U h b
  let k := indexOf U h x
  have hk : k < p := indexOf_lt U h x
  have hbφ : orbitBase U h (bounceφ U h x) = b := orbitBase_of_bounceφ U h x
  have hφ : bounceφ U h x = iter U (p - 1 - k) b := rfl
  have hspec := Classical.choose_spec (exists_index U h (bounceφ U h x))
  have hpφ : minPeriod U h (orbitBase U h (bounceφ U h x)) = p := by
    rw [hbφ]
  have hlt : indexOf U h (bounceφ U h x) < p :=
    Nat.lt_of_lt_of_eq hspec.1 hpφ
  have heq :
      iter U (indexOf U h (bounceφ U h x)) b = iter U (p - 1 - k) b := by
    have h1 : iter U (indexOf U h (bounceφ U h x)) b =
        iter U (indexOf U h (bounceφ U h x))
          (orbitBase U h (bounceφ U h x)) := by rw [hbφ]
    have h2 : iter U (indexOf U h (bounceφ U h x))
        (orbitBase U h (bounceφ U h x)) = bounceφ U h x := hspec.2
    exact h1.trans (h2.trans hφ)
  exact orbit_distinct U h b _ _ hlt (reflect_idx p k hk) heq

theorem bounceφ_involution {n : Nat} (U : Fin n → Fin n) (h : EndoInj U) :
    IsInvolution (bounceφ U h) := by
  intro x
  let b := orbitBase U h x
  let p := minPeriod U h b
  let k := indexOf U h x
  have hk : k < p := indexOf_lt U h x
  have hx : iter U k b = x := indexOf_iter U h x
  have hbφ : orbitBase U h (bounceφ U h x) = b := orbitBase_of_bounceφ U h x
  have hidx : indexOf U h (bounceφ U h x) = p - 1 - k :=
    indexOf_bounceφ U h x
  have hpφ : minPeriod U h (orbitBase U h (bounceφ U h x)) = p := by
    rw [hbφ]
  have hunfold :
      bounceφ U h (bounceφ U h x) =
        iter U
          (minPeriod U h (orbitBase U h (bounceφ U h x)) - 1 -
            indexOf U h (bounceφ U h x))
          (orbitBase U h (bounceφ U h x)) := rfl
  rw [hunfold, hpφ, hidx, hbφ, reflect_idx_involutive p k hk, hx]

theorem bounceσ_eq_iter {n : Nat} (U : Fin n → Fin n) (h : EndoInj U)
    (x : Fin n) :
    bounceσ U h x =
      iter U (minPeriod U h (orbitBase U h x) - indexOf U h x)
        (orbitBase U h x) := by
  let b := orbitBase U h x
  let p := minPeriod U h b
  let k := indexOf U h x
  have hk : k < p := indexOf_lt U h x
  dsimp [bounceσ, bounceφ]
  have : iter U ((p - 1 - k) + 1) b = U (iter U (p - 1 - k) b) := rfl
  rw [← this, succ_pred_idx p k hk]

theorem bounceσ_involution {n : Nat} (U : Fin n → Fin n) (h : EndoInj U) :
    IsInvolution (bounceσ U h) := by
  intro x
  let b := orbitBase U h x
  let p := minPeriod U h b
  let k := indexOf U h x
  have hk : k < p := indexOf_lt U h x
  have hx : iter U k b = x := indexOf_iter U h x
  have hp : 0 < p := minPeriod_pos U h b
  have hσx : bounceσ U h x = iter U (p - k) b := bounceσ_eq_iter U h x
  cases Nat.eq_zero_or_pos k with
  | inl hk0 =>
    -- k = 0: x = b and σ x = iter p b = b = x
    have hx0 : x = b := by
      have := hx
      rw [hk0] at this
      simpa [iter] using this.symm
    have hσ : bounceσ U h x = x := by
      rw [hσx, hk0, Nat.sub_zero, minPeriod_return U h b, hx0]
    rw [hσ, hσ]
  | inr hk0 =>
    have hpk : p - k < p := Nat.sub_lt hp hk0
    have hbσ : orbitBase U h (bounceσ U h x) = b := by
      rw [hσx, orbitBase_iter, orbitBase_idem]
    have hidxσ : indexOf U h (bounceσ U h x) = p - k := by
      have hspec := Classical.choose_spec (exists_index U h (bounceσ U h x))
      have hpσ : minPeriod U h (orbitBase U h (bounceσ U h x)) = p := by
        rw [hbσ]
      have hlt : indexOf U h (bounceσ U h x) < p :=
        Nat.lt_of_lt_of_eq hspec.1 hpσ
      have heq :
          iter U (indexOf U h (bounceσ U h x)) b = iter U (p - k) b := by
        have h1 : iter U (indexOf U h (bounceσ U h x)) b =
            iter U (indexOf U h (bounceσ U h x))
              (orbitBase U h (bounceσ U h x)) := by rw [hbσ]
        have h2 : iter U (indexOf U h (bounceσ U h x))
            (orbitBase U h (bounceσ U h x)) = bounceσ U h x := hspec.2
        exact h1.trans (h2.trans hσx)
      exact orbit_distinct U h b _ _ hlt hpk heq
    have hφσ :
        bounceφ U h (bounceσ U h x) = iter U (p - 1 - (p - k)) b := by
      have hunfold :
          bounceφ U h (bounceσ U h x) =
            iter U
              (minPeriod U h (orbitBase U h (bounceσ U h x)) - 1 -
                indexOf U h (bounceσ U h x))
              (orbitBase U h (bounceσ U h x)) := rfl
      have hpσ : minPeriod U h (orbitBase U h (bounceσ U h x)) = p := by
        rw [hbσ]
      rw [hunfold, hpσ, hidxσ, hbσ]
    have hrefl : p - 1 - (p - k) = k - 1 := by
      have hkle : k ≤ p := Nat.le_of_lt hk
      have h1 : p - (p - k) = k := Nat.sub_sub_self hkle
      have hle : p - k ≤ p - 1 :=
        Nat.sub_le_sub_left (Nat.succ_le_of_lt hk0) p
      have hsucc' : p - 1 - (p - k) + 1 = k := by
        have hcomm : p - 1 - (p - k) + 1 = p - 1 + 1 - (p - k) :=
          (Nat.sub_add_comm hle).symm
        have h2 : p - 1 + 1 = p := Nat.sub_add_cancel (Nat.succ_le_of_lt hp)
        rw [hcomm, h2, h1]
      exact Nat.succ.inj
        (hsucc'.trans (Nat.succ_pred_eq_of_pos hk0).symm)
    show bounceσ U h (bounceσ U h x) = x
    have hσσ : bounceσ U h (bounceσ U h x) =
        U (bounceφ U h (bounceσ U h x)) := rfl
    rw [hσσ, hφσ, hrefl]
    have hstep : iter U ((k - 1) + 1) b = U (iter U (k - 1) b) := rfl
    have hks : (k - 1) + 1 = k := Nat.sub_add_cancel (Nat.succ_le_of_lt hk0)
    rw [← hstep, hks, hx]

/-- Every injective endomap on `Fin n` factors as two involutions. -/
noncomputable def factor_fin {n : Nat} (U : Fin n → Fin n) (h : EndoInj U) :
    TwoBounceFactor U where
  φ := bounceφ U h
  σ := bounceσ U h
  φ_inv := bounceφ_involution U h
  σ_inv := bounceσ_involution U h
  factor := by
    intro x
    -- U x = σ (φ x) = U (φ (φ x)) = U x
    dsimp [bounceσ]
    rw [bounceφ_involution U h x]

/-! ## Canonicity fails (essential non-uniqueness)

Two factorisations of the same `U` need not share `φ` (or `σ`). The
involutive Bool case already kills uniqueness; its binary reordering is
T-7-shaped (ordered bounce pair), not a new dictionary face. On `Fin 3`
distinct reflection axes give factorisations unrelated by mere swap,
so the I-1 discharge gauge properly exceeds ℤ/2 while T-7 stays one ℤ/2. -/

theorem not_involution : IsInvolution (not : Bool → Bool) := by
  intro b; cases b <;> rfl

theorem not_endoInj : EndoInj (not : Bool → Bool) := by
  intro a b h
  cases a <;> cases b <;> first | rfl | cases h

/-- Pointwise inequality of first factors. -/
def FactorsDisagree {α : Type} {U : α → α}
    (f g : TwoBounceFactor U) : Prop :=
  (∃ x, f.φ x ≠ g.φ x) ∨ (∃ x, f.σ x ≠ g.σ x)

/-- Involutive reordering: `(id, U)` and `(U, id)` both factor `U`. -/
theorem involutive_factor_reorder {α : Type} (U : α → α)
    (h : IsInvolution U) :
    FactorsDisagree (factor_involution U h) (factor_involution_rev U h) ↔
      ∃ x, U x ≠ x := by
  constructor
  · intro hd
    cases hd with
    | inl hφ =>
      obtain ⟨x, hx⟩ := hφ
      exact ⟨x, fun heq => hx (Eq.symm heq)⟩
    | inr hσ =>
      obtain ⟨x, hx⟩ := hσ
      exact ⟨x, fun heq => hx heq⟩
  · intro ⟨x, hx⟩
    exact Or.inl ⟨x, fun heq => hx (Eq.symm heq)⟩

/-- **Canonicity fails.** `not` admits two disagreeing two-bounce
    factorisations (`not∘id` and `id∘not`). -/
theorem canonicity_fails :
    ∃ (U : Bool → Bool) (f g : TwoBounceFactor U),
      EndoInj U ∧ FactorsDisagree f g :=
  ⟨not,
   factor_involution not not_involution,
   factor_involution_rev not not_involution,
   not_endoInj,
   Or.inl ⟨false, by decide⟩⟩

/-- Bounce-swap of an ordered factor pair: `(φ,σ) ↦ (σ,φ)`. -/
def IsBounceSwap {α : Type} {U : α → α}
    (f g : TwoBounceFactor U) : Prop :=
  (∀ x, f.φ x = g.σ x) ∧ (∀ x, f.σ x = g.φ x)

/-! ### Fin 3: axis choice exceeds bounce-swap -/

/-- The 3-cycle `(0 1 2)`. -/
def cycle3 : Fin 3 → Fin 3
  | ⟨0, _⟩ => ⟨1, by decide⟩
  | ⟨1, _⟩ => ⟨2, by decide⟩
  | ⟨2, _⟩ => ⟨0, by decide⟩

theorem cycle3_inj : EndoInj cycle3 := by
  intro a b h
  match a, b with
  | ⟨0, _⟩, ⟨0, _⟩ => rfl
  | ⟨0, _⟩, ⟨1, _⟩ => cases h
  | ⟨0, _⟩, ⟨2, _⟩ => cases h
  | ⟨1, _⟩, ⟨0, _⟩ => cases h
  | ⟨1, _⟩, ⟨1, _⟩ => rfl
  | ⟨1, _⟩, ⟨2, _⟩ => cases h
  | ⟨2, _⟩, ⟨0, _⟩ => cases h
  | ⟨2, _⟩, ⟨1, _⟩ => cases h
  | ⟨2, _⟩, ⟨2, _⟩ => rfl

/-- Reflect through `0` (fix 0, swap 1↔2). -/
def reflect0 : Fin 3 → Fin 3
  | ⟨0, _⟩ => ⟨0, by decide⟩
  | ⟨1, _⟩ => ⟨2, by decide⟩
  | ⟨2, _⟩ => ⟨1, by decide⟩

/-- Reflect through `1` (fix 1, swap 0↔2). -/
def reflect1 : Fin 3 → Fin 3
  | ⟨0, _⟩ => ⟨2, by decide⟩
  | ⟨1, _⟩ => ⟨1, by decide⟩
  | ⟨2, _⟩ => ⟨0, by decide⟩

theorem reflect0_involution : IsInvolution reflect0 := by
  intro x; exact (by decide : ∀ y : Fin 3, reflect0 (reflect0 y) = y) x

theorem reflect1_involution : IsInvolution reflect1 := by
  intro x; exact (by decide : ∀ y : Fin 3, reflect1 (reflect1 y) = y) x

theorem cycle3_reflect0_involution :
    IsInvolution (fun x => cycle3 (reflect0 x)) := by
  intro x
  exact (by decide : ∀ y : Fin 3,
    cycle3 (reflect0 (cycle3 (reflect0 y))) = y) x

theorem cycle3_reflect1_involution :
    IsInvolution (fun x => cycle3 (reflect1 x)) := by
  intro x
  exact (by decide : ∀ y : Fin 3,
    cycle3 (reflect1 (cycle3 (reflect1 y))) = y) x

def factor_cycle3_axis0 : TwoBounceFactor cycle3 where
  φ := reflect0
  σ := fun x => cycle3 (reflect0 x)
  φ_inv := reflect0_involution
  σ_inv := cycle3_reflect0_involution
  factor := fun x => by rw [reflect0_involution x]

def factor_cycle3_axis1 : TwoBounceFactor cycle3 where
  φ := reflect1
  σ := fun x => cycle3 (reflect1 x)
  φ_inv := reflect1_involution
  σ_inv := cycle3_reflect1_involution
  factor := fun x => by rw [reflect1_involution x]

/-- Axis choice: two Fin-3 factorisations disagree, and one is not the
    bounce-swap of the other. (I-1 discharge gauge > ℤ/2 reorder.) -/
theorem factorization_gauge_exceeds_swap :
    FactorsDisagree factor_cycle3_axis0 factor_cycle3_axis1 ∧
    ¬ IsBounceSwap factor_cycle3_axis0 factor_cycle3_axis1 := by
  constructor
  · refine Or.inl ⟨⟨0, by decide⟩, ?_⟩
    decide
  · intro h
    have hx := h.2 ⟨0, by decide⟩
    -- σ₀ 0 = 1, φ₁ 0 = 2
    revert hx
    decide

/-- **I-1 canonicity package.** Uniqueness fails; involutive reorder is
    available whenever `U` moves a point; Fin-3 axis choice exceeds
    bounce-swap. -/
theorem i1_canonicity_package :
    (∃ (U : Bool → Bool) (f g : TwoBounceFactor U),
      EndoInj U ∧ FactorsDisagree f g) ∧
    (∀ {α : Type} (U : α → α) (h : IsInvolution U),
      (∃ x, U x ≠ x) →
        FactorsDisagree (factor_involution U h) (factor_involution_rev U h)) ∧
    (FactorsDisagree factor_cycle3_axis0 factor_cycle3_axis1 ∧
      ¬ IsBounceSwap factor_cycle3_axis0 factor_cycle3_axis1) :=
  ⟨canonicity_fails,
   fun U h hx => (involutive_factor_reorder U h).mpr hx,
   factorization_gauge_exceeds_swap⟩

/-- **I-1 two-bounce fragment.** Converse + spine ¬erase + existence on
    involutions / Bool / swapStep / every injection on `Fin n` +
    canonicity failure. -/
theorem i1_two_bounce_fragment :
    (∀ {α : Type} (U : α → α) (_f : TwoBounceFactor U), Lossless U) ∧
    (∀ {S E : Type} (U : S × E → S × E) (_f : TwoBounceFactor U),
      Geom.Registration.Inj U) ∧
    (∀ {α : Type} (U : α → α), IsInvolution U →
      Nonempty (TwoBounceFactor U)) ∧
    (∀ U : Bool → Bool, EndoInj U → Nonempty (TwoBounceFactor U)) ∧
    Nonempty (TwoBounceFactor Geom.Registration.swapStep) ∧
    (∀ {α : Type} (act : α → α), SymmetricStep act → ¬ Erasing act) ∧
    (∀ {n : Nat} (U : Fin n → Fin n), EndoInj U →
      Nonempty (TwoBounceFactor U)) ∧
    (∃ (U : Bool → Bool) (f g : TwoBounceFactor U),
      EndoInj U ∧ FactorsDisagree f g) :=
  ⟨fun _U => lossless_of_two_bounce _,
   fun _U => inj_of_two_bounce _,
   fun _U h => ⟨factor_involution _ h⟩,
   fun U h => ⟨factor_bool U h⟩,
   ⟨factor_swapStep⟩,
   fun act hs => symmetric_excludes_erase act hs,
   fun U h => ⟨factor_fin U h⟩,
   canonicity_fails⟩

#print axioms Bridge.TwoBounce.symmetric_excludes_erase
#print axioms Bridge.TwoBounce.lossless_of_two_bounce
#print axioms Bridge.TwoBounce.inj_of_two_bounce
#print axioms Bridge.TwoBounce.factor_bool
#print axioms Bridge.TwoBounce.factor_fin
#print axioms Bridge.TwoBounce.canonicity_fails
#print axioms Bridge.TwoBounce.i1_canonicity_package
#print axioms Bridge.TwoBounce.i1_two_bounce_fragment

end Bridge.TwoBounce
