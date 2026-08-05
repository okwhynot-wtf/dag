import WaveDynamics
import WaveEquation

/-!
# CouplingGauge (EXPERIMENTAL: quarantined; exports nothing to the paper)

Resolution of the coupling-flip gauge question. The dynamics
classification (`Bridge.DynamicsAmbient.coupling_uniqueness`) leaves
two couplings, `xor` and its pointwise flip `!xor`, a single orbit of
the flip involution on coupling space. Pole conjugation fixes each
survivor, because complement invariance is a hypothesis of the
classification, so the coupling flip is a distinct involution and its
gauge class was unassigned. This module settles the class by proof.

**Kernel exploration record.** The full cycle structures of
`step ringX` and `step (flipX ringX)` on `WState n`, computed for
`n = 2` through `8` and written as `length: count` multisets:

| n | `xor` | `!xor` | equal |
|---|---|---|---|
| 2 | 1:4, 2:6 | 4:4 | no |
| 3 | 1:2, 2:1, 3:10, 6:5 | 4:1, 12:5 | no |
| 4 | 1:4, 2:6, 4:60 | 1:4, 2:6, 4:60 | yes |
| 5 | 1:2, 2:1, 5:102, 10:51 | 4:1, 20:51 | no |
| 6 | 1:4, 2:6, 3:20, 6:670 | 4:4, 12:340 | no |
| 7 | 1:2, 2:1, 7:1170, 14:585 | 4:1, 28:585 | no |
| 8 | 1:4, 2:6, 4:60, 8:8160 | 1:4, 2:6, 4:60, 8:8160 | yes |

The spectra agree exactly at the sizes divisible by four. The module
proves that pattern as a theorem at every size, in both directions.

**Results.**

* **Per-tick flip form** (`flip_step_pointwise`): for every coupling
  `X`, the flipped step equals the plain step followed by a pole flip
  of the freshly written layer. This is the mechanism named by the R1
  candidate of the gauge question; by itself it is a cocycle
  presentation, and it supplies no conjugacy.
* **Mask conjugacy mechanism** (`mask_intertwines_pointwise`): call a
  field `a` an alternating mask when `ringX a i = true` at every
  site, so that the mask poles alternate along each parity chain of
  the ring. For every alternating mask, the layerwise masking
  `maskS a` is an involution intertwining `step ringX` with
  `step (flipX ringX)`, pointwise on both layers.
* **Alternating masks exist exactly on carriers divisible by four**
  (`mask4_alternating`, `alternating_forces_four_dvd`,
  `alternating_mask_iff_four_dvd`): the block mask
  `i ↦ decide (2 ≤ i % 4)` alternates whenever `4 ∣ n`; conversely an
  alternating mask forces `4 ∣ n`, by lifting the mask to a
  `Nat`-indexed stream with `d (j + 2) = !(d j)` and period `n` and
  driving the sign around the ring.
* **The spectra separate at every other size** (`ring_fixes_zero`,
  `flip_no_fixed_pointwise`, `flip_no_fixed_point`,
  `fixed_point_spectra_differ`): the ring step fixes the zero state
  definitionally; when `n % 4 ≠ 0` the flipped step fixes no state at
  all, because the current layer of a fixed state would be an
  alternating mask. The two cycle structures already differ at cycle
  length one.
* **R2, the decisive negative** (`flip_no_intertwiner_pointwise`,
  `flip_no_intertwiner`, `flip_not_conjugate`): when `n % 4 ≠ 0`, no
  map of state spaces intertwines the two dynamics, even pointwise
  and even without injectivity; in particular no state-space
  bijection conjugates them, shift-commuting or otherwise. The proof
  transports the definitional fixed point through any candidate
  intertwiner.
* **R1 on the divisible carriers** (`flip_conjugacy_of_four_dvd`,
  kernel instance `flip_conjugate_four`): when `4 ∣ n` the coupling
  flip is realised by the explicit half-period pole mask, an
  involution on states conjugating the two dynamics exactly. On
  those carriers the flip is packaging.
* **Dichotomy package** (`coupling_flip_dichotomy`): both directions
  in one statement over every carrier size.
* **Tick-periodic dressing at every size**
  (`flip_step_dress_pointwise`, `flip_iter_dress_pointwise`): at
  every size the flipped evolution equals the plain evolution
  dressed, at time `T`, by a constant pole mask pair drawn from the
  period-four schedule identity, flip the current layer, flip both
  layers, flip the previous layer. The flip therefore always admits a
  record-gauge-style per-tick repackaging; the negative theorem shows
  that outside the divisible sizes the schedule cannot be traded for
  a single time-independent map. The dressing also explains the
  observed spectra: every orbit length of the flipped dynamics
  divides the least common multiple of four and the corresponding
  plain orbit length.
* **Kernel exhibits** (`flip_ring2_pulse_period_four`,
  `flip_ring3_pulse_period_twelve`, `flip_ring4_pulse_period_four`,
  `flip_ring5_pulse_period_twenty`, `mask4_alternating_four`): the
  single-pulse state periods under the flipped coupling at sizes 2,
  3, 4, 5 are 4, 12, 4, 20, against 2, 6, 4, 10 for the plain
  coupling (`Experimental.Wave.ring2_period_two`,
  `Experimental.Wave.ring3_period_six`,
  `Bridge.WaveDynamics.ring4_period_four`,
  `Experimental.Wave.ring5_period_ten`). Sizes 2, 3, and 4 are
  decided directly by the kernel. At size 5 a direct twenty-step
  decision exceeds feasible kernel reduction, so the exhibit is
  assembled from the dressing theorem, the plain period ten, and
  kernel decisions confined to the first ten plain states. The
  doubling at sizes 2, 3, 5 and the agreement at size 4 instantiate
  the dichotomy on the exhibit carriers.

**Gauge placement, stated as mathematics.** Three facts are now
theorems. The coupling flip admits an equivariant identification with
a state-space packaging exactly on carriers divisible by four, where
it is conjugation by the half-period pole mask. On every other
carrier the two surviving dynamics are observably distinct and no
identification exists, so there the flip carries content and the two
couplings can be exported only inside "up to coupling flip" clauses,
mirroring the label-swap treatment. At every size the flip is a
per-tick dressing by constant pole masks with period four. The
framing decision for the paper's gauge table rests with the author;
the candidate row reads: coupling flip, content in general,
collapsing to packaging on carriers divisible by four, citing
`coupling_flip_dichotomy`.

**Footprints.** The Bool lemmas, the per-tick flip form
(`flip_step_pointwise`), the mask involution
(`maskS_involution_pointwise`), and the iterate splitting lemma are
axiom-free. Every declaration whose statement touches the ring
coupling inherits propext through the `Fin` index arithmetic of
`ringX` (the `Nat.mod` machinery behind the neighbour offsets); on
that base, `ringX_mask_pointwise`, `mask_intertwines_pointwise`,
`ring_fixes_zero`, the congruence lemma, the one-step dressing
lemma, and the kernel-decided `mask4_alternating_four` carry propext
alone, and the declarations that additionally pass through `omega`,
the schedule recursion, or a kernel-decided `Decidable` instance
carry `Quot.sound` beside it: the mask existence results, the
fixed-point and intertwiner negatives at pointwise and packaged
level, the dichotomy, and the iterated dressing.
`flip_conjugacy_of_four_dvd`
invokes function extensionality directly (`funext` with `Prod.ext`)
to package the pointwise conjugacy, and `coupling_flip_dichotomy`
with `flip_conjugate_four` inherit that footprint; this use is
flagged here and in `AXIOMS.md`. The four pulse exhibits carry
propext and `Quot.sound`, the first three through their `Decidable`
instances and the five-site exhibit through the plain period-ten
theorem and the reduced kernel decisions it is assembled from.
`Classical.choice` appears nowhere in this module.
-/
namespace Experimental.CouplingGauge

open Bridge.WaveDynamics
open Experimental.Wave (pulseN iterN_succ_out ring5_period_ten
  iterN_step_ringX_congr)

/-! ## Bool lemmas -/

/-- Flipping one xor argument flips the xor. -/
theorem xor_not_right (a b : Bool) : (a ^^ !b) = !(a ^^ b) := by
  cases a <;> cases b <;> rfl

/-- The right arguments of a double xor commute. -/
theorem xor_right_comm (a b c : Bool) :
    ((a ^^ b) ^^ c) = ((a ^^ c) ^^ b) := by
  cases a <;> cases b <;> cases c <;> rfl

/-- Regrouping a xor of xors into paired columns. -/
theorem xor_pair_exchange (p u q v : Bool) :
    ((p ^^ u) ^^ (q ^^ v)) = ((p ^^ q) ^^ (u ^^ v)) := by
  cases p <;> cases u <;> cases q <;> cases v <;> rfl

/-- Exchanging a plain and a negated xor argument across the pair. -/
theorem xor_not_exchange (x u r : Bool) :
    ((x ^^ u) ^^ !r) = ((x ^^ r) ^^ !u) := by
  cases x <;> cases u <;> cases r <;> rfl

/-- A xor that returns its left argument has a silent right argument. -/
theorem cancel_of_xor_eq (x y : Bool) (h : (x ^^ y) = x) : y = false := by
  cases x <;> cases y <;> first | rfl | exact Bool.noConfusion h

/-- A pole whose flip is `false` is `true`. -/
theorem true_of_not_false (b : Bool) (h : (!b) = false) : b = true := by
  cases b <;> first | rfl | exact Bool.noConfusion h

/-- A live xor determines each argument as the flip of the other. -/
theorem flip_of_xor_true (x y : Bool) (h : (x ^^ y) = true) : y = !x := by
  cases x <;> cases y <;> first | rfl | exact Bool.noConfusion h

/-! ## The coupling flip and the per-tick flip form -/

/-- The coupling flip at field level: pointwise complement of the
    coupling values. Instantiated at `ringX` this is the second
    survivor of the coupling classification. -/
def flipX {n : Nat} (X : Field n → Fin n → Bool) :
    Field n → Fin n → Bool :=
  fun c i => !(X c i)

/-- Pole flip of the freshly written (current) layer only. -/
def flipNew {n : Nat} (s : WState n) : WState n :=
  (s.1, fun i => !(s.2 i))

/-- **Per-tick flip form.** For every coupling, the flipped step is
    the plain step followed by a pole flip of the freshly written
    layer, pointwise on both layers. This is a cocycle presentation
    of the flipped dynamics; it is available at every carrier size
    and by itself supplies no conjugacy. -/
theorem flip_step_pointwise {n : Nat} (X : Field n → Fin n → Bool)
    (s : WState n) :
    (∀ i, (step (flipX X) s).1 i = (flipNew (step X s)).1 i) ∧
    (∀ i, (step (flipX X) s).2 i = (flipNew (step X s)).2 i) :=
  ⟨fun _ => rfl, fun i => xor_not_right (s.1 i) (X s.2 i)⟩

/-! ## Masks and the conjugacy mechanism -/

/-- Layer masking: flip the pole at every site where the mask is
    live. -/
def maskF {n : Nat} (a c : Field n) : Field n :=
  fun i => c i ^^ a i

/-- State masking: the same mask on both layers. -/
def maskS {n : Nat} (a : Field n) (s : WState n) : WState n :=
  (maskF a s.1, maskF a s.2)

/-- Masking is an involution, pointwise on both layers. -/
theorem maskS_involution_pointwise {n : Nat} (a : Field n)
    (s : WState n) :
    (∀ i, (maskS a (maskS a s)).1 i = s.1 i) ∧
    (∀ i, (maskS a (maskS a s)).2 i = s.2 i) :=
  ⟨fun i => xor_cancel (s.1 i) (a i), fun i => xor_cancel (s.2 i) (a i)⟩

/-- The ring coupling is additive under masking, pointwise: the
    coupling of a masked layer is the coupling xor the coupling of
    the mask. -/
theorem ringX_mask_pointwise {m : Nat} (a c : Field (m + 1))
    (i : Fin (m + 1)) :
    ringX (maskF a c) i = (ringX c i ^^ ringX a i) :=
  xor_pair_exchange (c (i - 1)) (a (i - 1)) (c (i + 1)) (a (i + 1))

/-- An alternating mask: the mask's own ring coupling is live at
    every site, so the mask poles alternate along each parity chain
    of the ring. -/
def Alternating {m : Nat} (a : Field (m + 1)) : Prop :=
  ∀ i, ringX a i = true

/-- **Mask conjugacy mechanism.** Masking both layers by an
    alternating mask intertwines the plain and flipped ring steps,
    pointwise on both layers. -/
theorem mask_intertwines_pointwise {m : Nat} (a : Field (m + 1))
    (ha : Alternating a) (s : WState (m + 1)) :
    (∀ i, (maskS a (step ringX s)).1 i
        = (step (flipX ringX) (maskS a s)).1 i) ∧
    (∀ i, (maskS a (step ringX s)).2 i
        = (step (flipX ringX) (maskS a s)).2 i) := by
  refine ⟨fun _ => rfl, fun i => ?_⟩
  show ((s.1 i ^^ ringX s.2 i) ^^ a i)
      = ((s.1 i ^^ a i) ^^ !(ringX (maskF a s.2) i))
  rw [ringX_mask_pointwise, ha i, Bool.xor_true, Bool.not_not]
  exact xor_right_comm (s.1 i) (ringX s.2 i) (a i)

/-! ## Existence of alternating masks on carriers divisible by four -/

/-- The block mask: two silent sites, two live sites, repeating. -/
def mask4 {n : Nat} : Field n :=
  fun i => decide (2 ≤ i.val % 4)

/-- Reduction of a variable modulus to modulus four when four divides
    the modulus. -/
private theorem mod_mod_four {n : Nat} (h4 : n % 4 = 0) (x : Nat) :
    x % n % 4 = x % 4 := by
  have hd : n = 4 * (n / 4) := by omega
  calc x % n % 4
      = (x % n + 4 * (n / 4 * (x / n))) % 4 :=
        (Nat.add_mul_mod_self_left _ _ _).symm
    _ = (x % n + n * (x / n)) % 4 := by rw [← Nat.mul_assoc, ← hd]
    _ = x % 4 := by rw [Nat.mod_add_div]

/-- On a carrier divisible by four, the block mask alternates. -/
theorem mask4_alternating {m : Nat} (h4 : (m + 1) % 4 = 0) :
    Alternating (mask4 (n := m + 1)) := by
  intro i
  have h1 : 1 % (m + 1) = 1 := Nat.mod_eq_of_lt (by omega)
  show (mask4 (i - 1) ^^ mask4 (i + 1)) = true
  rw [Fin.sub_def, Fin.add_def]
  show (decide (2 ≤ (m + 1 - 1 % (m + 1) + i.val) % (m + 1) % 4) ^^
      decide (2 ≤ (i.val + 1 % (m + 1)) % (m + 1) % 4)) = true
  rw [h1, mod_mod_four h4, mod_mod_four h4]
  have hc : i.val % 4 = 0 ∨ i.val % 4 = 1 ∨ i.val % 4 = 2 ∨
      i.val % 4 = 3 := by omega
  obtain h | h | h | h := hc
  · rw [show (m + 1 - 1 + i.val) % 4 = 3 by omega,
      show (i.val + 1) % 4 = 1 by omega]
    rfl
  · rw [show (m + 1 - 1 + i.val) % 4 = 0 by omega,
      show (i.val + 1) % 4 = 2 by omega]
    rfl
  · rw [show (m + 1 - 1 + i.val) % 4 = 1 by omega,
      show (i.val + 1) % 4 = 3 by omega]
    rfl
  · rw [show (m + 1 - 1 + i.val) % 4 = 2 by omega,
      show (i.val + 1) % 4 = 0 by omega]
    rfl

/-! ## Alternating masks force divisibility by four

The mask lifts to a `Nat`-indexed stream that flips every two steps
and repeats every `n` steps; driving the flip around the ring forces
the carrier size into `4Z`. The degenerate one-site ring is handled
separately, since there the two neighbours coincide and the coupling
of any mask is silent. -/

/-- The mask read as a `Nat`-indexed stream through the quotient map. -/
private def streamOf {m : Nat} (a : Field (m + 1)) : Nat → Bool :=
  fun j => a ⟨j % (m + 1), Nat.mod_lt j (Nat.succ_pos m)⟩

/-- An alternating mask's stream flips every two steps (carriers of
    at least two sites). -/
private theorem stream_step {m : Nat} (hm : 1 ≤ m) (a : Field (m + 1))
    (ha : Alternating a) (j : Nat) :
    streamOf a (j + 2) = !(streamOf a j) := by
  have npos : 0 < m + 1 := Nat.succ_pos m
  have h1 : 1 % (m + 1) = 1 := Nat.mod_eq_of_lt (by omega)
  have hlt : (j + 1) % (m + 1) < m + 1 := Nat.mod_lt _ npos
  have h := ha ⟨(j + 1) % (m + 1), hlt⟩
  have h' : (a (⟨(j + 1) % (m + 1), hlt⟩ - 1) ^^
      a (⟨(j + 1) % (m + 1), hlt⟩ + 1)) = true := h
  have hA : (⟨(j + 1) % (m + 1), hlt⟩ - 1 : Fin (m + 1))
      = ⟨j % (m + 1), Nat.mod_lt j npos⟩ := by
    apply Fin.ext
    show (m + 1 - 1 % (m + 1) + (j + 1) % (m + 1)) % (m + 1)
        = j % (m + 1)
    rw [h1]
    have e1 : ((j + 1) % (m + 1)) % (m + 1) = (j + 1) % (m + 1) :=
      Nat.mod_eq_of_lt hlt
    calc (m + 1 - 1 + (j + 1) % (m + 1)) % (m + 1)
        = ((m + 1 - 1) % (m + 1) + ((j + 1) % (m + 1)) % (m + 1))
            % (m + 1) := Nat.add_mod _ _ _
      _ = ((m + 1 - 1) % (m + 1) + (j + 1) % (m + 1)) % (m + 1) := by
          rw [e1]
      _ = (m + 1 - 1 + (j + 1)) % (m + 1) := (Nat.add_mod _ _ _).symm
      _ = (m + 1 + j) % (m + 1) := by
          have e2 : m + 1 - 1 + (j + 1) = m + 1 + j := by omega
          rw [e2]
      _ = j % (m + 1) := Nat.add_mod_left _ _
  have hB : (⟨(j + 1) % (m + 1), hlt⟩ + 1 : Fin (m + 1))
      = ⟨(j + 2) % (m + 1), Nat.mod_lt (j + 2) npos⟩ := by
    apply Fin.ext
    show ((j + 1) % (m + 1) + 1 % (m + 1)) % (m + 1)
        = (j + 2) % (m + 1)
    exact (Nat.add_mod (j + 1) 1 (m + 1)).symm
  rw [hA, hB] at h'
  exact flip_of_xor_true _ _ h'

/-- The stream repeats with the carrier period. -/
private theorem stream_period {m : Nat} (a : Field (m + 1)) (j : Nat) :
    streamOf a (j + (m + 1)) = streamOf a j :=
  congrArg a (Fin.ext (Nat.add_mod_right j (m + 1)))

/-- Iterating the two-step flip: after `2k` steps the stream carries
    the parity of `k` as a sign. -/
private theorem d_period_flip (d : Nat → Bool)
    (hstep : ∀ j, d (j + 2) = !(d j)) :
    ∀ k j, d (j + 2 * k) = (decide (k % 2 = 1) ^^ d j) := by
  intro k
  induction k with
  | zero => intro j; exact (Bool.false_xor (d j)).symm
  | succ k ih =>
    intro j
    have harith : j + 2 * (k + 1) = (j + 2 * k) + 2 := by omega
    rw [harith, hstep (j + 2 * k), ih j]
    have hpar : k % 2 = 0 ∨ k % 2 = 1 := by omega
    obtain h | h := hpar
    · have h1 : (k + 1) % 2 = 1 := by omega
      rw [h, h1]
      cases d j <;> rfl
    · have h1 : (k + 1) % 2 = 0 := by omega
      rw [h, h1]
      cases d j <;> rfl

/-- Parity split for a bare `Nat`, kept division-free so the `omega`
    proof stays clear of `Classical.choice`. -/
private theorem mod_two_cases (k : Nat) : k % 2 = 0 ∨ k % 2 = 1 := by
  omega

/-- A stream that flips every two steps and repeats with period `n`
    forces `n` into `4Z`. -/
private theorem stream_contradiction (n : Nat) (hn4 : n % 4 ≠ 0)
    (d : Nat → Bool) (hstep : ∀ j, d (j + 2) = !(d j))
    (hper : ∀ j, d (j + n) = d j) : False := by
  have hcase : n % 2 = 1 ∨ (n % 2 = 0 ∧ (n / 2) % 2 = 1) := by
    cases mod_two_cases n with
    | inl heven =>
      cases mod_two_cases (n / 2) with
      | inl hzero => exact absurd (by omega : n % 4 = 0) hn4
      | inr hone => exact Or.inr ⟨heven, hone⟩
    | inr hodd => exact Or.inl hodd
  obtain hodd | ⟨heven, hhalf⟩ := hcase
  · have hdouble : d (2 * n) = d 0 := by
      have hp1 := hper 0
      have hp2 := hper (0 + n)
      rw [Nat.zero_add] at hp1 hp2
      have e : n + n = 2 * n := by omega
      rw [e] at hp2
      exact hp2.trans hp1
    have h := d_period_flip d hstep n 0
    rw [Nat.zero_add, hdouble, hodd] at h
    cases hd : d 0 with
    | false => rw [hd] at h; exact Bool.noConfusion h
    | true => rw [hd] at h; exact Bool.noConfusion h
  · have h := d_period_flip d hstep (n / 2) 0
    rw [Nat.zero_add, hhalf] at h
    have e : 2 * (n / 2) = n := by omega
    rw [e] at h
    have hp1 := hper 0
    rw [Nat.zero_add] at hp1
    rw [hp1] at h
    cases hd : d 0 with
    | false => rw [hd] at h; exact Bool.noConfusion h
    | true => rw [hd] at h; exact Bool.noConfusion h

/-- No alternating mask exists on a carrier outside `4Z`. -/
private theorem no_alternating_of_mod {m : Nat}
    (h4 : (m + 1) % 4 ≠ 0) (a : Field (m + 1))
    (ha : Alternating a) : False := by
  cases m with
  | zero =>
    have hx : (a 0 ^^ a 0) = true := ha 0
    cases h0 : a 0 with
    | false => rw [h0] at hx; exact Bool.noConfusion hx
    | true => rw [h0] at hx; exact Bool.noConfusion hx
  | succ m' =>
    exact stream_contradiction (m' + 1 + 1) h4 (streamOf a)
      (stream_step (Nat.succ_le_succ (Nat.zero_le m')) a ha)
      (stream_period a)

/-- **An alternating mask forces divisibility by four.** -/
theorem alternating_forces_four_dvd {m : Nat} (a : Field (m + 1))
    (ha : Alternating a) : (m + 1) % 4 = 0 :=
  if h : (m + 1) % 4 = 0 then h
  else (no_alternating_of_mod h a ha).elim

/-- **Alternating masks exist exactly on carriers divisible by
    four.** -/
theorem alternating_mask_iff_four_dvd {m : Nat} :
    (∃ a : Field (m + 1), Alternating a) ↔ (m + 1) % 4 = 0 :=
  ⟨fun ⟨a, ha⟩ => alternating_forces_four_dvd a ha,
   fun h4 => ⟨mask4, mask4_alternating h4⟩⟩

/-! ## The fixed-point spectra -/

/-- The zero state: both layers silent. -/
def zeroS {n : Nat} : WState n :=
  (fun _ => false, fun _ => false)

/-- The ring step fixes the zero state, definitionally, at every
    carrier size. -/
theorem ring_fixes_zero {m : Nat} :
    step ringX (zeroS (n := m + 1)) = zeroS := rfl

/-- Outside `4Z` the flipped step fixes no state, even pointwise: a
    pointwise-fixed state's current layer would be an alternating
    mask. -/
theorem flip_no_fixed_pointwise {m : Nat} (h4 : (m + 1) % 4 ≠ 0)
    (s : WState (m + 1))
    (h1 : ∀ i, (step (flipX ringX) s).1 i = s.1 i)
    (h2 : ∀ i, (step (flipX ringX) s).2 i = s.2 i) : False := by
  apply no_alternating_of_mod h4 s.2
  intro i
  have e1 : s.2 i = s.1 i := h1 i
  have e2 : (s.1 i ^^ !(ringX s.2 i)) = s.2 i := h2 i
  rw [← e1] at e2
  have e3 : (!(ringX s.2 i)) = false :=
    cancel_of_xor_eq (s.2 i) (!(ringX s.2 i)) e2
  exact true_of_not_false (ringX s.2 i) e3

/-- Outside `4Z` the flipped step fixes no state (packaged form). -/
theorem flip_no_fixed_point {m : Nat} (h4 : (m + 1) % 4 ≠ 0)
    (s : WState (m + 1)) (hs : step (flipX ringX) s = s) : False :=
  flip_no_fixed_pointwise h4 s
    (fun i => congrArg (fun w : WState (m + 1) => w.1 i) hs)
    (fun i => congrArg (fun w : WState (m + 1) => w.2 i) hs)

/-- **The spectra separate.** Outside `4Z` the ring dynamics fixes
    the zero state while the flipped dynamics fixes no state: the two
    cycle structures differ already at cycle length one. -/
theorem fixed_point_spectra_differ {m : Nat} (h4 : (m + 1) % 4 ≠ 0) :
    (step ringX (zeroS (n := m + 1)) = zeroS) ∧
    (∀ s : WState (m + 1), step (flipX ringX) s ≠ s) :=
  ⟨ring_fixes_zero, fun s hs => flip_no_fixed_point h4 s hs⟩

/-! ## The decisive theorems -/

/-- **R2, pointwise form.** Outside `4Z`, no map of state spaces
    intertwines the plain and flipped ring dynamics, even pointwise
    and even without injectivity: the definitional fixed point of the
    plain step transports through any candidate intertwiner to a
    fixed point of the flipped step, and none exists. -/
theorem flip_no_intertwiner_pointwise {m : Nat}
    (h4 : (m + 1) % 4 ≠ 0)
    (φ : WState (m + 1) → WState (m + 1))
    (h : ∀ s,
      (∀ i, (φ (step ringX s)).1 i = (step (flipX ringX) (φ s)).1 i) ∧
      (∀ i, (φ (step ringX s)).2 i = (step (flipX ringX) (φ s)).2 i)) :
    False := by
  have hz := h zeroS
  rw [ring_fixes_zero] at hz
  exact flip_no_fixed_pointwise h4 (φ zeroS)
    (fun i => (hz.1 i).symm) (fun i => (hz.2 i).symm)

/-- **R2, packaged form.** Outside `4Z` there is no equivariant map
    from the plain ring dynamics to the flipped ring dynamics. -/
theorem flip_no_intertwiner {m : Nat} (h4 : (m + 1) % 4 ≠ 0) :
    ¬ ∃ φ : WState (m + 1) → WState (m + 1),
        ∀ s, φ (step ringX s) = step (flipX ringX) (φ s) := by
  intro hex
  obtain ⟨φ, hφ⟩ := hex
  exact flip_no_intertwiner_pointwise h4 φ (fun s =>
    ⟨fun i => congrArg (fun w : WState (m + 1) => w.1 i) (hφ s),
     fun i => congrArg (fun w : WState (m + 1) => w.2 i) (hφ s)⟩)

/-- **R2, conjugacy form.** Outside `4Z` the two dynamics are
    conjugate by no state-space bijection: a conjugating bijection
    would in particular be an equivariant map. -/
theorem flip_not_conjugate {m : Nat} (h4 : (m + 1) % 4 ≠ 0) :
    ¬ ∃ (φ ψ : WState (m + 1) → WState (m + 1)),
        (∀ s, ψ (φ s) = s) ∧ (∀ s, φ (ψ s) = s) ∧
        (∀ s, φ (step ringX s) = step (flipX ringX) (φ s)) := by
  intro hex
  obtain ⟨φ, _, _, _, hφ⟩ := hex
  exact flip_no_intertwiner h4 ⟨φ, hφ⟩

/-- **R1 on carriers divisible by four.** The half-period pole mask
    is an involution on states conjugating the plain ring dynamics to
    the flipped ring dynamics exactly. On these carriers the coupling
    flip is packaging. Uses function extensionality (`funext` with
    `Prod.ext`) to package the pointwise conjugacy; the lift is made
    in daylight and flagged in `AXIOMS.md`. -/
theorem flip_conjugacy_of_four_dvd {m : Nat} (h4 : (m + 1) % 4 = 0) :
    ∃ φ : WState (m + 1) → WState (m + 1),
      (∀ s, φ (φ s) = s) ∧
      (∀ s, φ (step ringX s) = step (flipX ringX) (φ s)) := by
  refine ⟨maskS mask4, fun s => ?_, fun s => ?_⟩
  · have h := maskS_involution_pointwise mask4 s
    exact Prod.ext (funext h.1) (funext h.2)
  · have h := mask_intertwines_pointwise mask4 (mask4_alternating h4) s
    exact Prod.ext (funext h.1) (funext h.2)

/-- **The coupling-flip dichotomy.** On carriers divisible by four
    the coupling flip is realised by an involutive state-space
    conjugacy, and on every other carrier no equivariant map between
    the two dynamics exists at all. The gauge class of the flip is
    thereby decided at every carrier size. -/
theorem coupling_flip_dichotomy {m : Nat} :
    ((m + 1) % 4 = 0 →
      ∃ φ : WState (m + 1) → WState (m + 1),
        (∀ s, φ (φ s) = s) ∧
        (∀ s, φ (step ringX s) = step (flipX ringX) (φ s))) ∧
    ((m + 1) % 4 ≠ 0 →
      ¬ ∃ φ : WState (m + 1) → WState (m + 1),
          ∀ s, φ (step ringX s) = step (flipX ringX) (φ s)) :=
  ⟨flip_conjugacy_of_four_dvd, flip_no_intertwiner⟩

/-- The conjugacy instantiated on the paper's four-site carrier. -/
theorem flip_conjugate_four :
    ∃ φ : WState 4 → WState 4,
      (∀ s, φ (φ s) = s) ∧
      (∀ s, φ (step ringX s) = step (flipX ringX) (φ s)) :=
  flip_conjugacy_of_four_dvd (by decide)

/-- The negative instantiated on two sites. -/
theorem flip_no_intertwiner_two :
    ¬ ∃ φ : WState 2 → WState 2,
        ∀ s, φ (step ringX s) = step (flipX ringX) (φ s) :=
  flip_no_intertwiner (by decide)

/-- The negative instantiated on three sites. -/
theorem flip_no_intertwiner_three :
    ¬ ∃ φ : WState 3 → WState 3,
        ∀ s, φ (step ringX s) = step (flipX ringX) (φ s) :=
  flip_no_intertwiner (by decide)

/-- The negative instantiated on five sites. -/
theorem flip_no_intertwiner_five :
    ¬ ∃ φ : WState 5 → WState 5,
        ∀ s, φ (step ringX s) = step (flipX ringX) (φ s) :=
  flip_no_intertwiner (by decide)

/-! ## Tick-periodic dressing at every size

The per-tick flip form iterates into a dressing of the plain
evolution by constant pole masks on the two layers, cycling with
period four through identity, flip the current layer, flip both
layers, flip the previous layer. The dressing exists at every
carrier size; the decisive theorems show that outside `4Z` it cannot
be traded for a single time-independent map. -/

/-- Dressing a state by constant pole masks, one per layer. -/
def dress {n : Nat} (u v : Bool) (s : WState n) : WState n :=
  (fun i => s.1 i ^^ u, fun i => s.2 i ^^ v)

/-- The previous-layer mask of the tick schedule. -/
def uSched (T : Nat) : Bool :=
  decide (T % 4 = 2) || decide (T % 4 = 3)

/-- The current-layer mask of the tick schedule. -/
def vSched (T : Nat) : Bool :=
  decide (T % 4 = 1) || decide (T % 4 = 2)

private theorem uSched_succ (T : Nat) : uSched (T + 1) = vSched T := by
  show (decide ((T + 1) % 4 = 2) || decide ((T + 1) % 4 = 3))
      = (decide (T % 4 = 1) || decide (T % 4 = 2))
  have hc : T % 4 = 0 ∨ T % 4 = 1 ∨ T % 4 = 2 ∨ T % 4 = 3 := by omega
  obtain h | h | h | h := hc
  · rw [show (T + 1) % 4 = 1 by omega, h]; rfl
  · rw [show (T + 1) % 4 = 2 by omega, h]; rfl
  · rw [show (T + 1) % 4 = 3 by omega, h]; rfl
  · rw [show (T + 1) % 4 = 0 by omega, h]; rfl

private theorem vSched_succ (T : Nat) :
    vSched (T + 1) = !(uSched T) := by
  show (decide ((T + 1) % 4 = 1) || decide ((T + 1) % 4 = 2))
      = !(decide (T % 4 = 2) || decide (T % 4 = 3))
  have hc : T % 4 = 0 ∨ T % 4 = 1 ∨ T % 4 = 2 ∨ T % 4 = 3 := by omega
  obtain h | h | h | h := hc
  · rw [show (T + 1) % 4 = 1 by omega, h]; rfl
  · rw [show (T + 1) % 4 = 2 by omega, h]; rfl
  · rw [show (T + 1) % 4 = 3 by omega, h]; rfl
  · rw [show (T + 1) % 4 = 0 by omega, h]; rfl

/-- The flipped step sends pointwise-equal states to pointwise-equal
    states (the coupling reads only three sites). -/
theorem flip_step_congr_pointwise {m : Nat} (a b : WState (m + 1))
    (h1 : ∀ i, a.1 i = b.1 i) (h2 : ∀ i, a.2 i = b.2 i) :
    (∀ i, (step (flipX ringX) a).1 i = (step (flipX ringX) b).1 i) ∧
    (∀ i, (step (flipX ringX) a).2 i = (step (flipX ringX) b).2 i) :=
  ⟨h2, fun i => by
    show (a.1 i ^^ !(a.2 (i - 1) ^^ a.2 (i + 1)))
        = (b.1 i ^^ !(b.2 (i - 1) ^^ b.2 (i + 1)))
    rw [h1 i, h2 (i - 1), h2 (i + 1)]⟩

/-- One flipped step advances the dressing by one tick of the
    schedule: dressing by `(u, v)` before the flipped step equals
    dressing by `(v, !u)` after the plain step, pointwise. -/
theorem flip_step_dress_pointwise {m : Nat} (u v : Bool)
    (s : WState (m + 1)) :
    (∀ i, (step (flipX ringX) (dress u v s)).1 i
        = (dress v (!u) (step ringX s)).1 i) ∧
    (∀ i, (step (flipX ringX) (dress u v s)).2 i
        = (dress v (!u) (step ringX s)).2 i) := by
  refine ⟨fun _ => rfl, fun i => ?_⟩
  show ((s.1 i ^^ u) ^^ !((s.2 (i - 1) ^^ v) ^^ (s.2 (i + 1) ^^ v)))
      = ((s.1 i ^^ ringX s.2 i) ^^ !u)
  rw [xor_pair_exchange (s.2 (i - 1)) v (s.2 (i + 1)) v,
    Bool.xor_self, Bool.xor_false]
  exact xor_not_exchange (s.1 i) u (s.2 (i - 1) ^^ s.2 (i + 1))

/-- **Tick-periodic dressing.** At every carrier size and every time
    `T`, the flipped evolution equals the plain evolution dressed by
    the period-four constant-mask schedule, pointwise on both
    layers. The coupling flip is a per-tick repackaging of the same
    evolution; only its trade for a time-independent map depends on
    the carrier size. -/
theorem flip_iter_dress_pointwise {m : Nat} (T : Nat)
    (s : WState (m + 1)) :
    (∀ i, (iterN (step (flipX ringX)) T s).1 i
        = (dress (uSched T) (vSched T) (iterN (step ringX) T s)).1 i) ∧
    (∀ i, (iterN (step (flipX ringX)) T s).2 i
        = (dress (uSched T) (vSched T) (iterN (step ringX) T s)).2 i) := by
  induction T with
  | zero =>
    exact ⟨fun i => (Bool.xor_false _).symm,
      fun i => (Bool.xor_false _).symm⟩
  | succ T ih =>
    have hcong := flip_step_congr_pointwise
      (iterN (step (flipX ringX)) T s)
      (dress (uSched T) (vSched T) (iterN (step ringX) T s)) ih.1 ih.2
    have hdress := flip_step_dress_pointwise (uSched T) (vSched T)
      (iterN (step ringX) T s)
    refine ⟨fun i => ?_, fun i => ?_⟩
    · rw [iterN_succ_out (step (flipX ringX)) T s,
        iterN_succ_out (step ringX) T s, uSched_succ T, vSched_succ T]
      exact (hcong.1 i).trans (hdress.1 i)
    · rw [iterN_succ_out (step (flipX ringX)) T s,
        iterN_succ_out (step ringX) T s, uSched_succ T, vSched_succ T]
      exact (hcong.2 i).trans (hdress.2 i)

/-! ## Kernel exhibits

The single-pulse experiment of the period table, run under the
flipped coupling. Sizes 2, 3, 4 are decided directly by the kernel;
the five-site exhibit is assembled through the dressing theorem in
the subsection below. Sizes 2, 3, 5 double their plain periods, and
size 4 keeps its plain period; the four exhibits instantiate the
dichotomy on the exhibit carriers. -/

/-- Ring of two, flipped coupling: state period 4 against the plain
    period 2 of `Experimental.Wave.ring2_period_two`. -/
theorem flip_ring2_pulse_period_four :
    (∀ i, (iterN (step (flipX ringX)) 4 (pulseN 1)).1 i
        = (pulseN 1).1 i) ∧
    (∀ i, (iterN (step (flipX ringX)) 4 (pulseN 1)).2 i
        = (pulseN 1).2 i) ∧
    (∀ k : Fin 4, k.val ≠ 0 →
      (∃ i, (iterN (step (flipX ringX)) k.val (pulseN 1)).1 i
        ≠ (pulseN 1).1 i) ∨
      (∃ i, (iterN (step (flipX ringX)) k.val (pulseN 1)).2 i
        ≠ (pulseN 1).2 i)) := by
  decide

/-- Ring of three, flipped coupling: state period 12 against the
    plain period 6 of `Experimental.Wave.ring3_period_six`. -/
theorem flip_ring3_pulse_period_twelve :
    (∀ i, (iterN (step (flipX ringX)) 12 (pulseN 2)).1 i
        = (pulseN 2).1 i) ∧
    (∀ i, (iterN (step (flipX ringX)) 12 (pulseN 2)).2 i
        = (pulseN 2).2 i) ∧
    (∀ k : Fin 12, k.val ≠ 0 →
      (∃ i, (iterN (step (flipX ringX)) k.val (pulseN 2)).1 i
        ≠ (pulseN 2).1 i) ∨
      (∃ i, (iterN (step (flipX ringX)) k.val (pulseN 2)).2 i
        ≠ (pulseN 2).2 i)) := by
  decide

/-- Ring of four, flipped coupling: state period 4, agreeing with the
    plain period of `Bridge.WaveDynamics.ring4_period_four`, as the
    conjugacy `flip_conjugate_four` requires. -/
theorem flip_ring4_pulse_period_four :
    (∀ i, (iterN (step (flipX ringX)) 4 (pulseN 3)).1 i
        = (pulseN 3).1 i) ∧
    (∀ i, (iterN (step (flipX ringX)) 4 (pulseN 3)).2 i
        = (pulseN 3).2 i) ∧
    (∀ k : Fin 4, k.val ≠ 0 →
      (∃ i, (iterN (step (flipX ringX)) k.val (pulseN 3)).1 i
        ≠ (pulseN 3).1 i) ∨
      (∃ i, (iterN (step (flipX ringX)) k.val (pulseN 3)).2 i
        ≠ (pulseN 3).2 i)) := by
  decide

/-! ### Ring of five through the dressing

A direct kernel decision of the twenty-step flipped orbit on five
sites is out of reach: evaluating the iterate at one site unfolds the
step closure at three sites of the predecessor state, so the
reduction cost grows exponentially in the horizon, near `3^20` for
this exhibit. The dressing theorem removes the wall. The flipped
iterate equals the plain iterate under a constant pole mask pair
drawn from the period-four schedule, the plain orbit has period ten
(`Experimental.Wave.ring5_period_ten`), and every claim about the
flipped trajectory therefore reduces to a claim about the first ten
plain states, each of which the kernel decides cheaply. -/

/-- Splitting the iterate: the head segment first, then the
    remainder. -/
private theorem iterN_add {α : Type} (f : α → α) (a b : Nat) (x : α) :
    iterN f (a + b) x = iterN f b (iterN f a x) := by
  induction b with
  | zero => rfl
  | succ b ih =>
    show iterN f ((a + b) + 1) x = iterN f (b + 1) (iterN f a x)
    rw [iterN_succ_out f (a + b) x, ih,
      ← iterN_succ_out f b (iterN f a x)]

/-- The plain five-site pulse trajectory repeats after ten steps:
    step `10 + j` agrees with step `j`, pointwise on both layers. -/
private theorem plain5_reduce (j : Nat) :
    (∀ i, (iterN (step ringX) (10 + j) (pulseN 4)).1 i
        = (iterN (step ringX) j (pulseN 4)).1 i) ∧
    (∀ i, (iterN (step ringX) (10 + j) (pulseN 4)).2 i
        = (iterN (step ringX) j (pulseN 4)).2 i) := by
  have e := iterN_add (step ringX) 10 j (pulseN 4)
  have h10 := ring5_period_ten
  have hc := iterN_step_ringX_congr j
    (iterN (step ringX) 10 (pulseN 4)) (pulseN 4) h10.1 h10.2.1
  exact ⟨fun i => by rw [e]; exact hc.1 i,
    fun i => by rw [e]; exact hc.2 i⟩

/-- The plain five-site pulse trajectory returns at twenty steps,
    pointwise on both layers. -/
private theorem plain5_return_twenty :
    (∀ i, (iterN (step ringX) 20 (pulseN 4)).1 i = (pulseN 4).1 i) ∧
    (∀ i, (iterN (step ringX) 20 (pulseN 4)).2 i = (pulseN 4).2 i) := by
  have hr := plain5_reduce 10
  have h10 := ring5_period_ten
  exact ⟨fun i => (hr.1 i).trans (h10.1 i),
    fun i => (hr.2 i).trans (h10.2.1 i)⟩

/-- Transport of an exhibited difference from the dressed plain
    trajectory to the flipped trajectory: if the plain state at time
    `T` agrees pointwise with the plain state at time `j`, and the
    time-`j` plain state dressed by the time-`T` schedule masks
    differs somewhere from the pulse, then the flipped state at time
    `T` differs somewhere from the pulse. -/
private theorem flip5_differs (T j : Nat)
    (hred : (∀ i, (iterN (step ringX) T (pulseN 4)).1 i
                = (iterN (step ringX) j (pulseN 4)).1 i) ∧
            (∀ i, (iterN (step ringX) T (pulseN 4)).2 i
                = (iterN (step ringX) j (pulseN 4)).2 i))
    (hdec : (∃ i, ((iterN (step ringX) j (pulseN 4)).1 i ^^ uSched T)
              ≠ (pulseN 4).1 i) ∨
            (∃ i, ((iterN (step ringX) j (pulseN 4)).2 i ^^ vSched T)
              ≠ (pulseN 4).2 i)) :
    (∃ i, (iterN (step (flipX ringX)) T (pulseN 4)).1 i
      ≠ (pulseN 4).1 i) ∨
    (∃ i, (iterN (step (flipX ringX)) T (pulseN 4)).2 i
      ≠ (pulseN 4).2 i) := by
  have hd := flip_iter_dress_pointwise T (pulseN 4)
  cases hdec with
  | inl h =>
    obtain ⟨i, hi⟩ := h
    refine Or.inl ⟨i, fun hcon => hi ?_⟩
    calc ((iterN (step ringX) j (pulseN 4)).1 i ^^ uSched T)
        = ((iterN (step ringX) T (pulseN 4)).1 i ^^ uSched T) := by
          rw [hred.1 i]
      _ = (dress (uSched T) (vSched T)
            (iterN (step ringX) T (pulseN 4))).1 i := rfl
      _ = (iterN (step (flipX ringX)) T (pulseN 4)).1 i :=
          (hd.1 i).symm
      _ = (pulseN 4).1 i := hcon
  | inr h =>
    obtain ⟨i, hi⟩ := h
    refine Or.inr ⟨i, fun hcon => hi ?_⟩
    calc ((iterN (step ringX) j (pulseN 4)).2 i ^^ vSched T)
        = ((iterN (step ringX) T (pulseN 4)).2 i ^^ vSched T) := by
          rw [hred.2 i]
      _ = (dress (uSched T) (vSched T)
            (iterN (step ringX) T (pulseN 4))).2 i := rfl
      _ = (iterN (step (flipX ringX)) T (pulseN 4)).2 i :=
          (hd.2 i).symm
      _ = (pulseN 4).2 i := hcon

/-- Ring of five, flipped coupling: state period 20 against the plain
    period 10 of `Experimental.Wave.ring5_period_ten`. A direct
    kernel decision of the twenty-step orbit is out of reach, so the
    exhibit is assembled: the return at twenty follows from the plain
    return at ten taken twice, because the tick schedule is silent at
    multiples of four, and each of the nineteen minimality cases
    reduces through the dressing theorem to a kernel decision on the
    first ten plain states. -/
theorem flip_ring5_pulse_period_twenty :
    (∀ i, (iterN (step (flipX ringX)) 20 (pulseN 4)).1 i
        = (pulseN 4).1 i) ∧
    (∀ i, (iterN (step (flipX ringX)) 20 (pulseN 4)).2 i
        = (pulseN 4).2 i) ∧
    (∀ k : Fin 20, k.val ≠ 0 →
      (∃ i, (iterN (step (flipX ringX)) k.val (pulseN 4)).1 i
        ≠ (pulseN 4).1 i) ∨
      (∃ i, (iterN (step (flipX ringX)) k.val (pulseN 4)).2 i
        ≠ (pulseN 4).2 i)) := by
  have hd := flip_iter_dress_pointwise 20 (pulseN 4)
  have hp := plain5_return_twenty
  refine ⟨fun i => ?_, fun i => ?_, fun k hk => ?_⟩
  · calc (iterN (step (flipX ringX)) 20 (pulseN 4)).1 i
        = (dress (uSched 20) (vSched 20)
            (iterN (step ringX) 20 (pulseN 4))).1 i := hd.1 i
      _ = (iterN (step ringX) 20 (pulseN 4)).1 i := by
          show ((iterN (step ringX) 20 (pulseN 4)).1 i ^^ uSched 20)
              = (iterN (step ringX) 20 (pulseN 4)).1 i
          rw [show uSched 20 = false from rfl]
          exact Bool.xor_false _
      _ = (pulseN 4).1 i := hp.1 i
  · calc (iterN (step (flipX ringX)) 20 (pulseN 4)).2 i
        = (dress (uSched 20) (vSched 20)
            (iterN (step ringX) 20 (pulseN 4))).2 i := hd.2 i
      _ = (iterN (step ringX) 20 (pulseN 4)).2 i := by
          show ((iterN (step ringX) 20 (pulseN 4)).2 i ^^ vSched 20)
              = (iterN (step ringX) 20 (pulseN 4)).2 i
          rw [show vSched 20 = false from rfl]
          exact Bool.xor_false _
      _ = (pulseN 4).2 i := hp.2 i
  · match k, hk with
    | ⟨0, _⟩, hk => exact absurd rfl hk
    | ⟨1, _⟩, _ =>
      exact flip5_differs 1 1 ⟨fun _ => rfl, fun _ => rfl⟩ (by decide)
    | ⟨2, _⟩, _ =>
      exact flip5_differs 2 2 ⟨fun _ => rfl, fun _ => rfl⟩ (by decide)
    | ⟨3, _⟩, _ =>
      exact flip5_differs 3 3 ⟨fun _ => rfl, fun _ => rfl⟩ (by decide)
    | ⟨4, _⟩, _ =>
      exact flip5_differs 4 4 ⟨fun _ => rfl, fun _ => rfl⟩ (by decide)
    | ⟨5, _⟩, _ =>
      exact flip5_differs 5 5 ⟨fun _ => rfl, fun _ => rfl⟩ (by decide)
    | ⟨6, _⟩, _ =>
      exact flip5_differs 6 6 ⟨fun _ => rfl, fun _ => rfl⟩ (by decide)
    | ⟨7, _⟩, _ =>
      exact flip5_differs 7 7 ⟨fun _ => rfl, fun _ => rfl⟩ (by decide)
    | ⟨8, _⟩, _ =>
      exact flip5_differs 8 8 ⟨fun _ => rfl, fun _ => rfl⟩ (by decide)
    | ⟨9, _⟩, _ =>
      exact flip5_differs 9 9 ⟨fun _ => rfl, fun _ => rfl⟩ (by decide)
    | ⟨10, _⟩, _ =>
      exact flip5_differs 10 0 (plain5_reduce 0) (by decide)
    | ⟨11, _⟩, _ =>
      exact flip5_differs 11 1 (plain5_reduce 1) (by decide)
    | ⟨12, _⟩, _ =>
      exact flip5_differs 12 2 (plain5_reduce 2) (by decide)
    | ⟨13, _⟩, _ =>
      exact flip5_differs 13 3 (plain5_reduce 3) (by decide)
    | ⟨14, _⟩, _ =>
      exact flip5_differs 14 4 (plain5_reduce 4) (by decide)
    | ⟨15, _⟩, _ =>
      exact flip5_differs 15 5 (plain5_reduce 5) (by decide)
    | ⟨16, _⟩, _ =>
      exact flip5_differs 16 6 (plain5_reduce 6) (by decide)
    | ⟨17, _⟩, _ =>
      exact flip5_differs 17 7 (plain5_reduce 7) (by decide)
    | ⟨18, _⟩, _ =>
      exact flip5_differs 18 8 (plain5_reduce 8) (by decide)
    | ⟨19, _⟩, _ =>
      exact flip5_differs 19 9 (plain5_reduce 9) (by decide)
    | ⟨j + 20, h⟩, _ => exact absurd h (by omega)

/-- The block mask alternates on the four-site carrier, decided by
    the kernel. -/
theorem mask4_alternating_four :
    ∀ i : Fin 4, ringX (mask4 (n := 4)) i = true := by
  decide

#print axioms Experimental.CouplingGauge.xor_not_right
#print axioms Experimental.CouplingGauge.xor_right_comm
#print axioms Experimental.CouplingGauge.xor_pair_exchange
#print axioms Experimental.CouplingGauge.xor_not_exchange
#print axioms Experimental.CouplingGauge.cancel_of_xor_eq
#print axioms Experimental.CouplingGauge.true_of_not_false
#print axioms Experimental.CouplingGauge.flip_of_xor_true
#print axioms Experimental.CouplingGauge.flip_step_pointwise
#print axioms Experimental.CouplingGauge.maskS_involution_pointwise
#print axioms Experimental.CouplingGauge.ringX_mask_pointwise
#print axioms Experimental.CouplingGauge.mask_intertwines_pointwise
#print axioms Experimental.CouplingGauge.mod_mod_four
#print axioms Experimental.CouplingGauge.mask4_alternating
#print axioms Experimental.CouplingGauge.stream_step
#print axioms Experimental.CouplingGauge.stream_period
#print axioms Experimental.CouplingGauge.d_period_flip
#print axioms Experimental.CouplingGauge.mod_two_cases
#print axioms Experimental.CouplingGauge.stream_contradiction
#print axioms Experimental.CouplingGauge.no_alternating_of_mod
#print axioms Experimental.CouplingGauge.alternating_forces_four_dvd
#print axioms Experimental.CouplingGauge.alternating_mask_iff_four_dvd
#print axioms Experimental.CouplingGauge.ring_fixes_zero
#print axioms Experimental.CouplingGauge.flip_no_fixed_pointwise
#print axioms Experimental.CouplingGauge.flip_no_fixed_point
#print axioms Experimental.CouplingGauge.fixed_point_spectra_differ
#print axioms Experimental.CouplingGauge.flip_no_intertwiner_pointwise
#print axioms Experimental.CouplingGauge.flip_no_intertwiner
#print axioms Experimental.CouplingGauge.flip_not_conjugate
#print axioms Experimental.CouplingGauge.flip_conjugacy_of_four_dvd
#print axioms Experimental.CouplingGauge.coupling_flip_dichotomy
#print axioms Experimental.CouplingGauge.flip_conjugate_four
#print axioms Experimental.CouplingGauge.flip_no_intertwiner_two
#print axioms Experimental.CouplingGauge.flip_no_intertwiner_three
#print axioms Experimental.CouplingGauge.flip_no_intertwiner_five
#print axioms Experimental.CouplingGauge.uSched_succ
#print axioms Experimental.CouplingGauge.vSched_succ
#print axioms Experimental.CouplingGauge.flip_step_congr_pointwise
#print axioms Experimental.CouplingGauge.flip_step_dress_pointwise
#print axioms Experimental.CouplingGauge.flip_iter_dress_pointwise
#print axioms Experimental.CouplingGauge.flip_ring2_pulse_period_four
#print axioms Experimental.CouplingGauge.flip_ring3_pulse_period_twelve
#print axioms Experimental.CouplingGauge.flip_ring4_pulse_period_four
#print axioms Experimental.CouplingGauge.iterN_add
#print axioms Experimental.CouplingGauge.plain5_reduce
#print axioms Experimental.CouplingGauge.plain5_return_twenty
#print axioms Experimental.CouplingGauge.flip5_differs
#print axioms Experimental.CouplingGauge.flip_ring5_pulse_period_twenty
#print axioms Experimental.CouplingGauge.mask4_alternating_four

end Experimental.CouplingGauge
