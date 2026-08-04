import Apophasis
import Branch

/-!
# Canon — the Fundamental as initial object

The Fundamental is characterized by a universal property over pointed
`SymmetricStep` acts, stated extensionally (no `Category` class).

* **Ambient** (`canon_initial`): morphisms are pointed equivariant maps;
  `(Bool, not, true)` is initial via `TwoCycle.reading`.
* **Fundamentality** (`IsFundamental`): an act is a fundamental when the initial map
  is bijective at some seed; liveness, generation, and `Draws` follow
  (`IsFundamental.live`, `exhaustive`, `sustains`); equivalence with the
  three-clause package (`isFundamental_iff_clauses`).
* **Existence** (`canon_is_fundamental`): `(Bool, not)` is a fundamental.
* **Uniqueness** (`fundamental_correspondence`): two pointed fundamentals relate
  by a unique constructive isomorphism-as-relation.
* **Name** (`theFundamental`): Lean identifier for the initial object;
  prose name is the Fundamental.
-/
namespace Canon

open Orbit

variable {α β : Type}

/-! ## Initiality of the canon -/

/-- For pointed `SymmetricStep` `act` at seed `z`, `TwoCycle.reading` is
    the unique pointed equivariant map from `(Bool, not)`. -/
theorem canon_initial (act : α → α) (hs : SymmetricStep act) (z : α) :
    (TwoCycle.reading act z true = z) ∧
    (∀ b, TwoCycle.reading act z (!b) = act (TwoCycle.reading act z b)) ∧
    (∀ e : Bool → α, e true = z → (∀ b, e (!b) = act (e b)) →
      ∀ b, e b = TwoCycle.reading act z b) :=
  ⟨rfl,
   TwoCycle.reading_equivariant act hs z,
   fun e he heq => TwoCycle.reading_unique act z e he heq⟩

/-! ## Fundamentality = iso to the initial object -/

/-- Surjectivity of the initial map at one seed, with involutivity,
    yields generation of the whole carrier. -/
theorem generated_of_initial_surj (act : α → α) (hs : SymmetricStep act)
    (z : α) (hsurj : ∀ x, ∃ b, TwoCycle.reading act z b = x) :
    TwoCycle.Generated act := by
  intro x y
  have hinv := (symmetricStep_iff_involutive act).mp hs
  obtain ⟨bx, hbx⟩ := hsurj x
  obtain ⟨byb, hby⟩ := hsurj y
  cases bx with
  | true =>
    cases byb with
    | true =>
      left
      exact hby.symm.trans hbx
    | false =>
      right
      have hx : x = z := hbx.symm
      have hy : y = act z := hby.symm
      exact hy.trans (congrArg act hx.symm)
  | false =>
    cases byb with
    | true =>
      right
      have hx : x = act z := hbx.symm
      have hy : y = z := hby.symm
      have hy' : y = act (act z) := hy.trans (hinv z).symm
      exact hy'.trans (congrArg act hx.symm)
    | false =>
      left
      exact hby.symm.trans hbx

/-- Injectivity of the initial map at a seed yields a drawn distinction. -/
theorem draws_of_initial_inj (act : α → α) (z : α)
    (hinj : ∀ b b', TwoCycle.reading act z b = TwoCycle.reading act z b' →
      b = b') : Monism.Draws α := by
  refine ⟨z, act z, ?_⟩
  intro heq
  have hread : TwoCycle.reading act z false = TwoCycle.reading act z true :=
    heq.symm
  exact Bool.noConfusion (hinj false true hread)

/-- An act is a fundamental when it is symmetric-step and the initial map is
    bijective at some seed. -/
structure IsFundamental (act : α → α) : Prop where
  /-- Ambient: objects of the category are `SymmetricStep` acts. -/
  unoriented : Orbit.SymmetricStep act
  /-- The unique map from the canon is bijective at some seed. -/
  iso_at : ∃ z : α,
    (∀ x, ∃ b, TwoCycle.reading act z b = x) ∧
    (∀ b b', TwoCycle.reading act z b = TwoCycle.reading act z b' →
      b = b')

/-- Generation, derived from surjectivity of the initial map. -/
theorem IsFundamental.exhaustive {act : α → α} (h : IsFundamental act) :
    TwoCycle.Generated act := by
  obtain ⟨z, hsurj, _hinj⟩ := h.iso_at
  exact generated_of_initial_surj act h.unoriented z hsurj

/-- The datum, derived from injectivity of the initial map. -/
theorem IsFundamental.sustains {act : α → α} (h : IsFundamental act) :
    Monism.Draws α := by
  obtain ⟨z, _hsurj, hinj⟩ := h.iso_at
  exact draws_of_initial_inj act z hinj

/-- Liveness, derived: iso-to-canon forces a drawn difference on a
    generated carrier. -/
theorem IsFundamental.live {act : α → α} (h : IsFundamental act) :
    Orbit.Live act :=
  Apophasis.draws_forces_live act h.exhaustive h.sustains

/-- Losslessness, derived: involutions are injective. -/
theorem IsFundamental.lossless {act : α → α} (h : IsFundamental act) :
    Orbit.Lossless act :=
  Orbit.symmetric_lossless act h.unoriented

/-- Involutivity, derived. -/
theorem IsFundamental.involutive {act : α → α} (h : IsFundamental act) :
    ∀ x, act (act x) = x :=
  (Orbit.symmetricStep_iff_involutive act).mp h.unoriented

/-- At every seed the initial map is an isomorphism. -/
theorem IsFundamental.iso_everywhere {act : α → α} (h : IsFundamental act)
    (z : α) :
    (∀ x, ∃ b, TwoCycle.reading act z b = x) ∧
    (∀ b b', TwoCycle.reading act z b = TwoCycle.reading act z b' →
      b = b') :=
  ⟨TwoCycle.reading_surjective act h.exhaustive z,
   TwoCycle.reading_injective act h.live z⟩

/-- Equivalence with `Draws`, symmetric step, and generation. -/
theorem isFundamental_iff_clauses (act : α → α) :
    IsFundamental act ↔
      Monism.Draws α ∧ Orbit.SymmetricStep act ∧ TwoCycle.Generated act := by
  constructor
  · intro h
    exact ⟨h.sustains, h.unoriented, h.exhaustive⟩
  · intro h
    obtain ⟨hd, hsg⟩ := h
    obtain ⟨hs, hgen⟩ := hsg
    have hl := Apophasis.draws_forces_live act hgen hd
    obtain ⟨a, _, _⟩ := hd
    exact ⟨hs, ⟨a, TwoCycle.reading_surjective act hgen a,
                 TwoCycle.reading_injective act hl a⟩⟩

/-! ## Classification -/

/-- Classification of non-fundamental shapes: fixed points collapse under
    generation; erasing acts merge iterates; non-involutivity yields
    directed steps; symmetric live acts are restless two-cycles. -/
theorem elimination (act : α → α) :
    (TwoCycle.Generated act →
      ∀ {z : α}, act z = z → ∀ w, w = z) ∧
    (Orbit.Erasing act →
      ∃ x y, x ≠ y ∧ ∀ n,
        Orbit.iter act (n + 1) x = Orbit.iter act (n + 1) y) ∧
    (∀ z, ¬ Orbit.Collides act z → act (act z) ≠ z) ∧
    (∀ z, act (act z) ≠ z →
      Orbit.Step act z (act z) ∧ ¬ Orbit.Step act (act z) z) ∧
    (Orbit.SymmetricStep act → Orbit.Live act →
      ∀ z, act (act z) = z ∧ act z ≠ z ∧
        (∀ n, Orbit.iter act n z = z ∨ Orbit.iter act n z = act z)) :=
  ⟨fun hgen {_z} hz w => Apophasis.no_static_fundamental act hgen hz w,
   fun h => Orbit.erasing_forever act h,
   fun z h => Orbit.no_collision_forces_arrow act z h,
   fun z h => Orbit.arrow_of_not_involutive act z h,
   fun hs hl => Orbit.two_cycle act hs hl⟩

/-! ## Existence -/

/-- The initial object is a fundamental: the unique map to itself is an iso. -/
theorem canon_is_fundamental : IsFundamental (not : Bool → Bool) := by
  refine ⟨TwoCycle.bool_fundamental.2.1, ⟨true, ?_, ?_⟩⟩
  · intro x
    exact ⟨x, by cases x <;> rfl⟩
  · exact TwoCycle.reading_injective not TwoCycle.bool_fundamental.1 true

/-! ## Uniqueness -/

/-- The canonical correspondence between two pointed fundamentals: relate
    points that share a Bool coordinate. -/
def Corr (act₁ : α → α) (act₂ : β → β) (z₁ : α) (z₂ : β)
    (x : α) (y : β) : Prop :=
  ∃ b : Bool,
    TwoCycle.reading act₁ z₁ b = x ∧ TwoCycle.reading act₂ z₂ b = y

/-- Uniqueness corollary of initiality: `Corr` is total, surjective,
    functional, injective, equivariant, and pointed between two
    fundamentals. -/
theorem fundamental_correspondence {act₁ : α → α} {act₂ : β → β}
    (h₁ : IsFundamental act₁) (h₂ : IsFundamental act₂) (z₁ : α) (z₂ : β) :
    (∀ x, ∃ y, Corr act₁ act₂ z₁ z₂ x y) ∧
    (∀ y, ∃ x, Corr act₁ act₂ z₁ z₂ x y) ∧
    (∀ x y y', Corr act₁ act₂ z₁ z₂ x y → Corr act₁ act₂ z₁ z₂ x y' →
      y = y') ∧
    (∀ x x' y, Corr act₁ act₂ z₁ z₂ x y → Corr act₁ act₂ z₁ z₂ x' y →
      x = x') ∧
    (∀ x y, Corr act₁ act₂ z₁ z₂ x y →
      Corr act₁ act₂ z₁ z₂ (act₁ x) (act₂ y)) ∧
    Corr act₁ act₂ z₁ z₂ z₁ z₂ := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ⟨true, rfl, rfl⟩⟩
  · intro x
    obtain ⟨b, hb⟩ :=
      TwoCycle.reading_surjective act₁ h₁.exhaustive z₁ x
    exact ⟨TwoCycle.reading act₂ z₂ b, b, hb, rfl⟩
  · intro y
    obtain ⟨b, hb⟩ :=
      TwoCycle.reading_surjective act₂ h₂.exhaustive z₂ y
    exact ⟨TwoCycle.reading act₁ z₁ b, b, rfl, hb⟩
  · intro x y y' hxy hxy'
    obtain ⟨b, hb1, hb2⟩ := hxy
    obtain ⟨b', hb1', hb2'⟩ := hxy'
    have hbb : b = b' :=
      TwoCycle.reading_injective act₁ h₁.live z₁ b b'
        (hb1.trans hb1'.symm)
    rw [← hb2, ← hb2', hbb]
  · intro x x' y hxy hx'y
    obtain ⟨b, hb1, hb2⟩ := hxy
    obtain ⟨b', hb1', hb2'⟩ := hx'y
    have hbb : b = b' :=
      TwoCycle.reading_injective act₂ h₂.live z₂ b b'
        (hb2.trans hb2'.symm)
    rw [← hb1, ← hb1', hbb]
  · intro x y hxy
    obtain ⟨b, hb1, hb2⟩ := hxy
    refine ⟨!b, ?_, ?_⟩
    · rw [← hb1]
      exact (TwoCycle.act_reads_as_not act₁ h₁.unoriented z₁ b).symm
    · rw [← hb2]
      exact (TwoCycle.act_reads_as_not act₂ h₂.unoriented z₂ b).symm

/-- Every fundamental reads as the canon: from any seed, the canonical Bool
    coordinates are an equivariant bijection with a unique pointed
    reading. -/
theorem every_fundamental_reads_as_canon {act : α → α} (h : IsFundamental act)
    (z : α) :
    (∀ b, act (TwoCycle.reading act z b) = TwoCycle.reading act z (!b)) ∧
    (∀ b b', TwoCycle.reading act z b = TwoCycle.reading act z b' →
      b = b') ∧
    (∀ x, ∃ b, TwoCycle.reading act z b = x) ∧
    (∀ e : Bool → α, e true = z → (∀ b, e (!b) = act (e b)) →
      ∀ b, e b = TwoCycle.reading act z b) :=
  ⟨TwoCycle.act_reads_as_not act h.unoriented z,
   TwoCycle.reading_injective act h.live z,
   TwoCycle.reading_surjective act h.exhaustive z,
   fun e he heq => TwoCycle.reading_unique act z e he heq⟩

/-- Any pointed equivariant map between pointed fundamentals is the
    Bool-coordinate transport: uniqueness of the isomorphism. -/
theorem fundamental_map_unique {act₁ : α → α} {act₂ : β → β}
    (h₁ : IsFundamental act₁) (_h₂ : IsFundamental act₂) (z₁ : α) (z₂ : β)
    (φ : α → β) (hφz : φ z₁ = z₂)
    (heq : ∀ x, φ (act₁ x) = act₂ (φ x)) :
    ∀ b, φ (TwoCycle.reading act₁ z₁ b) = TwoCycle.reading act₂ z₂ b := by
  intro b
  have he :
      ∀ b', φ (TwoCycle.reading act₁ z₁ (!b')) =
        act₂ (φ (TwoCycle.reading act₁ z₁ b')) := by
    intro b'
    rw [← TwoCycle.act_reads_as_not act₁ h₁.unoriented z₁ b']
    exact heq _
  exact TwoCycle.reading_unique act₂ z₂
    (fun b' => φ (TwoCycle.reading act₁ z₁ b')) hφz he b

/-! ## The name -/

/-- The initial object among pointed symmetric-step acts. -/
def theFundamental : Bool → Bool := not

theorem theFundamental_is_fundamental : IsFundamental theFundamental :=
  canon_is_fundamental

/-! ## Compatibility -/

/-- A fundamental yields an `ApophaticReading`. -/
def toReading {act : α → α} (h : IsFundamental act) :
    Apophasis.ApophaticReading :=
  ⟨α, act, h.unoriented, h.exhaustive, h.sustains⟩

/-- An `ApophaticReading` satisfies `IsFundamental`. -/
theorem ofReading (R : Apophasis.ApophaticReading) :
    IsFundamental R.actOf :=
  (isFundamental_iff_clauses R.actOf).mpr ⟨R.draws, R.unoriented, R.simple⟩

/-! ## Master theorem from fundamentality -/

/-- Master chain from the definition of fundamentality: `IsFundamental` supplies
    liveness, symmetric step, and generation. -/
theorem diagonal_monism_of_fundamental {act : α → α} (h : IsFundamental act)
    (z : α) :
    (∀ x, act (act x) = x) ∧
    (∀ x, act x ≠ x) ∧
    (∀ n, Orbit.iter act n z = z ∨ Orbit.iter act n z = act z) ∧
    (∀ b, act (TwoCycle.reading act z b) = TwoCycle.reading act z (!b)) ∧
    (∀ x, ∃ b, TwoCycle.reading act z b = x) ∧
    (∀ b b', TwoCycle.reading act z b = TwoCycle.reading act z b' →
      b = b') ∧
    (∀ (A : Type) (f : A → A → α), ¬ Diagonal.PointSurjective f) ∧
    (∀ (A B : Type) (f : A → A → α) (g : B → B → α) (ι : A → B)
      (e : A → α), Tower.NamingExtension f g ι e → ∃ b, ∀ a, ι a ≠ b) ∧
    (∀ (A : Type) (f g : A → A → α) (e : A → α),
      ¬ Tower.NamingExtension f g (fun a => a) e) ∧
    (∀ (A : Type) (f : A → A → α), ∃ g : A → α, ∀ a, f a ≠ g) ∧
    (∀ (A : Type) (f : A → A → α),
      ¬ Interior.Articulates f (Diagonal.dodgeWith act f)) ∧
    (∀ (S E : α → Bool) (z₀ : α),
      TwoCycle.TDiff S act → TwoCycle.Alive S act z₀ →
        Interior.Tracks E S → ∀ c, E (act c) = !(E c)) ∧
    (∀ (A : Type) (f f' : A → A → α),
      (∀ x, f x x = f' x x) →
        ∀ a, Cause.effectOf act f a = Cause.effectOf act f' a) ∧
    (∀ (A : Type) (f f' : A → A → α) (a : A),
      Cause.effectOf act f a ≠ Cause.effectOf act f' a ↔
        f a a ≠ f' a a) :=
  Monism.diagonal_monism act h.live h.unoriented h.exhaustive z

/-- Coordinate of a state under the canonical reading (decidable carrier). -/
def coord [DecidableEq α] (act : α → α) (z x : α) : Bool :=
  decide (TwoCycle.reading act z true = x)

theorem coord_reading [DecidableEq α] (act : α → α)
    (hl : Orbit.Live act) (hgen : TwoCycle.Generated act) (z x : α) :
    TwoCycle.reading act z (coord act z x) = x := by
  unfold coord
  cases hgen z x with
  | inl hx =>
    -- x = z = reading true
    have heq : TwoCycle.reading act z true = x := by
      rw [TwoCycle.reading, hx]
    rw [decide_eq_true heq, TwoCycle.reading, hx]
  | inr hx =>
    -- x = act z = reading false; live ⇒ x ≠ z
    have hne : TwoCycle.reading act z true ≠ x := by
      intro he
      exact hl z (by
        show act z = z
        calc
          act z = x := hx.symm
          _ = TwoCycle.reading act z true := he.symm
          _ = z := rfl)
    rw [decide_eq_false hne, TwoCycle.reading, hx]

theorem coord_of_reading [DecidableEq α] (act : α → α)
    (hl : Orbit.Live act) (hgen : TwoCycle.Generated act) (z : α)
    (b : Bool) : coord act z (TwoCycle.reading act z b) = b :=
  TwoCycle.reading_injective act hl z _ _
    (coord_reading act hl hgen z (TwoCycle.reading act z b))

/-- Underdetermination for any fundamental on a decidable carrier: every
    self-reading omits at least two distinct predicates. -/
theorem underdetermined_of_fundamental [DecidableEq α] {act : α → α}
    (h : IsFundamental act) (z : α) (f : α → α → α) :
    ∃ g₁ g₂ : α → α,
      (∃ x, g₁ x ≠ g₂ x) ∧
      (∀ a, f a ≠ g₁) ∧
      (∀ a, f a ≠ g₂) := by
  let fB : Bool → Bool → Bool := fun b b' =>
    coord act z (f (TwoCycle.reading act z b) (TwoCycle.reading act z b'))
  obtain ⟨gB, hB, hgh, hgu, hhv⟩ := Tower.underdetermined_at_fundamental fB
  refine
    ⟨fun x => TwoCycle.reading act z (gB (coord act z x)),
     fun x => TwoCycle.reading act z (hB (coord act z x)), ?_, ?_, ?_⟩
  · obtain ⟨b, hb⟩ := hgh
    refine ⟨TwoCycle.reading act z b, ?_⟩
    intro he
    have hcoord := coord_of_reading act h.live h.exhaustive z b
    have he' :
        gB (coord act z (TwoCycle.reading act z b)) =
          hB (coord act z (TwoCycle.reading act z b)) :=
      TwoCycle.reading_injective act h.live z _ _ he
    rw [hcoord] at he'
    exact hb he'
  · intro a heq
    obtain ⟨b, hb⟩ := TwoCycle.reading_surjective act h.exhaustive z a
    obtain ⟨x, hx⟩ := hgu b
    apply hx
    have hcx := coord_of_reading act h.live h.exhaustive z x
    have heqx :
        f (TwoCycle.reading act z b) (TwoCycle.reading act z x) =
          TwoCycle.reading act z (gB x) := by
      have := congrFun heq (TwoCycle.reading act z x)
      rw [← hb] at this
      -- this: f (reading b) (reading x) = reading (gB (coord (reading x)))
      rw [hcx] at this
      exact this
    change coord act z
        (f (TwoCycle.reading act z b) (TwoCycle.reading act z x)) = gB x
    rw [heqx, coord_of_reading act h.live h.exhaustive z (gB x)]
  · intro a heq
    obtain ⟨b, hb⟩ := TwoCycle.reading_surjective act h.exhaustive z a
    obtain ⟨x, hx⟩ := hhv b
    apply hx
    have hcx := coord_of_reading act h.live h.exhaustive z x
    have heqx :
        f (TwoCycle.reading act z b) (TwoCycle.reading act z x) =
          TwoCycle.reading act z (hB x) := by
      have := congrFun heq (TwoCycle.reading act z x)
      rw [← hb, hcx] at this
      exact this
    change coord act z
        (f (TwoCycle.reading act z b) (TwoCycle.reading act z x)) = hB x
    rw [heqx, coord_of_reading act h.live h.exhaustive z (hB x)]

/-- Gathered package from fundamentality: master chain, underdetermination
    on the canon, ladder, and escape-parameterised causation. -/
theorem master_of_fundamental {act : α → α} [DecidableEq α]
    (h : IsFundamental act) (z : α) :
    -- definitional master
    (∀ x, act (act x) = x) ∧
    (∀ x, act x ≠ x) ∧
    (∀ (A : Type) (f : A → A → α), ¬ Diagonal.PointSurjective f) ∧
    -- underdetermination at this fundamental
    (∀ f : α → α → α, ∃ g₁ g₂ : α → α,
      (∃ x, g₁ x ≠ g₂ x) ∧ (∀ a, f a ≠ g₁) ∧ (∀ a, f a ≠ g₂)) ∧
    -- explicit ladder facts on the Bool model
    (∀ k, Tower.NamingExtension (Ladder.rep k) (Ladder.rep (k + 1)) some
      (Ladder.dodgeEscape k)) ∧
    (∀ k, ¬ Diagonal.PointSurjective (Ladder.rep k)) ∧
    -- underdetermination at every ladder level
    (∀ k (f : Ladder.Level k → Ladder.Level k → Bool),
      ∃ g h : Ladder.Level k → Bool,
        (∃ x, g x ≠ h x) ∧
        (∀ a, ∃ x, f a x ≠ g x) ∧
        (∀ a, ∃ x, f a x ≠ h x)) ∧
    -- intervention on dodge steps; escape policies diverge at every level
    (∀ (A : Type) (f f' : A → A → Bool) (a : A),
      f a a ≠ f' a a →
        Cause.step f none (some a) ≠ Cause.step f' none (some a)) ∧
    (∀ k, ∃ π π' : Cause.Policy, π.WF ∧ π'.WF ∧
      ∃ x : Ladder.Level k,
        Cause.repP π (k + 1) none (some x) ≠
          Cause.repP π' (k + 1) none (some x)) := by
  have m := diagonal_monism_of_fundamental h z
  refine ⟨m.1, m.2.1, m.2.2.2.2.2.2.1, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun f => underdetermined_of_fundamental h z f
  · exact fun k => Ladder.ladder_step k
  · exact fun k => Ladder.ladder_never_settles k
  · exact fun k f => Ladder.underdetermined_at_level k f
  · exact fun A f f' a hne => Cause.intervention_changes_dodge f f' a hne
  · exact fun k => Cause.escapes_differ_at k

/-- Modal package from fundamentality: escape branching, committed path,
    seal along every path, and ascent necessary with direction free. -/
theorem modal_of_fundamental {act : α → α} (_h : IsFundamental act) (_z : α) :
    (∀ k (f : Ladder.Level k → Ladder.Level k → Bool),
      ∃ e₁ e₂ : Branch.Predicate k,
        Branch.IsEscape k f e₁ ∧ Branch.IsEscape k f e₂ ∧
          ∃ x, e₁ x ≠ e₂ x) ∧
    Branch.committed.WF ∧
    (∀ π : Branch.Path, ∀ k, ¬ Diagonal.PointSurjective (π.rep k)) ∧
    (∀ k (f : Ladder.Level k → Ladder.Level k → Bool),
      Branch.Nec ⟨f⟩ (fun n' => ¬ Diagonal.PointSurjective n'.reading) ∧
      ∃ e₁ e₂ : Branch.Predicate k,
        Branch.IsEscape k f e₁ ∧ Branch.IsEscape k f e₂ ∧
          (∃ x, e₁ x ≠ e₂ x) ∧
          Branch.Poss ⟨f⟩ (fun n' =>
            ∀ a, n'.reading none (some a) = e₁ a) ∧
          Branch.Poss ⟨f⟩ (fun n' =>
            ∀ a, n'.reading none (some a) = e₂ a)) ∧
    (∀ k (f : Ladder.Level k → Ladder.Level k → Bool) e₁ e₂,
      (∃ x, e₁ x ≠ e₂ x) →
        ∃ x : Ladder.Level k,
          (Branch.childOf ⟨f⟩ e₁).reading none (some x) ≠
            (Branch.childOf ⟨f⟩ e₂).reading none (some x)) :=
  Branch.branch_package

/-! ## Summary -/

/-- Collected characterization: `theFundamental` is a fundamental; fundamentals are
    live and surjectively readable; fixed points collapse under
    generation. -/
theorem fundamental_characterized :
    IsFundamental theFundamental ∧
    (∀ {γ : Type} (act : γ → γ), IsFundamental act → Orbit.Live act) ∧
    (∀ {γ : Type} (act : γ → γ) (h : IsFundamental act) (z : γ),
      ∀ x, ∃ b, TwoCycle.reading act z b = x) ∧
    (∀ {γ : Type} (act : γ → γ), TwoCycle.Generated act →
      ∀ {z : γ}, act z = z → ∀ w, w = z) :=
  ⟨theFundamental_is_fundamental,
   fun {_γ} _act h => h.live,
   fun {_γ} act h z x =>
     TwoCycle.reading_surjective act h.exhaustive z x,
   fun {_γ} act hgen {_z} hz w =>
     Apophasis.no_static_fundamental act hgen hz w⟩

#print axioms Canon.canon_initial
#print axioms Canon.generated_of_initial_surj
#print axioms Canon.draws_of_initial_inj
#print axioms Canon.IsFundamental.exhaustive
#print axioms Canon.IsFundamental.sustains
#print axioms Canon.IsFundamental.live
#print axioms Canon.IsFundamental.lossless
#print axioms Canon.IsFundamental.involutive
#print axioms Canon.IsFundamental.iso_everywhere
#print axioms Canon.isFundamental_iff_clauses
#print axioms Canon.elimination
#print axioms Canon.canon_is_fundamental
#print axioms Canon.fundamental_correspondence
#print axioms Canon.every_fundamental_reads_as_canon
#print axioms Canon.fundamental_map_unique
#print axioms Canon.theFundamental_is_fundamental
#print axioms Canon.ofReading
#print axioms Canon.diagonal_monism_of_fundamental
#print axioms Canon.underdetermined_of_fundamental
#print axioms Canon.master_of_fundamental
#print axioms Canon.modal_of_fundamental
#print axioms Canon.fundamental_characterized

end Canon
