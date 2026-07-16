/-
  Spinoza, *Ethica* Pars I — kernel-level irreducibility counter-models
  for A32 (Mereology.lean) and A35 (Inherence.lean).

  Mirrors the methodology of `Models/Counterexamples.lean` and
  `Models/NoGod.lean`: independence claims ("P is not derivable from
  axiom set Σ") are meta-logical statements about Lean and cannot be
  expressed as Lean theorems directly. The honest mechanical evidence
  is a **counter-model** — a concrete model satisfying the alleged
  premises while falsifying the conclusion. If a Lean derivation of
  the conclusion from the premises existed, it would specialise to the
  counter-model and yield `False`, hence no such derivation exists.

  Both counter-models below instance the **strongest feasible baseline**
  register short of the very axiom being falsified — parity with
  `Models/NoGod.lean`'s A27 result, which runs against the *full*
  `Pars1Axioms` register rather than the weaker `StatedAxioms` register
  `Models/Counterexamples.lean` uses for A12/A15. The stronger the
  register a counter-model satisfies, the stronger the irreducibility
  claim: it shows the falsified axiom is not even a *consequence* of
  every other Section III commitment already made elsewhere in the
  project.

  ## Model 1 — `ModeParts` falsifies A32

  Philosophical reading: the *parts-as-modes* reading of extended
  substance. In Letter 12 (to Meyer) Spinoza distinguishes quantity
  conceived abstractly (as divisible, having parts) from quantity as
  substance (indivisible); commentators (Curley) read the "parts" of
  extension as modes, not rival substances. `ModeParts` embodies that
  reading directly: a substance (`whole`) whose only proper part
  (`part`) is a *mode*, not a rival substance. The model satisfies the
  full register `Pars1Axioms + CausalAxioms + TheologiaAxioms +
  InherenceAxioms` while falsifying A32
  (`MereologyAxioms.ax_substancePart_sameNatureSubstance`) — showing
  that A32 (a proper part of a substance would be a same-nature rival
  substance, horn (i) of Prop. XII's dilemma) is a genuine
  *interpretive choice*, not forced by any other commitment the
  formalisation has made.

  ## Model 2 — `NecessaryMode` falsifies A35

  Philosophical reading: a *necessarily-existing mode* — precisely the
  profile Spinoza himself assigns to the infinite modes (Props.
  XXI–XXIII: modes that "necessario et infinita existunt"), except
  with the necessity lodged in the mode's own essence rather than in
  its cause. A35 (= Prop. XXIV: produced things' essence does not
  involve existence) is exactly what rules this configuration out; the
  model shows nothing *else* in the register rules it out. The
  distinction A35 enforces — existing necessarily *through one's
  cause* versus *through one's own essence* — is invisible to
  `Pars1Axioms + CausalAxioms + TheologiaAxioms` plus the other three
  `InherenceAxioms` fields (A33, A34, A36).

  ## Deviation from the literal design brief (flagged)

  The design brief specifies `intellectPerceivesAsEssence s _ := (s =
  <substance>)`, i.e. a perception relation depending only on the
  substance argument. Taken literally this makes the substance
  perceive *every* element of the carrier (including the mode) as its
  essence, so `Attribute <mode> <substance>` would hold — which then
  breaks A10 (`Pars1Axioms.ax_attribute_perSe`: every attribute of a
  substance is per se conceived), since the mode is *not* per se
  conceived. Both models below instead use
  `intellectPerceivesAsEssence s a := (s = <substance> ∧ a =
  <substance>)` — the substance perceives *only itself* as its
  essence. This is the conservative fix the task brief anticipates
  ("adjust the model's field values conservatively"): it keeps "only
  the substance has attributes" (the intended reading) while making
  A10, A12, A14, A15, A29 all honestly dischargeable. No falsification
  theorem or baseline instance is weakened by this change.
-/
import Ethica.Pars1.Definitions
import Ethica.Pars1.Axioms
import Ethica.Pars1.Causation
import Ethica.Pars1.Theologia
import Ethica.Pars1.Mereology
import Ethica.Pars1.Inherence

namespace Ethica.Pars1.Models.CounterexamplesII

open Ethica.Pars1
open EthicaWorld CausalWorld InherenceWorld MereologyWorld

/-! ## Model 1 — `ModeParts` (falsifies A32) -/

/-- Two-element universe: `whole` (the substance) and `part` (its sole
    proper part, interpreted as a *mode* rather than a rival
    substance). -/
inductive ModeParts where
  | whole : ModeParts
  | part : ModeParts
  deriving DecidableEq

/-- `whole` is a full substance-God profile (in itself, per se
    conceived, causa sui, absolutely infinite, unconstrained,
    eternal); `part` is a genuine mode (in another, conceived through
    another, constrained, not causa sui) — never a substance. -/
instance modeParts_ethicaWorld : EthicaWorld ModeParts where
  inItself
    | .whole => True
    | .part => False
  perSeConceived
    | .whole => True
    | .part => False
  involvesExistence
    | .whole => True
    | .part => False
  natureRequiresExistence
    | .whole => True
    | .part => False
  inAnother
    | .whole => False
    | .part => True
  conceivedThroughAnother
    | .whole => False
    | .part => True
  limitedBy _ _ := False
  -- `whole` perceives only itself as its essence — see the file-level
  -- "Deviation" note above for why the second conjunct is needed.
  intellectPerceivesAsEssence s a := (s = ModeParts.whole ∧ a = ModeParts.whole)
  absolutelyInfinite
    | .whole => True
    | .part => False
  expressesEternalEssence _ := True
  freelyExistent _ := True
  constrained
    | .whole => False
    | .part => True
  eternal _ := True

/-- `part` is a mode: in another and conceived through another. -/
theorem modeParts_partIsMode : Mode ModeParts.part := ⟨trivial, trivial⟩

/-- `part` is not a substance. -/
theorem modeParts_partNotSubstance : ¬ Substance ModeParts.part := fun h => h.1

/-- The full `Pars1Axioms` register (A1–A15) holds on `ModeParts`.
    `whole` is the unique substance and the unique attribute-bearer
    (of itself); every field discharges by forcing the relevant
    element to be `whole`, or vacuously via `part`'s failed `Substance`
    / `Mode`-side hypotheses. -/
instance modeParts_pars1Axioms : Pars1Axioms ModeParts where
  ax1_inItselfOrInAnother x := by
    cases x with
    | whole => exact Or.inl trivial
    | part => exact Or.inr trivial
  ax1_exclusive x := by
    cases x with
    | whole => exact fun h => h.2
    | part => exact fun h => h.1
  ax2_perSeOrThroughAnother x := by
    cases x with
    | whole => exact Or.inl trivial
    | part => exact Or.inr trivial
  ax3_causationDeterminate := trivial
  ax4_effectKnowledgeFromCause := trivial
  ax5_nothingInCommonNoUnderstanding := trivial
  ax6_trueIdeaAgreesWithIdeatum := trivial
  ax7_conceivableAsNonExistent x := by
    cases x with
    | whole => exact fun h => absurd trivial h
    | part => exact fun _ h => h
  ax_inItself_iff_perSeConceived x := by cases x <;> exact Iff.rfl
  ax_inAnother_iff_conceivedThroughAnother x := by cases x <;> exact Iff.rfl
  ax_attribute_perSe := by
    intro a s h
    obtain ⟨_, _, hAeq⟩ := h
    subst hAeq
    trivial
  ax_causaSui_iff x := by cases x <;> exact Iff.rfl
  -- A12: forced from the shared attribute that both `s1` and `s2`
  -- carry — the attribute relation forces the substance argument to
  -- equal `whole` in both cases.
  ax_substanceIdByAttribute := by
    intro s1 s2 a h1 h2
    obtain ⟨_, hS1, _⟩ := h1
    obtain ⟨_, hS2, _⟩ := h2
    exact hS1.trans hS2.symm
  -- A15: any `IsGod g` forces `g = whole` (only `whole` is absolutely
  -- infinite); any `Attribute a s` forces `a = whole`; so the
  -- conclusion `Attribute a g` reduces to `Attribute whole whole`.
  ax_IsGod_has_attribute_of := by
    intro g s a hgod _hs ha
    obtain ⟨_, _, hAeq⟩ := ha
    subst hAeq
    obtain ⟨_, hAbsInf, _, _⟩ := hgod
    have hgw : g = ModeParts.whole := by
      cases g with
      | whole => rfl
      | part => exact hAbsInf.elim
    subst hgw
    exact ⟨⟨trivial, trivial⟩, rfl, rfl⟩
  ax_substance_has_attribute := by
    intro s hs
    cases s with
    | whole => exact ⟨ModeParts.whole, ⟨trivial, trivial⟩, rfl, rfl⟩
    | part => exact hs.1.elim
  ax_substance_involves_existence := by
    intro s hs
    cases s with
    | whole => trivial
    | part => exact hs.1.elim

/-- `Cause c e` : `whole` causes `part`. `intelligibleThrough x y` :
    `part` is intelligible through `whole` — the effect-through-cause
    direction A4 needs. -/
instance modeParts_causalWorld : CausalWorld ModeParts where
  toEthicaWorld := modeParts_ethicaWorld
  Cause c e := (c = ModeParts.whole ∧ e = ModeParts.part)
  intelligibleThrough x y := (x = ModeParts.part ∧ y = ModeParts.whole)

/-- A4–A5 (causal layer) hold on `ModeParts`. A5's substance-substance
    case is vacuous: the only substance is `whole`, and `whole` shares
    its own attribute with itself, so `¬ sameNature x y` is never
    satisfiable once `x = y = whole` is forced. -/
instance modeParts_causalAxioms : CausalAxioms ModeParts where
  toPars1Axioms := modeParts_pars1Axioms
  ax4_effectIntelligibleThroughCause := by
    intro c e h
    obtain ⟨hc, he⟩ := h
    subst hc
    subst he
    exact ⟨rfl, rfl⟩
  ax5_noCommonNoIntelligibility := by
    intro x y hx hy hno
    exfalso
    apply hno
    have hxw : x = ModeParts.whole := by
      cases x with
      | whole => rfl
      | part => exact hx.1.elim
    have hyw : y = ModeParts.whole := by
      cases y with
      | whole => rfl
      | part => exact hy.1.elim
    subst hxw
    subst hyw
    exact ⟨ModeParts.whole, ⟨⟨trivial, trivial⟩, rfl, rfl⟩, ⟨⟨trivial, trivial⟩, rfl, rfl⟩⟩

/-- `inheresIn x y` : `part` inheres in `whole`. -/
instance modeParts_inherenceWorld : InherenceWorld ModeParts where
  toCausalWorld := modeParts_causalWorld
  inheresIn x y := (x = ModeParts.part ∧ y = ModeParts.whole)

/-- A33–A36 (inherence layer) hold on `ModeParts`: `part` is the only
    mode, it inheres in `whole` (A33), inherence tracks the causal
    direction already fixed by `modeParts_causalWorld` (A34), `part`
    does not involve existence (A35 — a genuine mode here, unlike
    `NecessaryMode.m` below), and `part` is constrained (A36). -/
instance modeParts_inherenceAxioms : InherenceAxioms ModeParts where
  toCausalAxioms := modeParts_causalAxioms
  ax_mode_inheres_in_substance := by
    intro x hx
    cases x with
    | whole => exact hx.1.elim
    | part => exact ⟨ModeParts.whole, ⟨trivial, trivial⟩, rfl, rfl⟩
  ax_inherence_causation := by
    intro x y h
    obtain ⟨hx, hy⟩ := h
    subst hx
    subst hy
    exact ⟨rfl, rfl⟩
  ax_mode_not_involvesExistence := by
    intro x hx
    cases x with
    | whole => exact hx.1.elim
    | part => exact fun h => h
  ax_mode_constrained := by
    intro x hx
    cases x with
    | whole => exact hx.1.elim
    | part => trivial

/-- A27–A31 (theological layer) hold on `ModeParts`: `whole` is God
    (A27); eternity is set uniformly so A28 is trivial; A29 forces the
    attribute argument to be `whole` itself; A30/A31 discharge on
    `whole` directly and vacuously on `part` (not a substance). -/
instance modeParts_theologiaAxioms : TheologiaAxioms ModeParts where
  toPars1Axioms := modeParts_pars1Axioms
  ax_god_exists :=
    ⟨ModeParts.whole, ⟨trivial, trivial⟩, trivial,
      ⟨ModeParts.whole, ⟨trivial, trivial⟩, rfl, rfl⟩,
      fun _ _ => trivial⟩
  ax_natureRequiresExistence_eternal _ _ := trivial
  ax_attribute_involvesExistence := by
    intro a s h
    obtain ⟨_, _, hAeq⟩ := h
    subst hAeq
    trivial
  ax_causaSui_unconstrained_free := by
    intro x _ hnc
    cases x with
    | whole => trivial
    | part => exact (hnc trivial).elim
  ax_substance_not_constrained := by
    intro s hs
    cases s with
    | whole => exact fun h => h
    | part => exact hs.1.elim

/-- `properPart p x` : `part` is the sole proper part of `whole`. No
    `MereologyAxioms ModeParts` instance is built — instantiating it
    would *prove* A32 holds here, which is exactly what
    `A32_falsified` below shows cannot be done. -/
instance modeParts_mereologyWorld : MereologyWorld ModeParts where
  toEthicaWorld := modeParts_ethicaWorld
  properPart p x := (p = ModeParts.part ∧ x = ModeParts.whole)

/-- **A32 is falsified in this model**: `whole` is a substance with
    proper part `part`, but `part` is not itself a substance — so the
    conclusion of A32
    (`Substance p ∧ sameNature p s ∧ p ≠ s`) fails on its first
    conjunct. -/
theorem A32_falsified :
    ¬ (∀ s p : ModeParts, Substance s → properPart p s →
        Substance p ∧ sameNature p s ∧ p ≠ s) := by
  intro h
  have hres := h ModeParts.whole ModeParts.part ⟨trivial, trivial⟩ ⟨rfl, rfl⟩
  exact modeParts_partNotSubstance hres.1

/-! **The mechanical irreducibility result for A32**: `ModeParts`
    satisfies the full register `Pars1Axioms + CausalAxioms +
    TheologiaAxioms + InherenceAxioms` (instances
    `modeParts_pars1Axioms`, `modeParts_causalAxioms`,
    `modeParts_theologiaAxioms`, `modeParts_inherenceAxioms` above)
    while falsifying A32 (`A32_falsified`). Any Lean derivation of A32
    from that register would specialise to `ModeParts`, yielding
    `False` via `A32_falsified` — contradiction. Hence A32 is *not*
    derivable from that register: Prop. XII/XIII's indivisibility
    genuinely requires the Section III commitment A32. The
    parts-as-rival-substances horn (i) of Spinoza's dilemma is an
    interpretive *choice* against the live parts-as-modes alternative
    this model embodies, not something forced by the rest of the
    formalisation — including the causal and inherence machinery A32
    was not previously tested against. -/

/-! ## Model 2 — `NecessaryMode` (falsifies A35) -/

/-- Two-element universe: `g` (a substance-God profile) and `m` (a
    mode whose essence involves existence — the load-bearing choice
    that makes this model an infinite-mode-style counter-example to
    A35). -/
inductive NecessaryMode where
  | g : NecessaryMode
  | m : NecessaryMode
  deriving DecidableEq

/-- `g` is a full substance-God profile, exactly as `ModeParts.whole`.
    `m` is in another and conceived through another (a genuine mode,
    Def. V), constrained, yet — the load-bearing choice —
    `involvesExistence` and `natureRequiresExistence` both hold of
    `m`: its existence is necessary through its *own* essence, not
    merely through its cause. -/
instance necessaryMode_ethicaWorld : EthicaWorld NecessaryMode where
  inItself
    | .g => True
    | .m => False
  perSeConceived
    | .g => True
    | .m => False
  -- Load-bearing choice: both `g` and `m` involve/require existence.
  involvesExistence _ := True
  natureRequiresExistence _ := True
  inAnother
    | .g => False
    | .m => True
  conceivedThroughAnother
    | .g => False
    | .m => True
  limitedBy _ _ := False
  intellectPerceivesAsEssence s a := (s = NecessaryMode.g ∧ a = NecessaryMode.g)
  absolutelyInfinite
    | .g => True
    | .m => False
  expressesEternalEssence _ := True
  freelyExistent _ := True
  constrained
    | .g => False
    | .m => True
  eternal _ := True

/-- The full `Pars1Axioms` register (A1–A15) holds on `NecessaryMode`.
    A7's hypothesis `¬ natureRequiresExistence x` is always `¬ True`,
    so A7 discharges vacuously for both elements — the same idiom used
    in `Models/NoGod.lean`. -/
instance necessaryMode_pars1Axioms : Pars1Axioms NecessaryMode where
  ax1_inItselfOrInAnother x := by
    cases x with
    | g => exact Or.inl trivial
    | m => exact Or.inr trivial
  ax1_exclusive x := by
    cases x with
    | g => exact fun h => h.2
    | m => exact fun h => h.1
  ax2_perSeOrThroughAnother x := by
    cases x with
    | g => exact Or.inl trivial
    | m => exact Or.inr trivial
  ax3_causationDeterminate := trivial
  ax4_effectKnowledgeFromCause := trivial
  ax5_nothingInCommonNoUnderstanding := trivial
  ax6_trueIdeaAgreesWithIdeatum := trivial
  ax7_conceivableAsNonExistent _ h := fun _ => h trivial
  ax_inItself_iff_perSeConceived x := by cases x <;> exact Iff.rfl
  ax_inAnother_iff_conceivedThroughAnother x := by cases x <;> exact Iff.rfl
  ax_attribute_perSe := by
    intro a s h
    obtain ⟨_, _, hAeq⟩ := h
    subst hAeq
    trivial
  ax_causaSui_iff _ := Iff.rfl
  ax_substanceIdByAttribute := by
    intro s1 s2 a h1 h2
    obtain ⟨_, hS1, _⟩ := h1
    obtain ⟨_, hS2, _⟩ := h2
    exact hS1.trans hS2.symm
  ax_IsGod_has_attribute_of := by
    intro gg s a hgod _hs ha
    obtain ⟨_, _, hAeq⟩ := ha
    subst hAeq
    obtain ⟨_, hAbsInf, _, _⟩ := hgod
    have hgg : gg = NecessaryMode.g := by
      cases gg with
      | g => rfl
      | m => exact hAbsInf.elim
    subst hgg
    exact ⟨⟨trivial, trivial⟩, rfl, rfl⟩
  ax_substance_has_attribute := by
    intro s hs
    cases s with
    | g => exact ⟨NecessaryMode.g, ⟨trivial, trivial⟩, rfl, rfl⟩
    | m => exact hs.1.elim
  ax_substance_involves_existence := by
    intro s hs
    cases s with
    | g => trivial
    | m => exact hs.1.elim

/-- `Cause c e` : `g` causes `m`. `intelligibleThrough x y` : `m` is
    intelligible through `g`. -/
instance necessaryMode_causalWorld : CausalWorld NecessaryMode where
  toEthicaWorld := necessaryMode_ethicaWorld
  Cause c e := (c = NecessaryMode.g ∧ e = NecessaryMode.m)
  intelligibleThrough x y := (x = NecessaryMode.m ∧ y = NecessaryMode.g)

/-- A4–A5 (causal layer) hold on `NecessaryMode`, exactly mirroring
    `modeParts_causalAxioms`'s argument: the only substance is `g`, so
    A5's substance-substance case is vacuous. -/
instance necessaryMode_causalAxioms : CausalAxioms NecessaryMode where
  toPars1Axioms := necessaryMode_pars1Axioms
  ax4_effectIntelligibleThroughCause := by
    intro c e h
    obtain ⟨hc, he⟩ := h
    subst hc
    subst he
    exact ⟨rfl, rfl⟩
  ax5_noCommonNoIntelligibility := by
    intro x y hx hy hno
    exfalso
    apply hno
    have hxg : x = NecessaryMode.g := by
      cases x with
      | g => rfl
      | m => exact hx.1.elim
    have hyg : y = NecessaryMode.g := by
      cases y with
      | g => rfl
      | m => exact hy.1.elim
    subst hxg
    subst hyg
    exact ⟨NecessaryMode.g, ⟨⟨trivial, trivial⟩, rfl, rfl⟩, ⟨⟨trivial, trivial⟩, rfl, rfl⟩⟩

/-- `inheresIn x y` : `m` inheres in `g`. No `InherenceAxioms
    NecessaryMode` instance is built — A35 is a *field* of
    `InherenceAxioms`, so instantiating the class would prove A35
    holds here, contradicting `A35_falsified` below. The other three
    inherence-layer fields (A33, A34, A36) are proved as standalone
    theorems instead, showing they hold independently of A35. -/
instance necessaryMode_inherenceWorld : InherenceWorld NecessaryMode where
  toCausalWorld := necessaryMode_causalWorld
  inheresIn x y := (x = NecessaryMode.m ∧ y = NecessaryMode.g)

/-- A27–A31 (theological layer) hold on `NecessaryMode`, mirroring
    `modeParts_theologiaAxioms`. -/
instance necessaryMode_theologiaAxioms : TheologiaAxioms NecessaryMode where
  toPars1Axioms := necessaryMode_pars1Axioms
  ax_god_exists :=
    ⟨NecessaryMode.g, ⟨trivial, trivial⟩, trivial,
      ⟨NecessaryMode.g, ⟨trivial, trivial⟩, rfl, rfl⟩,
      fun _ _ => trivial⟩
  ax_natureRequiresExistence_eternal _ _ := trivial
  ax_attribute_involvesExistence := by
    intro a s h
    obtain ⟨_, _, hAeq⟩ := h
    subst hAeq
    trivial
  ax_causaSui_unconstrained_free := by
    intro x _ hnc
    cases x with
    | g => trivial
    | m => exact (hnc trivial).elim
  ax_substance_not_constrained := by
    intro s hs
    cases s with
    | g => exact fun h => h
    | m => exact hs.1.elim

/-- A33 (mode inheres in some substance): `m` is the only mode; it
    inheres in `g`. -/
theorem necessaryMode_satisfies_A33 :
    ∀ x : NecessaryMode, Mode x → ∃ s, Substance s ∧ inheresIn x s := by
  intro x hx
  cases x with
  | g => exact hx.1.elim
  | m => exact ⟨NecessaryMode.g, ⟨trivial, trivial⟩, rfl, rfl⟩

/-- A34 (inherence entails causation): tracks
    `necessaryMode_causalWorld`'s `Cause` relation directly. -/
theorem necessaryMode_satisfies_A34 :
    ∀ x y : NecessaryMode, inheresIn x y → Cause y x := by
  intro x y h
  obtain ⟨hx, hy⟩ := h
  subst hx
  subst hy
  exact ⟨rfl, rfl⟩

/-- A36 (every mode is constrained): `m` is constrained by
    construction. -/
theorem necessaryMode_satisfies_A36 :
    ∀ x : NecessaryMode, Mode x → constrained x := by
  intro x hx
  cases x with
  | g => exact hx.1.elim
  | m => trivial

/-- **A35 is falsified in this model**: `m` is a mode, yet
    `involvesExistence m` holds — the necessary-mode profile A35
    rules out. -/
theorem A35_falsified :
    ¬ (∀ x : NecessaryMode, Mode x → ¬ involvesExistence x) := by
  intro h
  exact h NecessaryMode.m ⟨trivial, trivial⟩ trivial

/-! **The mechanical irreducibility result for A35**: `NecessaryMode`
    satisfies the register `Pars1Axioms + CausalAxioms +
    TheologiaAxioms` in full (instances `necessaryMode_pars1Axioms`,
    `necessaryMode_causalAxioms`, `necessaryMode_theologiaAxioms`
    above) together with the *other three* `InherenceAxioms` fields —
    A33 (`necessaryMode_satisfies_A33`), A34
    (`necessaryMode_satisfies_A34`), and A36
    (`necessaryMode_satisfies_A36`) — while falsifying A35
    (`A35_falsified`). Any Lean derivation of A35 from that register
    would specialise to `NecessaryMode`, yielding `False` via
    `A35_falsified` — contradiction. Hence A35 is *not* derivable from
    that register: Prop. XXIV is a genuine Section III commitment.
    This is machine-checked confirmation that Spinoza's "patet ex
    definitione 1" *demonstratio* conceals a substantive premise
    (produced-by-another → essence does not involve existence), which
    the stated axioms run only in the opposite direction — A7
    (`Pars1Axioms.ax7_conceivableAsNonExistent`) derives *non*-necessity
    of existence from *non*-necessity of nature, not the reverse
    implication A35's contrapositive would need. -/

end Ethica.Pars1.Models.CounterexamplesII
