/-
  Spinoza, *Ethica* Pars I — counter-models for irreducibility claims.

  After the demote-attempt series (§δ through §δ-4), the project
  needed mechanical evidence that A12 and A15 are **not derivable**
  from PSR-flavoured commitments alone. Earlier marker theorems
  (`A12_full_NOT_demotable_from_PSR_alone : True := trivial` and
  the analogous A15 marker) used a Lean-as-rhetoric trick — `True`
  proves nothing about provability. Independence results
  (= "P is not derivable from axiom set Σ") are *meta-logical*
  statements about Lean and cannot be expressed as Lean theorems.

  The honest mechanical evidence is **a counter-model**: a concrete
  model that satisfies the alleged premises (e.g. `StatedAxioms` +
  `PSRSubstance`) while *falsifying* the conclusion (e.g. A12). If a
  derivation of the conclusion from the premises existed, it would
  yield `False` on this model, hence no such derivation exists.

  ## The register the counter-models instance

  The premise set is `StatedAxioms` — Spinoza's seven axioms A1–A7
  together with the Section I definitional bridges (A1ₑ, A8–A11) and
  the Section II placeholders — *without* the Section III substantive
  commitments (A12 / A13 / A14 / A15). See `Axioms.lean` for why this
  is a separate class from `Pars1Axioms`: a `Pars1Axioms` instance
  satisfies A12 by construction (A12 is one of its fields), so it can
  never falsify A12. `StatedAxioms` is exactly the register against
  which a Section III axiom can be shown non-derivable.

  These counter-models instance the full stated-axiom register, not
  merely the bare `EthicaWorld` predicate signature. An
  "attributes-as-modes" interpretation (old F2 caveat, retired
  below) would make A10 — every attribute is per se conceived,
  Spinoza Ip10 — unsatisfiable for the attribute-things. The
  all-substance interpretation used here discharges A10 and the rest
  of `StatedAxioms` honestly, so the strict claims hold over the
  full stated register, not just the predicate signature.

  This file constructs:
  * **A12 counter-model** — a `StatedAxioms` + `PSRSubstance`
    instance where two distinct substances share an attribute,
    falsifying A12 (`Pars1Axioms.ax_substanceIdByAttribute`).
  * **A15 counter-model** — a `StatedAxioms` instance where two
    `IsGod` substances exist with disjoint attributes such that
    A15 (`Pars1Axioms.ax_IsGod_has_attribute_of`) fails while
    plenitude (A25) holds. We do **not** instantiate the full
    `PSRPlenitude` class because god-uniqueness (A26) fails by
    construction; the failure of A26 is itself part of the point.

  These are the **kernel-level hard facts** for the two
  Bennett-line irreducibility results in the project.

  ## Scope of the irreducibility claims

  The strict claim for each model:

  * **A12CounterModel**: A12 (`Pars1Axioms.ax_substanceIdByAttribute`)
    is **not provable** from `[StatedAxioms T] + [PSRSubstance T]`.
    Any putative derivation would yield `s₁ = s₂` on this model,
    contradicting the model's `s₁ ≠ s₂`.
  * **A15CounterModel**: A15 is **not provable** from
    `[StatedAxioms T] + plenitude alone`. Any putative derivation
    would yield `Attribute attr_g₂ g₁` on this model, contradicting
    the falsifying clause.

  The counter-models do **not** refute derivations of A12 / A15
  from:
  - stronger PSR variants (e.g. PSR over essences, Della Rocca's
    "thoroughgoing" PSR);
  - additional Spinozistic commitments not currently axiomatised
    (e.g. "substance is fully expressible by its attributes",
    Bennett's "substance plenitude", or substance pre-conception);
  - any hypothetical augmented system that adds new typeclasses
    beyond `PSRSubstance` / `PSRPlenitude`.

  **Bennett-line scope**: Bennett 1984 §17 / §18's full claim is
  that Spinoza's Prop. V / Prop. XIV is invalid against *any*
  reasonable augmentation of his stated axioms. Demonstrating
  that full claim would require counter-models surviving every
  augmentation Della Rocca might propose — an open project for
  any Spinoza-Lean formalisation. The counter-models here are
  **first-step evidence for the Bennett line, not closing
  argument**: they refute the specific PSR-flavoured demote
  routes the project has tried, leaving stronger demote routes
  unrefuted (and inviting their construction as future demote
  attempts).

  ## Spinoza fidelity caveats

  The old F2 caveat (`inAnother := ¬ isSubstance`, treating
  attribute-things as modes) has been **retired**. It made A10
  unsatisfiable, so the previous models could not instance the
  stated-axiom register. The current models interpret every element
  as a substance (`inItself` and `perSeConceived` hold of all of
  them), with some substances serving as attributes of others. This
  is forced by the stated register itself: A10 makes every attribute
  per se conceived (Ip10) and A8 makes it in itself, so an
  attribute-thing cannot consistently be a mode. The cost is two
  remaining, milder fidelity gaps:

  1. `expressesEternalEssence _ := True` (set uniformly). Spinoza
     reserves "expresses eternal essence" for *attributes* of
     substance (Def. VI explanation; Pars II Prop. VIII). The
     uniform setting discharges `IsGod`'s fourth conjunct vacuously.

  2. The models contain **no modes** (every element is a substance),
     and a substance may be its own attribute or an attribute of
     another substance. Spinoza's intended ontology has modes, and
     attributes are essence-aspects rather than free-standing
     substances. The models are thus "Bennett-line multi-substance
     worlds" rather than Spinoza-faithful universes — which is
     appropriate: they exist precisely to exhibit configurations
     Spinoza's Prop. V / Prop. XIV would forbid.

  Neither caveat affects the meta-logical claim: the models satisfy
  `StatedAxioms` (+ `PSRSubstance`, resp. plenitude) and falsify
  A12 (resp. A15). The falsification depends only on the
  `intellectPerceivesAsEssence` graph being non-uniform. A
  scholar assessing the *philosophical* relevance of the results
  to Bennett's reading should know these gaps.

  ## Style note on `A12/A15_irreducibility_witness` definitions

  We use `∃ _ : EthicaWorld T, ∃ _ : StatedAxioms T, …` to package
  "the typeclass instances exist" inside the witness definition. The
  more idiomatic Lean form is `Nonempty (StatedAxioms T)` etc. Both
  are sound; the current form is kept because the witness `example`s
  read more naturally with the existential pattern.
-/
import Ethica.Pars1.Definitions
import Ethica.Pars1.Axioms
import Ethica.Pars1.ModalForm

namespace Ethica.Pars1.Models.Counterexamples

open Ethica.Pars1
open EthicaWorld

/-! ## Counter-model 1 — A12 not demotable from StatedAxioms + PSRSubstance

  Universe of 4 things, all of them substances: `s₁, s₂` share an
  attribute `a_shared`, plus an attribute `a_only_s1` that
  distinguishes them. Every attribute-thing is a substance (forced
  by A10 + A8) and is its own attribute, which is what
  `PSRSubstance`'s distinguishability requirement needs across the
  attribute-pairs; the shared attribute `a_shared` falsifies A12.
-/

namespace A12CounterModel

/-- Four-element universe. -/
inductive T where
  | s₁ : T
  | s₂ : T
  | a_shared : T
  | a_only_s1 : T
  deriving DecidableEq

/-- The intellect-perception graph. Since every element is a
    substance, `Attribute a x` reduces to `perceivesAsEssence x a`.
    `s₁` perceives itself, the shared attribute, and the s₁-only
    attribute; `s₂` perceives itself and the shared attribute; each
    attribute-substance perceives itself (giving it a self-attribute,
    which A22 needs to discriminate the attribute-pairs). -/
def perceivesAsEssence : T → T → Prop
  | T.s₁, T.s₁ => True
  | T.s₁, T.a_shared => True
  | T.s₁, T.a_only_s1 => True
  | T.s₂, T.s₂ => True
  | T.s₂, T.a_shared => True
  | T.a_shared, T.a_shared => True
  | T.a_only_s1, T.a_only_s1 => True
  | _, _ => False

/-- Every element is in itself and per se conceived — hence a
    substance (Def. III). No element is a mode. This is forced by the
    stated register: A10 makes every attribute per se conceived
    (Ip10) and A8 makes it in itself. -/
instance ethicaWorld : EthicaWorld T where
  inItself _ := True
  perSeConceived _ := True
  involvesExistence _ := True
  natureRequiresExistence _ := True
  inAnother _ := False
  conceivedThroughAnother _ := False
  limitedBy _ _ := False
  intellectPerceivesAsEssence := perceivesAsEssence
  absolutelyInfinite _ := True
  expressesEternalEssence _ := True
  freelyExistent _ := True
  constrained _ := False
  eternal _ := True

/-- `T` satisfies the stated-axiom register. Every field discharges
    trivially because the ontological/conceptual predicates are
    constant (`True` for the substance side, `False` for the mode
    side) and A10 holds because every element is per se conceived. -/
instance statedAxioms : StatedAxioms T where
  ax1_inItselfOrInAnother _ := Or.inl trivial
  ax1_exclusive _ h := h.2
  ax2_perSeOrThroughAnother _ := Or.inl trivial
  ax3_causationDeterminate := trivial
  ax4_effectKnowledgeFromCause := trivial
  ax5_nothingInCommonNoUnderstanding := trivial
  ax6_trueIdeaAgreesWithIdeatum := trivial
  ax7_conceivableAsNonExistent _ h := fun _ => h trivial
  ax_inItself_iff_perSeConceived _ := Iff.rfl
  ax_inAnother_iff_conceivedThroughAnother _ := Iff.rfl
  ax_attribute_perSe _ _ _ := trivial
  ax_causaSui_iff _ := Iff.rfl

/-- `T` satisfies `PSRSubstance`: distinct substances differ in some
    attribute. Every element is a substance, so all 12 distinct
    ordered pairs must be discriminated. Each `⟨witness, …⟩` provides
    the attribute one element has and the other lacks: the positive
    side is `⟨⟨trivial, trivial⟩, trivial⟩ : Attribute a x` and the
    negative side is `fun h => h.2`, where `h.2 : perceivesAsEssence
    y a` reduces to `False`. -/
instance psrSubstance : Modal.PSRSubstance T where
  ax_PSR_substance_distinguishability := by
    intro x y _ _ hne
    cases x <;> cases y
    case s₁.s₁ => exact (hne rfl).elim
    case s₁.s₂ =>
      exact ⟨T.a_only_s1, Or.inl ⟨⟨⟨trivial, trivial⟩, trivial⟩, fun h => h.2⟩⟩
    case s₁.a_shared =>
      exact ⟨T.a_only_s1, Or.inl ⟨⟨⟨trivial, trivial⟩, trivial⟩, fun h => h.2⟩⟩
    case s₁.a_only_s1 =>
      exact ⟨T.a_shared, Or.inl ⟨⟨⟨trivial, trivial⟩, trivial⟩, fun h => h.2⟩⟩
    case s₂.s₁ =>
      exact ⟨T.a_only_s1, Or.inr ⟨⟨⟨trivial, trivial⟩, trivial⟩, fun h => h.2⟩⟩
    case s₂.s₂ => exact (hne rfl).elim
    case s₂.a_shared =>
      exact ⟨T.s₂, Or.inl ⟨⟨⟨trivial, trivial⟩, trivial⟩, fun h => h.2⟩⟩
    case s₂.a_only_s1 =>
      exact ⟨T.a_shared, Or.inl ⟨⟨⟨trivial, trivial⟩, trivial⟩, fun h => h.2⟩⟩
    case a_shared.s₁ =>
      exact ⟨T.a_only_s1, Or.inr ⟨⟨⟨trivial, trivial⟩, trivial⟩, fun h => h.2⟩⟩
    case a_shared.s₂ =>
      exact ⟨T.s₂, Or.inr ⟨⟨⟨trivial, trivial⟩, trivial⟩, fun h => h.2⟩⟩
    case a_shared.a_shared => exact (hne rfl).elim
    case a_shared.a_only_s1 =>
      exact ⟨T.a_shared, Or.inl ⟨⟨⟨trivial, trivial⟩, trivial⟩, fun h => h.2⟩⟩
    case a_only_s1.s₁ =>
      exact ⟨T.a_shared, Or.inr ⟨⟨⟨trivial, trivial⟩, trivial⟩, fun h => h.2⟩⟩
    case a_only_s1.s₂ =>
      exact ⟨T.a_shared, Or.inr ⟨⟨⟨trivial, trivial⟩, trivial⟩, fun h => h.2⟩⟩
    case a_only_s1.a_shared =>
      exact ⟨T.a_shared, Or.inr ⟨⟨⟨trivial, trivial⟩, trivial⟩, fun h => h.2⟩⟩
    case a_only_s1.a_only_s1 => exact (hne rfl).elim

/-- **A12 is falsified in this model**: `T.s₁` and `T.s₂` are
    distinct substances sharing the attribute `a_shared`. -/
theorem A12_falsified :
    ∃ x y a : T, Substance x ∧ Substance y ∧
        Attribute a x ∧ Attribute a y ∧ x ≠ y :=
  ⟨T.s₁, T.s₂, T.a_shared,
   ⟨trivial, trivial⟩,
   ⟨trivial, trivial⟩,
   ⟨⟨trivial, trivial⟩, trivial⟩,
   ⟨⟨trivial, trivial⟩, trivial⟩,
   by intro h; cases h⟩

/-- **The mechanical irreducibility result for A12**: if A12 were
    derivable from `[StatedAxioms T] + [PSRSubstance T]`, it would
    yield `s₁ = s₂` on this model, contradicting the `s₁ ≠ s₂` clause
    of `A12_falsified`. Hence A12 is *not* derivable from the
    stated-axiom register plus PSR-substance-distinguishability. This
    is the **first kernel-level Bennett-line irreducibility result**
    (replacing the prior marker theorem in `ModalForm.lean` §δ).

    The argument is meta-logical (about provability), not a Lean
    theorem; this `def` records the witness data for the argument,
    namely the falsification given by `A12_falsified`. -/
def A12_irreducibility_witness : Prop :=
  ∃ _ : EthicaWorld T, ∃ _ : StatedAxioms T, ∃ _ : Modal.PSRSubstance T,
    ∃ x y a : T, Substance x ∧ Substance y ∧
      Attribute a x ∧ Attribute a y ∧ x ≠ y

example : A12_irreducibility_witness :=
  ⟨ethicaWorld, statedAxioms, psrSubstance, T.s₁, T.s₂, T.a_shared,
   ⟨trivial, trivial⟩,
   ⟨trivial, trivial⟩,
   ⟨⟨trivial, trivial⟩, trivial⟩,
   ⟨⟨trivial, trivial⟩, trivial⟩,
   by intro h; cases h⟩

end A12CounterModel

/-! ## Counter-model 2 — A15 not demotable from StatedAxioms + plenitude

  Three-element universe, all of them substances: two
  `IsGod`-satisfying substances `g₁, g₂`, each with its own
  (different) attribute, plus a third substance `attr_g₂` perceived
  as g₂'s essence but not absolutely infinite (so not a god).
  Plenitude holds (every realised attribute is in some god — its
  owner). A15 fails (g₁ does not have g₂'s attribute).

  Since A26 (god uniqueness) **fails** in this model (g₁ ≠ g₂ are
  both gods), we cannot instantiate the full `PSRPlenitude` class.
  This is the point: PSRPlenitude requires both plenitude *and*
  uniqueness, and the model demonstrates that plenitude alone is
  insufficient for A15 because uniqueness can independently fail.
-/

namespace A15CounterModel

/-- Three-element universe. -/
inductive T where
  | g₁ : T
  | g₂ : T
  | attr_g₂ : T
  deriving DecidableEq

/-- The intellect-perception graph. `g₁` has only itself as an
    attribute; `g₂` has itself and `attr_g₂`; `attr_g₂` has no
    attributes (an attribute-less substance — admissible, since A14
    is Section III and not part of `StatedAxioms`). -/
def perceivesAsEssence : T → T → Prop
  | T.g₁, T.g₁ => True
  | T.g₂, T.g₂ => True
  | T.g₂, T.attr_g₂ => True
  | _, _ => False

/-- Absolute infinity holds of `g₁` and `g₂` (the two gods) but not
    of `attr_g₂`. This keeps `attr_g₂` a substance without making it
    a god, so the falsifying clause names a genuine attribute. -/
def isAbsInfinite : T → Prop
  | T.g₁ => True
  | T.g₂ => True
  | _ => False

instance ethicaWorld : EthicaWorld T where
  inItself _ := True
  perSeConceived _ := True
  involvesExistence _ := True
  natureRequiresExistence _ := True
  inAnother _ := False
  conceivedThroughAnother _ := False
  limitedBy _ _ := False
  intellectPerceivesAsEssence := perceivesAsEssence
  absolutelyInfinite := isAbsInfinite
  expressesEternalEssence _ := True
  freelyExistent _ := True
  constrained _ := False
  eternal _ := True

/-- `T` satisfies the stated-axiom register, exactly as in the A12
    model (constant ontological predicates; A10 holds because every
    element is per se conceived). -/
instance statedAxioms : StatedAxioms T where
  ax1_inItselfOrInAnother _ := Or.inl trivial
  ax1_exclusive _ h := h.2
  ax2_perSeOrThroughAnother _ := Or.inl trivial
  ax3_causationDeterminate := trivial
  ax4_effectKnowledgeFromCause := trivial
  ax5_nothingInCommonNoUnderstanding := trivial
  ax6_trueIdeaAgreesWithIdeatum := trivial
  ax7_conceivableAsNonExistent _ h := fun _ => h trivial
  ax_inItself_iff_perSeConceived _ := Iff.rfl
  ax_inAnother_iff_conceivedThroughAnother _ := Iff.rfl
  ax_attribute_perSe _ _ _ := trivial
  ax_causaSui_iff _ := Iff.rfl

/-- Both `g₁` and `g₂` satisfy `IsGod` in this model (`absolutelyInfinite`
    holds of each). -/
theorem g₁_IsGod : IsGod T.g₁ :=
  ⟨ ⟨trivial, trivial⟩
  , trivial
  , ⟨T.g₁, ⟨⟨trivial, trivial⟩, trivial⟩⟩
  , fun _ _ => trivial ⟩

theorem g₂_IsGod : IsGod T.g₂ :=
  ⟨ ⟨trivial, trivial⟩
  , trivial
  , ⟨T.g₂, ⟨⟨trivial, trivial⟩, trivial⟩⟩
  , fun _ _ => trivial ⟩

/-- **Plenitude holds in this model**: every realised substance
    attribute is also realised in some god. The witness is the
    owning god itself. -/
theorem plenitude_holds :
    ∀ a s : T, Substance s → Attribute a s →
      ∃ g, IsGod g ∧ Attribute a g := by
  intro a s _ ha
  cases s
  case g₁ =>
    cases a
    case g₁ => exact ⟨T.g₁, g₁_IsGod, ha⟩
    case g₂ => exact ha.2.elim
    case attr_g₂ => exact ha.2.elim
  case g₂ =>
    cases a
    case g₁ => exact ha.2.elim
    case g₂ => exact ⟨T.g₂, g₂_IsGod, ha⟩
    case attr_g₂ => exact ⟨T.g₂, g₂_IsGod, ha⟩
  case attr_g₂ => exact ha.2.elim

/-- **A15 is falsified in this model**: g₁ is a god, g₂ is a
    substance with attribute `attr_g₂`, but g₁ does not have
    `attr_g₂` as an attribute. -/
theorem A15_falsified :
    ∃ g s a : T, IsGod g ∧ Substance s ∧ Attribute a s ∧
        ¬ Attribute a g :=
  ⟨T.g₁, T.g₂, T.attr_g₂,
   g₁_IsGod,
   ⟨trivial, trivial⟩,
   ⟨⟨trivial, trivial⟩, trivial⟩,
   fun h => h.2⟩

/-- **The mechanical irreducibility result for A15**: this model
    satisfies `StatedAxioms` and plenitude (A25) while falsifying
    A15. Hence A15 is *not* derivable from the stated-axiom register
    plus plenitude; the demote requires the additional god-uniqueness
    commitment (A26). This is the **second kernel-level Bennett-line
    irreducibility result**. -/
def A15_irreducibility_witness : Prop :=
  ∃ _ : EthicaWorld T, ∃ _ : StatedAxioms T,
    (∀ a s : T, Substance s → Attribute a s →
      ∃ g, IsGod g ∧ Attribute a g) ∧
    ∃ g s a : T, IsGod g ∧ Substance s ∧ Attribute a s ∧
      ¬ Attribute a g

example : A15_irreducibility_witness :=
  ⟨ethicaWorld, statedAxioms, plenitude_holds,
   T.g₁, T.g₂, T.attr_g₂,
   g₁_IsGod,
   ⟨trivial, trivial⟩,
   ⟨⟨trivial, trivial⟩, trivial⟩,
   fun h => h.2⟩

end A15CounterModel

end Ethica.Pars1.Models.Counterexamples
