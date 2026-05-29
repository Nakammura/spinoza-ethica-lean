/-
  Spinoza, *Ethica* Pars I — minimal model.

  Concrete model on `Unit` representing a "single-substance world":
  the universe contains exactly one thing, which is a self-existent
  substance (causa sui), absolutely infinite, eternal, free, and
  intelligible only through itself. No modes, no second substance.

  Purpose: this serves as a *consistency witness* for the Pars I
  axiom set — every `Pars1Axioms` and `CausalAxioms` field must hold
  on `Unit` under the chosen interpretation. If a future axiom
  addition makes the model fail to typecheck, the change has
  introduced an inconsistency relative to the single-substance
  reading and we catch it immediately.

  This model makes the typeclass layout's concrete-model checking
  concrete: it would catch the GAP-2 / A5 soundness regression
  (`¬ Cause m₁ m₂` for all mode pairs) at typecheck time.

  Caveat: `Unit` is *not* the intended model of Spinoza's God
  (which has *infinitely many* attributes). It is the smallest model
  in which all axioms are simultaneously satisfiable. The "every
  attribute expresses eternal essence" clause of Def. VI is met
  vacuously here in part, and `IsGod ()` *does* hold because the
  unique element witnesses `Attribute () ()` (so the existence
  clause is non-vacuous), but cardinality-counting (GAP-8) is
  trivially evaded.

  What this model does **not** catch
  ----------------------------------
  Every primitive predicate collapses to a constant on `Unit`
  (`True` or `False`); every binary relation has a one-element
  graph. So axiom pairs that disagree only on the *graph* of a
  relation over distinct elements (e.g. an asymmetric `Cause` that
  contradicts a reflexive `intelligibleThrough` over two distinct
  objects) are **not exercised** here. Iff axioms (A8/A9/A11) are
  discharged by `Iff.rfl` because both sides reduce to the same
  constant; so a hypothetical reversed-orientation iff would also
  go through unnoticed.

  The natural next regression test is a **two-point model** with an
  asymmetric `Cause` and distinct attributes — planned as
  `Ethica/Pars1/Models/MultiAttribute.lean` (see `coverage.md`).

  What this model does **not** validate
  -------------------------------------
  `IsGod ()` already holds in this model — the model is constructed
  precisely to make God's existence true, by interpreting the
  unique element as a self-existent absolutely-infinite substance.
  The formalisation of Prop. XI ("God necessarily exists") is
  therefore **not** validated by `Unit`. Prop. XI's content is the
  claim that `IsGod` is inhabited in *every* model satisfying
  `Pars1Axioms` (and by something not arbitrarily made-to-fit), and
  `Unit` cannot witness that universal — it is one model, not all
  models. The role of this file is consistency-witness only; do not
  read the bottom-section `example : IsGod ()` as an instance of
  Prop. XI.
-/
import Ethica.Pars1.Definitions
import Ethica.Pars1.Axioms
import Ethica.Pars1.Causation
import Ethica.Pars1.Propositions
import Ethica.Pars1.ModalForm

namespace Ethica.Pars1.Models.SingleSubstance

open Ethica.Pars1
open EthicaWorld CausalWorld

/-- The one-thing world. Every property the substance "should" have
    is `True`; every property a mode would have is `False`. -/
instance ethicaWorld : EthicaWorld Unit where
  inItself                      _   := True
  perSeConceived                _   := True
  involvesExistence             _   := True
  natureRequiresExistence       _   := True
  inAnother                     _   := False
  conceivedThroughAnother       _   := False
  limitedBy                     _ _ := False
  intellectPerceivesAsEssence   _ _ := True
  absolutelyInfinite            _   := True
  expressesEternalEssence       _   := True
  freelyExistent                _   := True
  constrained                   _   := False
  eternal                       _   := True

/-- All Pars I base axioms hold on `Unit`. -/
instance pars1Axioms : Pars1Axioms Unit where
  ax1_inItselfOrInAnother                  _ := Or.inl trivial
  ax1_exclusive                            _ h := h.2
  ax2_perSeOrThroughAnother                _ := Or.inl trivial
  ax3_causationDeterminate                   := trivial
  ax4_effectKnowledgeFromCause               := trivial
  ax5_nothingInCommonNoUnderstanding         := trivial
  ax6_trueIdeaAgreesWithIdeatum              := trivial
  ax7_conceivableAsNonExistent             _ h := fun _ => h trivial
  ax_inItself_iff_perSeConceived           _ := Iff.rfl
  ax_inAnother_iff_conceivedThroughAnother _ := Iff.rfl
  ax_attribute_perSe                       _ _ _ := trivial
  ax_causaSui_iff                          _ := Iff.rfl
  -- A12 holds vacuously on Unit: any two elements are `()`, so
  -- `s₁ = s₂` is `() = ()` which is `rfl`. The model satisfies A12
  -- but does not exercise it; `Models/TwoSubstance.lean` provides
  -- the bite-test bench.
  ax_substanceIdByAttribute                _ _ _ _ _ := rfl
  ax_substance_involves_existence          _ _ := trivial
  ax_substance_has_attribute               _ _ :=
    ⟨(), ⟨trivial, trivial⟩, trivial⟩
  ax_IsGod_has_attribute_of                _ _ _ _ _ _ :=
    ⟨⟨trivial, trivial⟩, trivial⟩

/-- Causal layer on `Unit`: the single substance is its own cause
    (causa sui) and is intelligible only through itself. -/
instance causalWorld : CausalWorld Unit where
  toEthicaWorld := ethicaWorld
  Cause _ _               := True
  intelligibleThrough _ _ := True

/-- All causal axioms hold on `Unit`. The substance-restricted A5
    fires vacuously: `sameNature () ()` holds (witnessed by `()`
    itself as a shared "attribute"), so `¬ sameNature` is false and
    the implication is empty. -/
instance causalAxioms : CausalAxioms Unit where
  toPars1Axioms := pars1Axioms
  ax4_effectIntelligibleThroughCause _ _ _ := trivial
  ax5_noCommonNoIntelligibility := by
    intro x y _ _ hno _
    -- `sameNature () ()` is True (witnessed by `()` itself, which is
    -- a shared `Attribute`), so `hno` is impossible.
    cases x; cases y
    have attr : Attribute (()) (()) := ⟨⟨trivial, trivial⟩, trivial⟩
    exact hno ⟨(), attr, attr⟩

/-- Sanity check: the unique element is a substance. -/
example : Substance () := ⟨trivial, trivial⟩

/-- Sanity check: the unique element is not a mode. -/
example : ¬ Mode () := by
  intro h
  exact h.1

/-- Sanity check: Prop. I (disjointness fragment) holds in the model. -/
example : ∀ x : Unit, Substance x → ¬ Mode x :=
  prop_1_substanceDisjointFromModes

/-- Sanity check: Prop. IV (partition) holds in the model. -/
example : ∀ x : Unit, Substance x ∨ Mode x :=
  prop_4_partition

/-- Sanity check: the unique element witnesses `IsGod`. The
    `Attribute () ()` witness unfolds to
    `Substance () ∧ intellectPerceivesAsEssence () ()`. -/
example : IsGod () :=
  let attr_witness : Attribute () () := ⟨⟨trivial, trivial⟩, trivial⟩
  ⟨ ⟨trivial, trivial⟩
  , trivial
  , ⟨(), attr_witness⟩
  , fun _ _ => trivial ⟩

/-! ## Prop. XIV in this model

  Because A14 and A15 are `Pars1Axioms` fields, the `Pars1Axioms
  Unit` instance above discharges them; `prop_14_onlyGodIsSubstance`
  therefore applies to `Unit` as a short-form theorem with no extra
  premises. -/

/-- Prop. XIV holds on `Unit`: every substance equals the unique
    god (which is the unique element). -/
example : ∀ g : Unit, IsGod g → ∀ s : Unit, Substance s → s = g :=
  fun g hgod s hs => prop_14_onlyGodIsSubstance g hgod s hs

/-! ## Modal-layer instances

  The modal layer (`Ethica/Pars1/ModalForm.lean`) is fully
  connected via four Section I bridge axioms (A18/A19/A20/A21)
  and two Section III candidate axioms (A16/A17). This block
  instantiates all six modal typeclasses on `Unit` with
  `World := Unit` (a single-world setting), exhibiting the
  **S5 modal collapse**:

  - With `World = Unit`, `∀ w : Unit, P w` is equivalent to `P ()`.
    All modal quantifiers collapse to their actual-world counterparts.
  - Necessity reduces to actuality; possibility reduces to actuality.
    This is the simplest modal model and serves as the trivial-case
    consistency witness.

  All bridge axioms (A18, A19, A20, A21) discharge to `Iff.rfl` or
  trivial calculations because both sides of each iff reduce to the
  same constant on `Unit`. The Section III candidates (A16, A17) are
  vacuously satisfied because `Unit` has no modes (every element is
  `()`, which is a substance, not a mode in our chosen
  interpretation).

  This is a **trivial-case witness**, not a non-trivial test of the
  modal-layer commitments. A non-trivial test requires a multi-world
  model — not yet implemented. -/

/-- World-relative existence on `Unit`: the unique element exists
    at every world (only one world, so this is degenerate). The
    `toEthicaWorld := inferInstance` pattern shares the base
    `EthicaWorld` instance, keeping the typeclass diamond
    coherent. -/
instance modalEthicaWorld : Modal.ModalEthicaWorld Unit Unit where
  toEthicaWorld := ethicaWorld
  existsAt _ _ := True

/-- A18 bridge holds trivially: `involvesExistence () = True` and
    `∀ w : Unit, existsAt () w = True`. Both sides reduce to
    `True`. -/
instance modalEthicaAxioms : Modal.ModalEthicaAxioms Unit Unit where
  ax_involvesExistence_iff_necExists _ := by
    constructor
    · intro _ _; trivial
    · intro _; trivial

/-- World-invariant conceptual dependence on `Unit`: the unique
    element is conceptually dependent on itself (the only option
    in a single-element universe). -/
instance conceptualStructure : Modal.ConceptualStructure Unit where
  toEthicaWorld := ethicaWorld
  conceptualDep _ _ := True

/-- A19 + A20 bridges hold trivially. For A19: `perSeConceived () =
    True`, and `∀ y : Unit, conceptualDep () y → y = ()` is `True`
    (since the only `y` is `()`). For A20: `conceivedThroughAnother
    () = False`, and `∃ y : Unit, y ≠ () ∧ ...` is `False` (no such
    `y` exists in `Unit`). -/
instance conceptualBridges : Modal.ConceptualBridges Unit where
  ax_perSe_iff_no_external_dep _ := by
    constructor
    · intro _ y _
      cases y; rfl
    · intro _; trivial
  ax_throughAnother_iff_external_dep _ := by
    constructor
    · intro h; exact h.elim
    · intro ⟨y, hne, _⟩
      cases y; exact hne rfl

/-- A16 / A17 hold vacuously on `Unit`: there are no modes (every
    element is a substance). `Mode ()` unfolds to `inAnother () ∧
    conceivedThroughAnother ()`, which is `False ∧ False = False`,
    so any `Mode _` hypothesis collapses via `.1.elim`. -/
instance conceptualDepAxioms : Modal.ConceptualDepAxioms Unit where
  ax_mode_depends_on_substance _ hm := hm.1.elim
  ax_substance_not_dep_on_mode _ _ _ hm := hm.1.elim

/-- Modal causal layer on `Unit` × `Unit`: `causeAt c e w` is
    always `True`. -/
instance modalCausalWorld : Modal.ModalCausalWorld Unit Unit where
  toModalEthicaWorld := modalEthicaWorld
  causeAt _ _ _ := True

/-- Modal causal axioms on `Unit` × `Unit`. A3 first clause:
    `causeAt → existsAt`, both `True`. A3 second clause: ¬
    (∃ c, causeAt c e w) is `False` in `Unit` (we can pick `c =
    ()`), so the implication is vacuous. A21 bridge: `Cause c e =
    True` iff `∀ w, causeAt c e w = True`, both sides `True`. -/
instance modalCausalAxioms : Modal.ModalCausalAxioms Unit Unit where
  ax3_causeNecessitatesEffect _ _ _ _ := trivial
  ax3_noCauseNoEffect _ _ h := by
    exact absurd ⟨(), trivial⟩ h
  ax_cause_iff_necCauseAt _ _ := by
    constructor
    · intro _ _; trivial
    · intro _; trivial

/-! ## S5 modal collapse witnesses

  With `World := Unit`, modal quantifiers become trivial. Below are
  small examples showing each bridge axiom discharges as expected. -/

/-- Necessary existence reduces to actual existence on `Unit`.
    Verifies A18 instance discharge. The explicit `@`-application
    pins down all type-class arguments because Lean cannot
    propagate `World := Unit` through the goal-type alone (the
    diamond inheritance from §B.1 manifests here). -/
example (s : Unit) :
    @involvesExistence Unit modalEthicaWorld.toEthicaWorld s ↔
      ∀ w : Unit,
        @Modal.ModalEthicaWorld.existsAt Unit Unit modalEthicaWorld
          s w :=
  Modal.ModalEthicaAxioms.ax_involvesExistence_iff_necExists s

/-- Necessary causation reduces to actual causation on `Unit`.
    Verifies A21 instance discharge. -/
example (c e : Unit) :
    @CausalWorld.Cause Unit causalWorld c e ↔
      ∀ w : Unit,
        @Modal.ModalCausalWorld.causeAt Unit Unit modalCausalWorld
          c e w :=
  Modal.ModalCausalAxioms.ax_cause_iff_necCauseAt c e

/-- Prop. I priority holds vacuously on `Unit` (no modes). -/
example :
    (∀ m : Unit, @Mode Unit conceptualStructure.toEthicaWorld m →
        ∃ s : Unit,
          @Substance Unit conceptualStructure.toEthicaWorld s ∧
            @Modal.ConceptualStructure.conceptualDep Unit
              conceptualStructure m s)
    ∧
    (∀ s m : Unit,
        @Substance Unit conceptualStructure.toEthicaWorld s →
        @Mode Unit conceptualStructure.toEthicaWorld m →
        ¬ @Modal.ConceptualStructure.conceptualDep Unit
            conceptualStructure s m) :=
  Modal.prop_1_priority

end Ethica.Pars1.Models.SingleSubstance
