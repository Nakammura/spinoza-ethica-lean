/-
  Spinoza, *Ethica* — Attributum: the dual-attribute witness.

  **The decisive model of the Attributum layer.** It exhibits a God
  with *two distinct attributes* — named `cogitatio` and `extensio`
  after Pars II's opening pair — while satisfying the full re-typed
  register `AttrAxioms` (A10′, A12′, A14′, A15′).

  What makes this load-bearing: `Ethica/Pars1/Realitas.lean` proves
  `god_no_two_attributes`, i.e. that *no* `Pars1Axioms` world with a
  God can have this shape. The present model is therefore the
  mechanical demonstration that the impossibility was an artefact of
  typing attributes into `Thing`, not a consequence of Spinoza's
  commitments: A12, A14 and A15 survive re-typing verbatim (as A12′,
  A14′, A15′) and, on their own, permit exactly what Def. VI and
  Pars II require.

  **The carrier is fresh.** `DualThing` is a new one-constructor type
  rather than `Unit`, following `Models/ConsecutioWitness.lean`'s
  precedent: this file owns its own instance set and cannot collide
  with any `Unit`-carried witness in `Ethica/Pars1/Models/`.

  **The legacy channel is switched off.**
  `intellectPerceivesAsEssence _ _ := False` — Pars I's `Thing`-typed
  attribution relation is uniformly empty here, so all attribution in
  this world runs through `perceivedAsEssence : DualThing → DualAttr
  → Prop`. This is not decoration: `dual_A14_thingTyped_falsified`
  below *proves* the legacy channel is empty, which is why no
  `Pars1Axioms DualThing` instance exists (A14 has no witness to
  offer) and hence why the collapse theorem has nothing to bite on.

  **Anchoring to the published register.** The model does carry a
  `StatedAxioms DualThing` instance — Spinoza's own A1–A7 plus the
  Section I bridges A1ₑ, A8–A11, i.e. the register the arXiv paper's
  irreducibility results run against. So the two-attribute God is not
  bought by abandoning Spinoza's stated axioms; it is bought by
  re-typing attributes and nothing else.
-/
import Ethica.Pars1.Definitions
import Ethica.Pars1.Axioms
import Ethica.Attributum.Core
import Ethica.Attributum.Axioms

namespace Ethica.Attributum.Models.DualAttribute

open Ethica.Pars1
open Ethica.Attributum
open Ethica.Attributum.AttrStructure

universe u

/-- The thing universe: a single substance, God. One constructor is
    enough — the interest of this model lies entirely in its
    *attribute* universe. -/
inductive DualThing where
  | deus
  deriving DecidableEq

/-- The attribute universe: exactly the two attributes Spinoza says
    we know (Pars II Props. I–II; *Ethica* II, Ax. V and the Ep. 64
    remark that the human mind knows only these two of God's
    infinitely many).

    That this type is *not* `DualThing` is the whole content of the
    Attributum layer. -/
inductive DualAttr where
  | cogitatio
  | extensio
  deriving DecidableEq

/-- The base Pars I world. Every unary predicate is at its most
    generous constant, following `Models/NoGod.lean`'s idiom, with
    one deliberate exception: `intellectPerceivesAsEssence` is
    uniformly `False`, switching off the `Thing`-typed attribution
    channel so that all attribution runs through `Attr`. -/
instance ethicaWorld : EthicaWorld DualThing where
  inItself                    _   := True
  perSeConceived              _   := True
  involvesExistence           _   := True
  natureRequiresExistence     _   := True
  inAnother                   _   := False
  conceivedThroughAnother     _   := False
  limitedBy                   _ _ := False
  -- The legacy `Thing`-typed attribution channel, deliberately empty.
  -- See `dual_A14_thingTyped_falsified` below.
  intellectPerceivesAsEssence _ _ := False
  absolutelyInfinite          _   := True
  expressesEternalEssence     _   := True
  freelyExistent              _   := True
  constrained                 _   := False
  eternal                     _   := True

/-- The re-typed attribute world. `perceivedAsEssence` is uniformly
    `True`, so *both* `cogitatio` and `extensio` are attributes of
    `deus` — the configuration `god_no_two_attributes` forbids in
    Pars I. -/
instance attrWorld : AttrWorld DualThing DualAttr where
  toEthicaWorld               := ethicaWorld
  perceivedAsEssence      _ _ := True
  perSeConceivedAttr        _ := True
  expressesEternalEssenceAttr _ := True

/-! ## The register instances -/

/-- The **stated-axiom register** holds: Spinoza's A1–A7 plus the
    Section I definitional bridges. This is the register the
    published irreducibility results (arXiv:2605.02331) run against,
    so carrying it here shows the two-attribute God costs nothing in
    Spinoza's own axioms.

    A10 (`ax_attribute_perSe`) discharges *vacuously*: its hypothesis
    is the `Thing`-typed `Attribute a s`, whose second conjunct is
    `intellectPerceivesAsEssence s a`, uniformly `False` here. The
    substantive attribute-side content is carried by A10′ in
    `attrAxioms` below. -/
instance statedAxioms : StatedAxioms DualThing where
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
  -- Vacuous: the legacy attribution channel is empty.
  ax_attribute_perSe _ _ h := h.2.elim
  ax_causaSui_iff _ := Iff.rfl

/-- The **re-typed attribute register** holds in full. Every field is
    discharged *non-vacuously* except A12′, which is non-vacuous in
    hypothesis but trivial in conclusion (the carrier has one
    element, so any two things are equal).

    A15′ in particular fires with real content: given any attribute
    of any substance, God has it — and here that is true of both
    `cogitatio` and `extensio` simultaneously. -/
instance attrAxioms : AttrAxioms DualThing DualAttr where
  ax_attributum_perSe _ _ _ := trivial
  ax_substanceIdByAttributum s₁ s₂ _ _ _ := by cases s₁; cases s₂; rfl
  ax_substance_has_attributum _ _ :=
    ⟨DualAttr.cogitatio, ⟨⟨trivial, trivial⟩, trivial⟩⟩
  ax_IsGod_has_attributum_of _ _ _ _ _ _ := ⟨⟨trivial, trivial⟩, trivial⟩

/-! ## The results -/

/-- `deus` satisfies the re-typed Def. VI. -/
theorem dual_deus_isGod : IsGodAttr (Attr := DualAttr) DualThing.deus := by
  refine ⟨⟨trivial, trivial⟩, trivial, ?_, ?_⟩
  · exact ⟨DualAttr.cogitatio, ⟨trivial, trivial⟩, trivial⟩
  · intro _ _
    exact trivial

/-- **God has two distinct attributes.** The injection
    `Fin 2 → DualAttr` sends `0 ↦ cogitatio` and `1 ↦ extensio`;
    injectivity is the constructor-disjointness of `DualAttr`.

    Compare `Ethica.Pars1.god_no_two_attributes`, which proves
    `¬ hasAtLeastNAttributes g 2` for every God in every
    `Pars1Axioms` world. Same claim, opposite verdict, and the only
    difference between the two settings is the type of the attribute
    argument. -/
theorem dual_god_two_attributes :
    hasAtLeastNAttrs (Attr := DualAttr) DualThing.deus 2 := by
  refine ⟨fun i => if i.val = 0 then DualAttr.cogitatio else DualAttr.extensio,
          ?_, ?_⟩
  · intro _
    exact ⟨⟨trivial, trivial⟩, trivial⟩
  · -- Injectivity is a finite check: `Fin 2` is decidably bounded and
    -- `DualAttr` has decidable equality, so the kernel settles it.
    decide

/-- **The headline of the Attributum layer**: a God with two distinct
    attributes, in a world satisfying `AttrAxioms` (A10′, A12′, A14′,
    A15′) and `StatedAxioms` (A1–A11).

    This is the statement that unblocks Pars II. Its Pars I analogue
    is refuted by `def6_infinitis_attributis_unsatisfiable`. -/
theorem dual_god_with_two_attributes :
    ∃ g : DualThing,
      IsGodAttr (Attr := DualAttr) g ∧ hasAtLeastNAttrs (Attr := DualAttr) g 2 :=
  ⟨DualThing.deus, dual_deus_isGod, dual_god_two_attributes⟩

/-- The legacy `Thing`-typed attribution channel really is empty:
    Pars I's A14 (`ax_substance_has_attribute`) has no witness to
    offer here.

    Consequence — and the reason this model is safe — no
    `Pars1Axioms DualThing` instance exists or could exist, so
    `Ethica.Pars1.attribute_collapse` cannot be specialised to this
    world. The collapse is not contradicted; it is left with nothing
    to apply to. -/
theorem dual_A14_thingTyped_falsified :
    ¬ (∀ s : DualThing, Substance s → ∃ a : DualThing, Attribute a s) := by
  intro h
  obtain ⟨_, ha⟩ := h DualThing.deus ⟨trivial, trivial⟩
  exact ha.2

/-! ## Sanity checks -/

/-- Sanity check: Prop. V (re-typed) applies — `deus` is the unique
    substance bearing `cogitatio`. -/
example (s : DualThing) (h : Attributum DualAttr.cogitatio s) :
    s = DualThing.deus :=
  prop_5_uniqueSubstancePerAttributum s DualThing.deus DualAttr.cogitatio h
    ⟨⟨trivial, trivial⟩, trivial⟩

/-- Sanity check: Prop. X (re-typed) applies to both attributes. -/
example : perSeConceivedAttr DualAttr.extensio :=
  prop_10_attributumPerSe DualAttr.extensio DualThing.deus
    ⟨⟨trivial, trivial⟩, trivial⟩

end Ethica.Attributum.Models.DualAttribute
