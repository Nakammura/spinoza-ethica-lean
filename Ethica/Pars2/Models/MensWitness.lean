/-
  Spinoza, *Ethica* Pars II — consistency witness for the idea layer.

  Carries a full `Pars2Axioms` instance: `Pars1Axioms` (A1–A15) +
  `CausalAxioms` (A4ₛ, A5ₛ) + `AttrAxioms` (A10′/A12′/A14′/A15′) +
  the six new Pars II commitments A45–A50, all on one carrier. So
  the idea layer introduces no contradiction, and Props. II.I, II.II,
  II.III and II.VII are not vacuously true by explosion.

  **The interesting part of this model is that it holds both
  verdicts at once.** In this single world:

  - `mens_pars1_collapse_holds` — no God has two `Thing`-typed
    attributes. This is `Ethica.Pars1.god_no_two_attributes` applied
    here, and it holds because `Pars1Axioms` genuinely holds.
  - `mens_duo_attributa` — God *does* have two `Attr`-typed
    attributes, `cogitatio` and `extensio`.

  There is no tension: the `Thing`-typed attribution channel is
  degenerate exactly as the collapse theorem forces
  (`god_is_own_only_attribute` — God is its own only `Thing`-typed
  attribute), while the load-bearing attribute structure lives in
  `MensAttr`. This is what the note in `Pars2Axioms`' docstring
  asserts, verified.

  The carrier is a fresh one-constructor type, per
  `Models/ConsecutioWitness.lean`'s precedent, so this file owns its
  own instance set.
-/
import Ethica.Pars1.Definitions
import Ethica.Pars1.Axioms
import Ethica.Pars1.Causation
import Ethica.Pars1.Realitas
import Ethica.Attributum.Core
import Ethica.Attributum.Axioms
import Ethica.Pars2.Idea

namespace Ethica.Pars2.Models.MensWitness

open Ethica.Pars1
open Ethica.Attributum
open Ethica.Pars2

universe u

/-- The thing universe: one substance, God. Ideas are things, so
    `deus` is also (trivially) the idea of everything — enough to
    discharge A49 non-vacuously. -/
inductive MensThing where
  | deus
  deriving DecidableEq

/-- The attribute universe: the two attributes Spinoza names. Unlike
    `MensThing` this type has **two** elements, which is the whole
    point. -/
inductive MensAttr where
  | cogitatio
  | extensio
  deriving DecidableEq

/-- The base Pars I world. Every predicate at its most generous
    constant.

    Note that unlike `Ethica/Attributum/Models/DualAttribute.lean`,
    here `intellectPerceivesAsEssence` is `True`, **not** `False`:
    this model deliberately satisfies the *full* `Pars1Axioms`
    register (A14 needs a `Thing`-typed attribute to exist), so that
    the coexistence claim below is a claim about a genuine
    `Pars1Axioms` world. -/
instance ethicaWorld : EthicaWorld MensThing where
  inItself                    _   := True
  perSeConceived              _   := True
  involvesExistence           _   := True
  natureRequiresExistence     _   := True
  inAnother                   _   := False
  conceivedThroughAnother     _   := False
  limitedBy                   _ _ := False
  intellectPerceivesAsEssence _ _ := True
  absolutelyInfinite          _   := True
  expressesEternalEssence     _   := True
  freelyExistent              _   := True
  constrained                 _   := False
  eternal                     _   := True

/-- The Pars II world: attribute channel, causal channel, ideas, and
    the two named attributes. -/
instance pars2World : Pars2World MensThing MensAttr where
  toEthicaWorld               := ethicaWorld
  perceivedAsEssence      _ _ := True
  perSeConceivedAttr        _ := True
  expressesEternalEssenceAttr _ := True
  Cause                   _ _ := True
  intelligibleThrough     _ _ := True
  ideaOf                  _ _ := True
  cogitatio                   := MensAttr.cogitatio
  extensio                    := MensAttr.extensio

/-- The full register: A1–A15, A4ₛ/A5ₛ, A10′–A15′, A45–A50.

    Discharge notes. A5ₛ is vacuous (`sameNature deus deus` holds via
    the `Thing`-typed attribute channel, so its `¬ sameNature`
    hypothesis is false). A45 is vacuous in the degenerate sense that
    the carrier has one element. Everything else fires
    non-vacuously — in particular A46/A47 produce genuine
    `Attributum` witnesses for two *distinct* attributes, and A48 is
    a real constructor disequality. -/
instance pars2Axioms : Pars2Axioms MensThing MensAttr where
  -- Pars1Axioms (A1–A15)
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
  ax_substanceIdByAttribute s₁ s₂ _ _ _ := by cases s₁; cases s₂; rfl
  ax_substance_has_attribute _ _ := ⟨MensThing.deus, ⟨trivial, trivial⟩, trivial⟩
  ax_IsGod_has_attribute_of _ _ _ _ _ _ := ⟨⟨trivial, trivial⟩, trivial⟩
  ax_substance_involves_existence _ _ := trivial
  -- CausalAxioms (A4ₛ, A5ₛ)
  ax4_effectIntelligibleThroughCause _ _ _ := trivial
  ax5_noCommonNoIntelligibility _ _ _ _ hns :=
    absurd ⟨MensThing.deus, ⟨⟨trivial, trivial⟩, trivial⟩,
            ⟨⟨trivial, trivial⟩, trivial⟩⟩ hns
  -- AttrAxioms (A10′, A12′, A14′, A15′)
  ax_attributum_perSe _ _ _ := trivial
  ax_substanceIdByAttributum s₁ s₂ _ _ _ := by cases s₁; cases s₂; rfl
  ax_substance_has_attributum _ _ :=
    ⟨MensAttr.cogitatio, ⟨⟨trivial, trivial⟩, trivial⟩⟩
  ax_IsGod_has_attributum_of _ _ _ _ _ _ := ⟨⟨trivial, trivial⟩, trivial⟩
  -- Pars II (A45–A50)
  ax6_idea_unique_ideatum _ x y _ _ := by cases x; cases y; rfl
  ax_cogitatio_attributum _ _ := ⟨⟨trivial, trivial⟩, trivial⟩
  ax_extensio_attributum _ _ := ⟨⟨trivial, trivial⟩, trivial⟩
  ax_cogitatio_ne_extensio := by decide
  ax_god_has_idea_of_all _ := ⟨MensThing.deus, trivial⟩
  ax_idea_tracks_intelligibility _ _ _ _ _ _ _ := trivial

/-! ## The results -/

/-- `deus` is God, in the re-typed sense. -/
theorem mens_deus_isGod : IsGodAttr (Attr := MensAttr) MensThing.deus := by
  refine ⟨⟨trivial, trivial⟩, trivial, ?_, ?_⟩
  · exact ⟨MensAttr.cogitatio, ⟨trivial, trivial⟩, trivial⟩
  · intro _ _
    exact trivial

/-- **Props. II.I and II.II hold together**: God has two distinct
    attributes here, via `prop_2_1_2_deusHabetDuoAttributa`. -/
theorem mens_duo_attributa :
    hasAtLeastNAttrs (Attr := MensAttr) MensThing.deus 2 :=
  prop_2_1_2_deusHabetDuoAttributa MensThing.deus mens_deus_isGod

/-- `deus` is also God in Pars I's sense — this model satisfies the
    full `Pars1Axioms` register, so Pars I's theorems apply to it. -/
theorem mens_deus_isGod_pars1 : IsGod MensThing.deus :=
  ⟨⟨trivial, trivial⟩, trivial,
   ⟨MensThing.deus, ⟨trivial, trivial⟩, trivial⟩, fun _ _ => trivial⟩

/-- **And Pars I's collapse still holds, in the same world.** No God
    here has two `Thing`-typed attributes — `god_no_two_attributes`
    applies, because `Pars1Axioms` genuinely holds.

    Read together with `mens_duo_attributa`, this is the coexistence
    claim: the two attribution channels live side by side, the
    `Thing`-typed one degenerate exactly as the collapse theorem
    forces, the `Attr`-typed one carrying Pars II's structure. -/
theorem mens_pars1_collapse_holds :
    ¬ hasAtLeastNAttributes MensThing.deus 2 :=
  god_no_two_attributes MensThing.deus mens_deus_isGod_pars1

/-- The coexistence, in one statement. -/
theorem mens_coexistence :
    hasAtLeastNAttrs (Attr := MensAttr) MensThing.deus 2 ∧
      ¬ hasAtLeastNAttributes MensThing.deus 2 :=
  ⟨mens_duo_attributa, mens_pars1_collapse_holds⟩

/-! ## Sanity checks -/

/-- Sanity check: Prop. II.III applies — everything has an idea. -/
example (x : MensThing) : ∃ i : MensThing, Pars2World.ideaOf i x :=
  prop_2_3_ideaOmnium (Attr := MensAttr) x

/-- Sanity check: Prop. II.VII (the parallelism) applies. -/
example (c e : MensThing) (h : Pars2World.Cause c e) :
    ∃ ic ie : MensThing,
      Pars2World.ideaOf ic c ∧ Pars2World.ideaOf ie e ∧ Pars2World.Cause ic ie :=
  prop_2_7_cor_ideaePariter (Attr := MensAttr) c e h

/-- Sanity check: Prop. I.XIV still applies — `deus` is the only
    substance. The Pars I layer is entirely intact under this
    model. -/
example (s : MensThing) (hs : Substance s) : s = MensThing.deus :=
  prop_14_onlyGodIsSubstance MensThing.deus mens_deus_isGod_pars1 s hs

end Ethica.Pars2.Models.MensWitness
