/-
  Spinoza, *Ethica* — Attributum: Def. VI recovered.

  `Models/DualAttribute.lean` shows a God with *two* attributes. This
  file goes to the end of the line: a God with **infinitely many**,
  which is what Def. VI actually says —

    *Per Deum intelligo ens absolute infinitum, hoc est substantiam
     constantem infinitis attributis, quorum unumquodque aeternam et
     infinitam essentiam exprimit.*

  **What this closes.** GAP-8a asked for a counting framework capable
  of expressing "*infinitis attributis*". `Ethica/Pars1/Realitas.lean`
  supplied the framework (`hasAtLeastNAttributes`,
  `HasInfiniteAttributes`) and then immediately proved the clause
  *unsatisfiable* of any God in the Pars I register
  (`def6_infinitis_attributis_unsatisfiable`) — so GAP-8a closed as a
  framework question and reopened as an impossibility.

  Here the clause is satisfied outright, by an actual God:
  `inf_def6_recovered` below. Def. VI is not merely stateable; it is
  true of something.

  **How the sharpness compares to Pars I.**
  `Ethica/Pars1/Models/MultiAttribute.lean` also exhibits infinitely
  many attributes on the *full* `Pars1Axioms` register — but only by
  being **godless** (`multiAttribute_hasNoGod`; `absolutelyInfinite`
  is uniformly `False` there, which is load-bearing, not incidental).
  Pars I could have plurality *or* God, never both. The re-typed
  layer has both at once, and the only thing that changed is the type
  of the attribute argument.

  The carrier `Nat` is used for `Attr` — the attribute universe is
  genuinely infinite — while the thing universe stays a single
  substance, as Prop. XIV demands.
-/
import Ethica.Pars1.Definitions
import Ethica.Pars1.Axioms
import Ethica.Attributum.Core
import Ethica.Attributum.Axioms

namespace Ethica.Attributum.Models.InfiniteAttribute

open Ethica.Pars1
open Ethica.Attributum

universe u

/-- The thing universe: one substance, God. Prop. XIV's conclusion
    built into the carrier. -/
inductive InfThing where
  | deus
  deriving DecidableEq

/-- The base Pars I world. Same shape as
    `Models/DualAttribute.lean`: generous constants throughout, with
    the `Thing`-typed attribution channel switched off so that all
    attribution runs through `Attr := Nat`. -/
instance ethicaWorld : EthicaWorld InfThing where
  inItself                    _   := True
  perSeConceived              _   := True
  involvesExistence           _   := True
  natureRequiresExistence     _   := True
  inAnother                   _   := False
  conceivedThroughAnother     _   := False
  limitedBy                   _ _ := False
  intellectPerceivesAsEssence _ _ := False
  absolutelyInfinite          _   := True
  expressesEternalEssence     _   := True
  freelyExistent              _   := True
  constrained                 _   := False
  eternal                     _   := True

/-- The re-typed attribute world, with `Attr := Nat`: every natural
    number is an attribute of `deus`. -/
instance attrWorld : AttrWorld InfThing Nat where
  toEthicaWorld               := ethicaWorld
  perceivedAsEssence      _ _ := True
  perSeConceivedAttr        _ := True
  expressesEternalEssenceAttr _ := True

/-- The stated-axiom register holds, exactly as in
    `Models/DualAttribute.lean`. A10 discharges vacuously (the
    `Thing`-typed attribution channel is empty). -/
instance statedAxioms : StatedAxioms InfThing where
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
  ax_attribute_perSe _ _ h := h.2.elim
  ax_causaSui_iff _ := Iff.rfl

/-- The re-typed attribute register holds in full, with `Attr := Nat`. -/
instance attrAxioms : AttrAxioms InfThing Nat where
  ax_attributum_perSe _ _ _ := trivial
  ax_substanceIdByAttributum s₁ s₂ _ _ _ := by cases s₁; cases s₂; rfl
  ax_substance_has_attributum _ _ := ⟨0, ⟨⟨trivial, trivial⟩, trivial⟩⟩
  ax_IsGod_has_attributum_of _ _ _ _ _ _ := ⟨⟨trivial, trivial⟩, trivial⟩

/-! ## The results -/

/-- `deus` satisfies the re-typed Def. VI's structural clauses. -/
theorem inf_deus_isGod : IsGodAttr (Attr := Nat) InfThing.deus := by
  refine ⟨⟨trivial, trivial⟩, trivial, ?_, ?_⟩
  · exact ⟨0, ⟨trivial, trivial⟩, trivial⟩
  · intro _ _
    exact trivial

/-- **Def. VI recovered.** God has at least `n` distinct attributes
    for every `n` — Spinoza's "*constantem infinitis attributis*",
    satisfied by an actual God for the first time in this
    formalisation.

    Witness: the identity injection `Fin n → Nat`, `i ↦ i.val`.
    Injectivity is `Fin.eq_of_val_eq`.

    Contrast `Ethica.Pars1.def6_infinitis_attributis_unsatisfiable`,
    which proves `¬ HasInfiniteAttributes g` for *every* God in
    *every* `Pars1Axioms` world. -/
theorem inf_def6_recovered : HasInfiniteAttrs (Attr := Nat) InfThing.deus := by
  intro n
  refine ⟨fun i => i.val, ?_, ?_⟩
  · intro _
    exact ⟨⟨trivial, trivial⟩, trivial⟩
  · intro _ _ h
    exact Fin.eq_of_val_eq h

/-- The full Def. VI claim in one statement: there is a God, and it
    has infinitely many attributes.

    This is the sentence GAP-8a was opened to make expressible and
    that the attribute-collapse theorem then proved impossible. It is
    now a theorem. -/
theorem inf_god_with_infinite_attributes :
    ∃ g : InfThing,
      IsGodAttr (Attr := Nat) g ∧ HasInfiniteAttrs (Attr := Nat) g :=
  ⟨InfThing.deus, inf_deus_isGod, inf_def6_recovered⟩

/-! ## Sanity checks -/

/-- Sanity check: Prop. IX's corollary (re-typed) applies — God
    dominates every substance in attributes. -/
example (s : InfThing) (hs : Substance s) :
    hasMoreRealityThanAttr (Attr := Nat) InfThing.deus s :=
  prop_9_cor_godMaximalRealityAttr InfThing.deus inf_deus_isGod s hs

/-- Sanity check: two named attributes, distinct, both God's — the
    `DualAttribute` result reproduced inside the infinite model. -/
example : hasAtLeastNAttrs (Attr := Nat) InfThing.deus 2 :=
  inf_def6_recovered 2

end Ethica.Attributum.Models.InfiniteAttribute
