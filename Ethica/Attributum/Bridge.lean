/-
  Spinoza, *Ethica* — Attributum: the bridge to Pars I.

  The Attributum layer is a *parallel* branch: nothing in
  `Ethica/Pars1/` is modified, and the v1.0.0 register together with
  the published irreducibility results (arXiv:2605.02331) stands
  untouched. This file records exactly how the two regimes relate.

  The content is one embedding and its consequence.

  **The embedding**: take `Attr := Thing` and route
  `perceivedAsEssence` through `intellectPerceivesAsEssence`. That is
  `legacyAttrWorld` below, and under it every Attributum-layer notion
  becomes *definitionally* its Pars I counterpart — `Attributum` is
  `Attribute`, `IsGodAttr` is `IsGod`, `hasAtLeastNAttrs` is
  `hasAtLeastNAttributes`. All three bridge lemmas are `Iff.rfl`.

  **The consequence**: the attribute-collapse theorem transports
  along the embedding. `legacy_collapse` and
  `legacy_god_no_two_attributes` re-derive Pars I's impossibility
  results *inside the Attributum vocabulary*, purely by instantiating
  `Attr := Thing`.

  Reading the two files together gives the exact diagnosis GAP-25
  asked for. `Models/DualAttribute.lean` proves

      ∃ g, IsGodAttr g ∧ hasAtLeastNAttrs g 2

  while `legacy_god_no_two_attributes` here proves that the same
  statement is refutable whenever `Attr := Thing`. Same sentence,
  same axioms (A12′/A14′/A15′ are A12/A14/A15 verbatim), opposite
  verdicts — and the only difference between the two settings is the
  *type* of the attribute argument. The collapse is therefore an
  artefact of the Prop. X scholium's identification of attributes
  with things, not a consequence of Spinoza's substantive
  commitments.

  `legacyAttrWorld` is deliberately a `def`, **not** an `instance`:
  as a global instance it would compete with every model's own
  `AttrWorld` during resolution. It is applied explicitly.
-/
import Ethica.Pars1.Definitions
import Ethica.Pars1.Axioms
import Ethica.Pars1.Propositions
import Ethica.Pars1.Realitas
import Ethica.Attributum.Core

namespace Ethica.Attributum

open Ethica.Pars1

universe u

/-- The legacy embedding: `Attr := Thing`, with attribution routed
    through Pars I's `intellectPerceivesAsEssence` and the two
    attribute-side predicates routed through their `Thing`-typed
    originals.

    This reconstructs, inside the Attributum layer, exactly the
    configuration Pars I commits to — including the Prop. X scholium
    reading that attributes inhabit the universe of things. -/
def legacyAttrWorld (Thing : Type u) [EthicaWorld Thing] :
    AttrWorld Thing Thing where
  toEthicaWorld               := inferInstance
  perceivedAsEssence      s a := EthicaWorld.intellectPerceivesAsEssence s a
  perSeConceivedAttr        a := EthicaWorld.perSeConceived a
  expressesEternalEssenceAttr a := EthicaWorld.expressesEternalEssence a

section bridge

variable (Thing : Type u) [EthicaWorld Thing]

/-- Under the legacy embedding, `Attributum` *is* Pars I's
    `Attribute` — definitionally, not merely extensionally. -/
theorem legacy_Attributum_iff (a s : Thing) :
    @Attributum Thing Thing (legacyAttrWorld Thing) a s ↔ Attribute a s :=
  Iff.rfl

/-- Under the legacy embedding, `IsGodAttr` *is* Pars I's `IsGod`. -/
theorem legacy_IsGodAttr_iff (g : Thing) :
    @IsGodAttr Thing Thing (legacyAttrWorld Thing) g ↔ IsGod g :=
  Iff.rfl

/-- Under the legacy embedding, the re-typed counting framework *is*
    Pars I's counting framework. -/
theorem legacy_hasAtLeastNAttrs_iff (s : Thing) (n : Nat) :
    @hasAtLeastNAttrs Thing Thing (legacyAttrWorld Thing) s n ↔
      hasAtLeastNAttributes s n :=
  Iff.rfl

/-- Under the legacy embedding, `HasInfiniteAttrs` *is* Pars I's
    `HasInfiniteAttributes`. -/
theorem legacy_HasInfiniteAttrs_iff (s : Thing) :
    @HasInfiniteAttrs Thing Thing (legacyAttrWorld Thing) s ↔
      HasInfiniteAttributes s :=
  Iff.rfl

end bridge

section collapse_transport

variable (Thing : Type u) [EthicaWorld Thing] [Pars1Axioms Thing]

/-- **The attribute-collapse theorem, transported.** In a
    `Pars1Axioms` world with a God, every `Attributum` of every
    substance equals God — *provided* the attribute type is `Thing`
    itself.

    Direct transport of `Ethica.Pars1.attribute_collapse` along
    `legacy_Attributum_iff`. Note the conclusion `a = g` only
    typechecks because `a : Thing`; in a genuine `AttrWorld Thing
    Attr` with `Attr ≠ Thing` this statement cannot even be
    written. -/
theorem legacy_collapse (g : Thing) (hgod : IsGod g) (s a : Thing)
    (h : @Attributum Thing Thing (legacyAttrWorld Thing) a s) : a = g :=
  attribute_collapse g hgod s a ((legacy_Attributum_iff Thing a s).mp h)

/-- **The impossibility, transported.** Under the legacy embedding no
    God has two distinct attributes.

    Compare
    `Ethica.Attributum.Models.DualAttribute.dual_god_two_attributes`,
    which exhibits a God with two distinct attributes in a world
    carrying `AttrAxioms` (A10′/A12′/A14′/A15′ — the same axioms,
    re-typed) and `StatedAxioms` (Spinoza's own A1–A11).

    The pair is the whole result of the Attributum layer: the *only*
    difference between the setting where this statement is refutable
    and the setting where it is satisfiable is whether the attribute
    argument shares a type with substances. -/
theorem legacy_god_no_two_attributes (g : Thing) (hgod : IsGod g) :
    ¬ @hasAtLeastNAttrs Thing Thing (legacyAttrWorld Thing) g 2 := by
  intro h
  exact god_no_two_attributes g hgod ((legacy_hasAtLeastNAttrs_iff Thing g 2).mp h)

/-- **Def. VI's unsatisfiability, transported.** Under the legacy
    embedding no God has infinitely many attributes.

    Compare
    `Ethica.Attributum.Models.InfiniteAttribute.inf_def6_recovered`,
    where a God does. -/
theorem legacy_def6_unsatisfiable (g : Thing) (hgod : IsGod g) :
    ¬ @HasInfiniteAttrs Thing Thing (legacyAttrWorld Thing) g := by
  intro h
  exact def6_infinitis_attributis_unsatisfiable g hgod
    ((legacy_HasInfiniteAttrs_iff Thing g).mp h)

end collapse_transport

end Ethica.Attributum
