/-
  Spinoza, *Ethica* Pars I — consistency witness for `TheologiaAxioms`.

  `TheologiaAxioms` (`Ethica/Pars1/Theologia.lean`) adds five new
  fields — A27–A31 — on top of `Pars1Axioms`. Before trusting proofs
  that consume `TheologiaAxioms`, we need to know the typeclass is
  *satisfiable*: that some concrete `Thing` type and interpretation
  discharges every field simultaneously. This file plays the same
  role for `TheologiaAxioms` that `Models/SingleSubstance.lean` plays
  for `Pars1Axioms`.

  `Models/SingleSubstance.lean`'s `Unit` model already interprets its
  unique element as absolutely infinite (`absolutelyInfinite _ :=
  True`), so `IsGod ()` holds there (see that file's own sanity-check
  `example : IsGod ()`). That is exactly the carrier A27
  (`ax_god_exists`) needs, so rather than duplicating a fresh
  one-element type, we add a `TheologiaAxioms Unit` instance on top of
  `SingleSubstance`'s existing `EthicaWorld Unit` / `Pars1Axioms Unit`
  instances here, without touching `SingleSubstance.lean` itself. -/
import Ethica.Pars1.Definitions
import Ethica.Pars1.Axioms
import Ethica.Pars1.Propositions
import Ethica.Pars1.Theologia
import Ethica.Pars1.Models.SingleSubstance

namespace Ethica.Pars1.Models.GodWorld

open Ethica.Pars1
open EthicaWorld
open Ethica.Pars1.Models.SingleSubstance (ethicaWorld pars1Axioms)

/-- `Unit` (as set up by `Models.SingleSubstance`) satisfies
    `TheologiaAxioms`: the unique element `()` witnesses `IsGod`
    (A27); the remaining four fields discharge the same way the
    `Pars1Axioms` fields did — every predicate involved is a uniform
    constant on `Unit`, so each bridge reduces to `trivial` or a
    one-line implication between constants. -/
instance theologiaAxioms : TheologiaAxioms Unit where
  toPars1Axioms := pars1Axioms
  ax_god_exists :=
    let attr_witness : Attribute () () := ⟨⟨trivial, trivial⟩, trivial⟩
    ⟨(), ⟨trivial, trivial⟩, trivial, ⟨(), attr_witness⟩,
      fun _ _ => trivial⟩
  ax_natureRequiresExistence_eternal _ _ := trivial
  ax_attribute_involvesExistence _ _ _ := trivial
  ax_causaSui_unconstrained_free _ _ _ := trivial
  ax_substance_not_constrained _ _ h := h

/-- **A27 discharges non-vacuously on `Unit`**: the unique element is
    God. This is the same witness `SingleSubstance.lean` already
    records as a sanity check; repeated here as the explicit
    consistency claim for `TheologiaAxioms`. -/
theorem godWorld_god_exists : ∃ g : Unit, IsGod g :=
  TheologiaAxioms.ax_god_exists (Thing := Unit)

/-- Sanity check: Prop. XI holds on `Unit` under `TheologiaAxioms`. -/
example : ∃ g : Unit, IsGod g ∧ involvesExistence g ∧
    natureRequiresExistence g :=
  prop_11_godNecessarilyExists

/-- Sanity check: Prop. XVII holds on `Unit` — the unique element is
    free. -/
example : Free () :=
  prop_17_godIsFree () ⟨⟨trivial, trivial⟩, trivial, ⟨(), ⟨⟨trivial, trivial⟩, trivial⟩⟩,
    fun _ _ => trivial⟩

/-- Sanity check: Prop. XIX holds on `Unit` — the unique element is
    eternal. -/
example : Eternal () :=
  prop_19_godIsEternal () ⟨⟨trivial, trivial⟩, trivial, ⟨(), ⟨⟨trivial, trivial⟩, trivial⟩⟩,
    fun _ _ => trivial⟩

end Ethica.Pars1.Models.GodWorld
