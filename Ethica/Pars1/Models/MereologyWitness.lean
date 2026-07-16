/-
  Spinoza, *Ethica* Pars I — consistency witness for `MereologyAxioms`.

  `MereologyAxioms` (`Ethica/Pars1/Mereology.lean`) adds one new field
  — A32 — on top of `Pars1Axioms`. Before trusting proofs that consume
  `MereologyAxioms` (Props. XII/XIII), we need to know the typeclass
  is *satisfiable*: that some concrete `Thing` type and interpretation
  discharges A32. This file plays the same role for `MereologyAxioms`
  that `Models/GodWorld.lean` plays for `TheologiaAxioms`.

  We reuse `Models/SingleSubstance.lean`'s existing `EthicaWorld Unit`
  / `Pars1Axioms Unit` instances (without touching that file) and add
  a `MereologyWorld Unit` instance with `properPart _ _ := False`: the
  unique element has no proper parts, so A32's hypothesis
  `properPart p s` is never satisfiable and the axiom discharges
  vacuously. This is placed in its own file, rather than at the end of
  `Mereology.lean`, to keep import layering clean — `Models/` files
  import the core layer, never the reverse. -/
import Ethica.Pars1.Definitions
import Ethica.Pars1.Axioms
import Ethica.Pars1.Propositions
import Ethica.Pars1.Mereology
import Ethica.Pars1.Models.SingleSubstance

namespace Ethica.Pars1.Models.MereologyWitness

open Ethica.Pars1
open EthicaWorld MereologyWorld
open Ethica.Pars1.Models.SingleSubstance (ethicaWorld pars1Axioms)

/-- `Unit` has no proper parts: `properPart` is uniformly `False`. -/
instance mereologyWorld : MereologyWorld Unit where
  toEthicaWorld := ethicaWorld
  properPart _ _ := False

/-- A32 discharges vacuously on `Unit`: `properPart p s` is `False`,
    so the hypothesis of `ax_substancePart_sameNatureSubstance` is
    never met. -/
instance mereologyAxioms : MereologyAxioms Unit where
  toPars1Axioms := pars1Axioms
  ax_substancePart_sameNatureSubstance _ _ _ h := h.elim

/-- Sanity check: the unique element has no proper part, hence is not
    divisible. -/
example : ¬ Divisible () := by
  intro ⟨_, h⟩
  exact h.elim

/-- Sanity check: Prop. XII holds on `Unit`. -/
example : ∀ s : Unit, Substance s → ¬ Divisible s :=
  prop_12_substanceIndivisible

/-- Sanity check: Prop. XIII holds on `Unit` (the unique element is
    God, per `SingleSubstance.lean`'s existing `example : IsGod ()`). -/
example (hgod : IsGod ()) : ¬ Divisible () :=
  prop_13_absolutelyInfiniteSubstanceIndivisible () hgod

end Ethica.Pars1.Models.MereologyWitness
