/-
  Spinoza, *Ethica* Pars I — consistency witness for `InherenceAxioms`.

  `InherenceAxioms` (`Ethica/Pars1/Inherence.lean`) adds four new
  fields — A33, A34, A35, A36 — on top of `CausalAxioms`. Before
  trusting proofs that consume `InherenceAxioms` (Props. XV, XVIII,
  XXIV, XXVI (partial), XXIX), we need to know the typeclass is
  *satisfiable*: that some concrete `Thing` type and interpretation
  discharges all four. This file plays the same role for
  `InherenceAxioms` that `Models/MereologyWitness.lean` plays for
  `MereologyAxioms` and `Models/GodWorld.lean` plays for
  `TheologiaAxioms`.

  We reuse `Models/SingleSubstance.lean`'s existing `EthicaWorld
  Unit` / `Pars1Axioms Unit` / `CausalWorld Unit` / `CausalAxioms
  Unit` instances (without touching that file) and add an
  `InherenceWorld Unit` instance with `inheresIn _ _ := False`. On
  `Unit`, `inAnother` and `conceivedThroughAnother` are both `False`
  (`SingleSubstance.ethicaWorld`), so `Mode ()` unfolds to `False ∧
  False`, i.e. `False` — the unique element is never a mode. A33,
  A35, and A36 all have `Mode x` as a hypothesis, so they discharge
  vacuously via that falsity; A34 has `inheresIn x y` as its
  hypothesis, which is `False` by construction, so it discharges
  vacuously too. Placed in its own file, rather than at the end of
  `Inherence.lean`, to keep import layering clean — `Models/` files
  import the core layer, never the reverse. -/
import Ethica.Pars1.Definitions
import Ethica.Pars1.Axioms
import Ethica.Pars1.Causation
import Ethica.Pars1.Propositions
import Ethica.Pars1.Inherence
import Ethica.Pars1.Models.SingleSubstance

namespace Ethica.Pars1.Models.InherenceWitness

open Ethica.Pars1
open EthicaWorld CausalWorld InherenceWorld
open Ethica.Pars1.Models.SingleSubstance
  (ethicaWorld pars1Axioms causalWorld causalAxioms)

/-- `Unit`'s inherence relation is uniformly `False` — the unique
    element is in nothing (consistent with it never being a mode). -/
instance inherenceWorld : InherenceWorld Unit where
  toCausalWorld := causalWorld
  inheresIn _ _ := False

/-- A33, A35, A36 discharge vacuously: `Mode ()` is `False ∧ False`
    on `Unit` (`SingleSubstance.ethicaWorld` sets both `inAnother`
    and `conceivedThroughAnother` to `False`), so any `Mode x`
    hypothesis is absurd. A34 discharges vacuously since `inheresIn`
    is uniformly `False`. -/
instance inherenceAxioms : InherenceAxioms Unit where
  toCausalAxioms := causalAxioms
  ax_mode_inheres_in_substance _ hm := hm.1.elim
  ax_inherence_causation _ _ h := h.elim
  ax_mode_not_involvesExistence _ hm := hm.1.elim
  ax_mode_constrained _ hm := hm.1.elim

/-- Sanity check: the unique element is not a mode (reused fact,
    restated here for local legibility). -/
example : ¬ Mode () := fun h => h.1

/-- Sanity check: Prop. XV holds on `Unit` — the unique element is
    God (per `SingleSubstance.lean`'s existing `example : IsGod ()`)
    and every element (i.e. the unique one) equals God. -/
example (hgod : IsGod ()) : ∀ x : Unit, x = () ∨ inheresIn x () :=
  prop_15_allInGod () hgod

/-- Sanity check: Prop. XXIX holds on `Unit`. -/
example : ∀ x : Unit, causaSui x ∨ Constrained x :=
  prop_29_nothingContingent

end Ethica.Pars1.Models.InherenceWitness
