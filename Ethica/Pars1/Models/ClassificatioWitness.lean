/-
  Spinoza, *Ethica* Pars I — consistency witness for `ClassificatioAxioms`.

  `ClassificatioAxioms` (`Ethica/Pars1/Classificatio.lean`) adds one
  new field — **A44** (`ax_consecution_trichotomy`) — on top of
  `ConsecutioAxioms`. This file extends `Models/ConsecutioWitness.lean`'s
  one-element carrier `ConsecutioW` with a `ClassificatioAxioms`
  instance, so the full extended register A1–A15, A27–A44 is
  witnessed consistent on one carrier.

  Discharge is vacuous: `Mode x` is `False ∧ False` on `ConsecutioW`
  (`inAnother`/`conceivedThroughAnother` are both `False` in the
  `ethicaWorld` profile), exactly the same shape `ConsecutioWitness.
  lean` already uses to discharge A42
  (`ax_finiteMode_causedByFiniteMode _ hm _ := hm.1.elim`) and
  A33/A35/A36. The trichotomy's hypothesis `Mode x` is never met, so
  A44 requires no genuine case analysis here — consistency, not
  content, is what this file certifies.

  By `trichotomySigma_of_classificatio` (`Classificatio.lean`), this
  instance also witnesses the demote register `TrichotomySigma
  ConsecutioW`, i.e. consistency of Σ for the A42 demote experiment. -/
import Ethica.Pars1.Definitions
import Ethica.Pars1.Axioms
import Ethica.Pars1.Causation
import Ethica.Pars1.Propositions
import Ethica.Pars1.Theologia
import Ethica.Pars1.Mereology
import Ethica.Pars1.Inherence
import Ethica.Pars1.Consecutio
import Ethica.Pars1.Classificatio
import Ethica.Pars1.Models.ConsecutioWitness

namespace Ethica.Pars1.Models.ClassificatioWitness

open Ethica.Pars1
open Ethica.Pars1.Models.ConsecutioWitness
open EthicaWorld CausalWorld InherenceWorld ConsecutioWorld

/-- A44 discharges vacuously on `ConsecutioW`, exactly as A42 does in
    `ConsecutioWitness.consecutioAxioms`: `Mode x` is impossible
    (`hx.1 : inAnother x`, which is `False` in the `ethicaWorld`
    profile), so `hx.1.elim` closes every branch of the trichotomy at
    once. -/
instance classificatioAxioms : ClassificatioAxioms ConsecutioW :=
  { (inferInstance : ConsecutioAxioms ConsecutioW) with
    ax_consecution_trichotomy := fun _ hx => hx.1.elim }

/-! ## Sanity checks -/

/-- Prop. XXIII (partial) holds on `ConsecutioW` — vacuously, since
    `ConsecutioW` has no modes. -/
example :
    ∀ x : ConsecutioW, Mode x →
      (∃ g a, IsGod g ∧ Attribute a g ∧ followsAbsolutely x a) ∨
      (∃ m, Mode m ∧ Eternal m ∧ ¬ finitumInSuoGenere m ∧ followsFrom x m) ∨
      (∃ y, Mode y ∧ finitumInSuoGenere y ∧ y ≠ x ∧ followsFrom x y) :=
  prop_23_partial_classification

/-- The demote register `TrichotomySigma` is satisfiable on
    `ConsecutioW` (via `trichotomySigma_of_classificatio`), and the
    A42 demote theorem holds on it — vacuously, as above. -/
example :
    ∀ x : ConsecutioW, Mode x → finitumInSuoGenere x →
      ∃ y, Mode y ∧ finitumInSuoGenere y ∧ y ≠ x ∧ Cause y x :=
  A42_demote_via_trichotomy

end Ethica.Pars1.Models.ClassificatioWitness
