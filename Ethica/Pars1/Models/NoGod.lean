/-
  Spinoza, *Ethica* Pars I — the A27 irreducibility witness.

  Mirrors the counter-model methodology of `Models/Counterexamples.lean`:
  independence claims ("P is not derivable from axiom set Σ") are
  meta-logical statements about Lean and cannot be expressed as Lean
  theorems directly. The honest mechanical evidence is a **counter-
  model** — a concrete model satisfying the alleged premises while
  falsifying the conclusion. If a Lean derivation of the conclusion
  from the premises existed, it would specialise to the counter-model
  and yield `False`, hence no such derivation exists.

  ## The register this counter-model instances

  Unlike `Models/Counterexamples.lean`'s A12/A15 counter-models — which
  run against `StatedAxioms` (the register *without* the Section III
  substantive commitments A12/A13/A14/A15) — this counter-model
  instances the **full** `Pars1Axioms` register, A1 through A15,
  including all four Section III commitments. This is a *stronger*
  baseline: it shows A27 (`TheologiaAxioms.ax_god_exists`, "Deus
  datur") is not derivable even from the complete stated-plus-
  committed axiom set of Pars I as it stood before this module.

  ## The model

  A one-element universe `NoGodThing`. Every "substance-side"
  predicate is interpreted as `True` (so the unique element is a
  substance, is causa sui, is eternal, is free — everything Prop. XI
  through XIX would want of *something*) **except** `absolutelyInfinite`,
  which is set to `False`. That single load-bearing choice makes
  `IsGod` unsatisfiable in this model (its second conjunct is
  `absolutelyInfinite g`), while leaving every other `Pars1Axioms`
  field trivially dischargeable — including A12 (indiscernibility of
  substance by attribute), which holds *vacuously* here because the
  single constructor makes any two `NoGodThing`s propositionally
  equal, and A15 (universality of God's attributes), which holds
  *vacuously* because its hypothesis `IsGod g` is never satisfiable.
-/
import Ethica.Pars1.Definitions
import Ethica.Pars1.Axioms

namespace Ethica.Pars1.Models.NoGod

open Ethica.Pars1
open EthicaWorld

/-- The one-element universe with nothing absolutely infinite. -/
inductive NoGodThing where
  | it : NoGodThing
  deriving DecidableEq

/-- Interpretation: the unique element is a substance (in itself, per
    se conceived), is causa sui (involves/requires existence), is its
    own attribute, is eternal, and is free — every `Pars1Axioms` field
    other than absolute infinity is satisfied maximally.

    The load-bearing choice is `absolutelyInfinite _ := False`: this
    is what makes `IsGod` unsatisfiable below, while every other
    field stays at its "most generous" constant so the rest of
    `Pars1Axioms` discharges without contortion. -/
instance ethicaWorld : EthicaWorld NoGodThing where
  inItself                      _   := True
  perSeConceived                _   := True
  involvesExistence             _   := True
  natureRequiresExistence       _   := True
  inAnother                     _   := False
  conceivedThroughAnother       _   := False
  limitedBy                     _ _ := False
  intellectPerceivesAsEssence   _ _ := True
  absolutelyInfinite            _   := False
  expressesEternalEssence       _   := True
  freelyExistent                _   := True
  constrained                   _   := False
  eternal                       _   := True

/-- `NoGodThing` satisfies the *full* `Pars1Axioms` register (A1–A15,
    including the Section III commitments A12–A15). Every field
    discharges by `trivial`/`Iff.rfl`, except A12 and A15 which need
    a one-line case split / vacuous discharge respectively. -/
instance pars1Axioms : Pars1Axioms NoGodThing where
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
  -- A12 holds vacuously: the single constructor forces `s₁ = s₂`.
  ax_substanceIdByAttribute
    | .it, .it, _, _, _ => rfl
  ax_substance_involves_existence          _ _ := trivial
  ax_substance_has_attribute               _ _ :=
    ⟨.it, ⟨trivial, trivial⟩, trivial⟩
  -- A15 holds vacuously: `IsGod g` is never satisfiable here
  -- (its second conjunct `absolutelyInfinite g` is `False`).
  ax_IsGod_has_attribute_of                _ _ _ hgod _ _ :=
    hgod.2.1.elim

/-- **Nothing in this model is God**: `IsGod` requires
    `absolutelyInfinite`, which is `False` for every element. -/
theorem noGodWorld_hasNoGod : ∀ g : NoGodThing, ¬ IsGod g := by
  intro g hgod
  exact hgod.2.1

/-- **A27 is falsified in this model**: no element of `NoGodThing`
    satisfies `IsGod`. -/
theorem A27_falsified : ¬ ∃ g : NoGodThing, IsGod g := by
  intro ⟨g, hgod⟩
  exact noGodWorld_hasNoGod g hgod

/-! ## The irreducibility argument

  Any Lean derivation of `∃ g, IsGod g` from `Pars1Axioms` alone
  (i.e. a term of type `∀ {Thing} [EthicaWorld Thing]
  [Pars1Axioms Thing], ∃ g : Thing, IsGod g`) would specialise to
  `NoGodThing` via the `ethicaWorld` and `pars1Axioms` instances
  above, producing a term of type `∃ g : NoGodThing, IsGod g`. That
  contradicts `A27_falsified`. Hence no such derivation exists: A27
  is **not derivable** from `Pars1Axioms` — Prop. XI genuinely
  requires the Section III commitment `TheologiaAxioms.ax_god_exists`.

  This is machine-checked confirmation, against the FULL `Pars1Axioms`
  register (not merely `StatedAxioms`), of Bennett's claim (1984 §18)
  that Spinoza's Prop. XI demonstrationes exceed his stated axioms:
  even after granting every other Section III commitment the project
  has made (A12–A15), God's existence still does not fall out for
  free. -/
def A27_irreducibility_witness : Prop :=
  ∃ _ : EthicaWorld NoGodThing, ∃ _ : Pars1Axioms NoGodThing,
    ¬ ∃ g : NoGodThing, IsGod g

example : A27_irreducibility_witness :=
  ⟨ethicaWorld, pars1Axioms, A27_falsified⟩

end Ethica.Pars1.Models.NoGod
