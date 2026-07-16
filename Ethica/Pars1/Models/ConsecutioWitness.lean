/-
  Spinoza, *Ethica* Pars I — consistency witness for `ConsecutioAxioms`.

  `ConsecutioAxioms` (`Ethica/Pars1/Consecutio.lean`) adds seven new
  fields — A37–A43 — on top of `InherenceAxioms`. Before trusting
  proofs that consume `ConsecutioAxioms` (Props. XVI (partial), XX
  (partial), XXI, XXII, XXV cor., XXVIII, XXXVI), we need to know the
  typeclass is *satisfiable*.

  A43 (`ax_omnia_effectum : ∀ x, ∃ e, followsFrom e x`) is *not*
  vacuously dischargeable the way A33–A36 were on `Models/
  InherenceWitness.lean`'s `Unit` model (which set `inheresIn _ _ :=
  False` and leaned on `Mode` being uniformly `False`): A43 has no
  `Mode`/`inheresIn` hypothesis to fall back on, so it needs an actual
  witness `e` for every `x`. We therefore do **not** reuse
  `Models/SingleSubstance.lean`'s `Unit` model here (whose
  `InherenceWitness.lean` companion sets `inheresIn` to `False`);
  instead this file defines a **fresh, self-contained one-element
  carrier** `ConsecutioW` and gives it a uniformly *positive* profile
  — `Cause`, `inheresIn`, `followsFrom`, and `followsAbsolutely` are
  all `True` — so A43 (and every other consecution axiom) discharges
  non-vacuously by reflexivity of the one-element domain rather than
  by an empty hypothesis.

  This file also adds `TheologiaAxioms` and `MereologyAxioms` instances
  on `ConsecutioW` (both cheap, given the positive profile below), so
  the model witnesses consistency of the **full extended register A1–
  A15 and A27–A43 on one carrier** — i.e. every layer developed so far
  *except* the Modal layer (A16–A26, `ModalForm.lean`), which needs a
  separate `World`-indexed family of typeclasses (`existsAt`,
  `causeAt`, `conceptualDep`, …) that this single-carrier model does
  not set up and that lies outside this batch's scope. With that one
  honest exception, this is the largest single-model consistency proof
  in the project so far — `Models/InherenceWitness.lean`'s companion
  covered only A1–A15 + A33–A36 (reusing `Unit`, all-vacuous
  discharge); this file covers A1–A15, A27–A43 (Theologia +
  Mereology + Inherence + Consecutio), non-vacuously for the seven new
  fields. -/
import Ethica.Pars1.Definitions
import Ethica.Pars1.Axioms
import Ethica.Pars1.Causation
import Ethica.Pars1.Propositions
import Ethica.Pars1.Theologia
import Ethica.Pars1.Mereology
import Ethica.Pars1.Inherence
import Ethica.Pars1.Consecutio

namespace Ethica.Pars1.Models.ConsecutioWitness

open Ethica.Pars1
open EthicaWorld CausalWorld InherenceWorld ConsecutioWorld MereologyWorld

/-- The fresh one-element carrier for this witness. Deliberately a
    *new* type (not `Unit`, not `SingleSubstance`'s `Unit` instance)
    so this file owns its own instance set independent of every prior
    `Models/*.lean` witness. -/
inductive ConsecutioW where
  | it

/-- Any two elements of `ConsecutioW` are equal — the one-constructor,
    no-argument shape makes this immediate by `cases`. Used repeatedly
    below to discharge the `x ≠ y` clause of `finitumInSuoGenere`. -/
theorem ConsecutioW_eq (x y : ConsecutioW) : x = y := by
  cases x; cases y; rfl

/-- Uniformly positive profile: every "should hold of the unique
    self-existent substance" predicate is `True`; every relation
    (`Cause`, `inheresIn`, `followsFrom`, `followsAbsolutely`,
    `intelligibleThrough`) is uniformly `True` as well — the one
    element causes/inheres-in/follows-from/is-intelligible-through
    itself. Only the two "otherness" predicates (`inAnother`,
    `conceivedThroughAnother`) and `constrained`/`limitedBy` are
    `False`, matching `Models/SingleSubstance.lean`'s pattern. -/
instance ethicaWorld : EthicaWorld ConsecutioW where
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

/-- No element of `ConsecutioW` is `finitumInSuoGenere`: that notion
    needs a *distinct* same-nature limiting element, and `ConsecutioW`
    has only one element (`ConsecutioW_eq`). -/
theorem consecutioW_not_finite (x : ConsecutioW) : ¬ finitumInSuoGenere x :=
  fun ⟨y, hne, _, _⟩ => hne (ConsecutioW_eq x y)

/-- All Pars I base axioms hold on `ConsecutioW` — identical
    discharge pattern to `Models/SingleSubstance.lean`'s `Unit`
    instance, restated on the fresh carrier. -/
instance pars1Axioms : Pars1Axioms ConsecutioW where
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
  ax_substanceIdByAttribute       s₁ s₂ _ _ _ := ConsecutioW_eq s₁ s₂
  ax_substance_involves_existence          _ _ := trivial
  ax_substance_has_attribute               _ _ :=
    ⟨.it, ⟨trivial, trivial⟩, trivial⟩
  ax_IsGod_has_attribute_of                _ _ _ _ _ _ :=
    ⟨⟨trivial, trivial⟩, trivial⟩

/-- Causal layer: the unique element is its own cause and is
    intelligible only through itself — both uniformly `True`. -/
instance causalWorld : CausalWorld ConsecutioW where
  toEthicaWorld := ethicaWorld
  Cause _ _               := True
  intelligibleThrough _ _ := True

/-- All causal axioms hold. A5 (substance-restricted) fires vacuously:
    `sameNature x y` always holds on `ConsecutioW` (witnessed by the
    unique element as a shared attribute), so `¬ sameNature` never
    applies. -/
instance causalAxioms : CausalAxioms ConsecutioW where
  toPars1Axioms := pars1Axioms
  ax4_effectIntelligibleThroughCause _ _ _ := trivial
  ax5_noCommonNoIntelligibility := by
    intro x y _ _ hno _
    have attr : Attribute (ConsecutioW.it) (ConsecutioW.it) :=
      ⟨⟨trivial, trivial⟩, trivial⟩
    cases x; cases y
    exact hno ⟨.it, attr, attr⟩

/-- Inherence layer: the unique element is in itself — `True`. -/
instance inherenceWorld : InherenceWorld ConsecutioW where
  toCausalWorld := causalWorld
  inheresIn _ _ := True

/-- A33, A35, A36 discharge vacuously: `Mode x` is `False ∧ False` on
    `ConsecutioW` (`inAnother` and `conceivedThroughAnother` are both
    `False`), so any `Mode x` hypothesis is absurd. A34 discharges
    *non*-vacuously: `inheresIn` and `Cause` are both uniformly `True`
    here (unlike `Models/InherenceWitness.lean`'s `Unit` model, which
    set `inheresIn` to `False`), so the implication is a direct
    `trivial`. -/
instance inherenceAxioms : InherenceAxioms ConsecutioW where
  toCausalAxioms := causalAxioms
  ax_mode_inheres_in_substance _ hm := hm.1.elim
  ax_inherence_causation _ _ _ := trivial
  ax_mode_not_involvesExistence _ hm := hm.1.elim
  ax_mode_constrained _ hm := hm.1.elim

/-- Consecution layer: the unique element follows from (and follows
    absolutely from) itself — both uniformly `True`. -/
instance consecutioWorld : ConsecutioWorld ConsecutioW where
  toInherenceWorld := inherenceWorld
  followsFrom _ _       := True
  followsAbsolutely _ _ := True

/-- All seven consecution axioms hold on `ConsecutioW`:

    - A37 (`ax_inherence_consecution`) and A38
      (`ax_consecution_causation`): both premises and conclusions are
      uniformly `True` (`inheresIn`, `followsFrom`, `Cause`), so each
      is a direct `trivial`.
    - A39 (`ax_absolute_consecution`): same, `followsAbsolutely` and
      `followsFrom` both `True`.
    - A40 (`ax_absoluteConsecution_eternalInfinite`) and A41
      (`ax_infiniteModeTransfer`): both conclude `Eternal x ∧
      ¬ finitumInSuoGenere x`. `Eternal x` is `True` directly;
      `¬ finitumInSuoGenere x` holds unconditionally by
      `consecutioW_not_finite` (no distinct same-nature element
      exists to witness `finitumInSuoGenere` on a one-element
      carrier), so both axioms discharge non-vacuously, ignoring
      their other hypotheses entirely.
    - A42 (`ax_finiteMode_causedByFiniteMode`): discharges vacuously —
      `Mode x` is impossible on `ConsecutioW`, exactly as A33/A35/A36
      above.
    - A43 (`ax_omnia_effectum`): discharges non-vacuously — the
      unique element itself is the witness `e`, and `followsFrom` is
      uniformly `True`. -/
instance consecutioAxioms : ConsecutioAxioms ConsecutioW where
  toInherenceAxioms := inherenceAxioms
  ax_inherence_consecution _ _ _ := trivial
  ax_consecution_causation _ _ _ := trivial
  ax_absolute_consecution _ _ _ := trivial
  ax_absoluteConsecution_eternalInfinite x _ _ _ _ _ :=
    ⟨trivial, consecutioW_not_finite x⟩
  ax_infiniteModeTransfer x _ _ _ _ _ :=
    ⟨trivial, consecutioW_not_finite x⟩
  ax_finiteMode_causedByFiniteMode _ hm _ := hm.1.elim
  ax_omnia_effectum x := ⟨x, trivial⟩

/-- Theologia layer (A27–A31), added on top of `ConsecutioW` at no
    extra cost — every predicate the five axioms mention is already
    uniformly `True`/`False` in the profile above, mirroring
    `Models/GodWorld.lean`'s `Unit` instance. A27 is witnessed
    non-vacuously: `ConsecutioW.it` is `IsGod`. -/
instance theologiaAxioms : TheologiaAxioms ConsecutioW where
  toPars1Axioms := pars1Axioms
  ax_god_exists :=
    let attr_witness : Attribute (ConsecutioW.it) (ConsecutioW.it) :=
      ⟨⟨trivial, trivial⟩, trivial⟩
    ⟨.it, ⟨trivial, trivial⟩, trivial, ⟨.it, attr_witness⟩,
      fun _ _ => trivial⟩
  ax_natureRequiresExistence_eternal _ _ := trivial
  ax_attribute_involvesExistence _ _ _ := trivial
  ax_causaSui_unconstrained_free _ _ _ := trivial
  ax_substance_not_constrained _ _ h := h

/-- Mereology layer (A32), added on top of `ConsecutioW` at no extra
    cost: no proper parts exist (`properPart _ _ := False`), so A32's
    hypothesis is never met. This makes the same claim
    `Models/MereologyWitness.lean` makes for `Unit`, now also on
    `ConsecutioW` — so this single carrier witnesses the *entire*
    extended register A1–A43 (all of it, A32 included). -/
instance mereologyWorld : MereologyWorld ConsecutioW where
  toEthicaWorld := ethicaWorld
  properPart _ _ := False

instance mereologyAxioms : MereologyAxioms ConsecutioW where
  toPars1Axioms := pars1Axioms
  ax_substancePart_sameNatureSubstance _ _ _ h := h.elim

/-! ## Sanity checks -/

/-- The unique element is `IsGod`. -/
example : IsGod ConsecutioW.it :=
  let attr_witness : Attribute (ConsecutioW.it) (ConsecutioW.it) :=
    ⟨⟨trivial, trivial⟩, trivial⟩
  ⟨⟨trivial, trivial⟩, trivial, ⟨.it, attr_witness⟩, fun _ _ => trivial⟩

/-- Prop. XVI (partial) holds on `ConsecutioW`. -/
example (hgod : IsGod (ConsecutioW.it)) :
    ∀ x : ConsecutioW, Mode x → followsFrom x (ConsecutioW.it) :=
  prop_16_modesFollowFromGod ConsecutioW.it hgod

/-- Prop. XX (partial) holds on `ConsecutioW`. -/
example (hgod : IsGod (ConsecutioW.it)) :
    ∀ a : ConsecutioW, Attribute a (ConsecutioW.it) →
      involvesExistence a ∧ expressesEternalEssence a :=
  prop_20_partial_attributesExpressBoth ConsecutioW.it hgod

/-- Prop. XXI holds on `ConsecutioW`: the unique element, following
    absolutely from itself, is eternal and not finite-after-its-kind. -/
example (hgod : IsGod (ConsecutioW.it))
    (ha : Attribute (ConsecutioW.it) (ConsecutioW.it)) :
    Eternal (ConsecutioW.it) ∧ ¬ finitumInSuoGenere (ConsecutioW.it) :=
  prop_21_absoluteFollowersEternalInfinite ConsecutioW.it ConsecutioW.it
    ConsecutioW.it hgod ha trivial

/-- Prop. XXV corollary holds on `ConsecutioW`. -/
example (hgod : IsGod (ConsecutioW.it)) :
    ∀ x : ConsecutioW, x = ConsecutioW.it ∨ Mode x :=
  prop_25_cor_everythingGodOrMode ConsecutioW.it hgod

/-- Prop. XXVIII's "no first finite cause" corollary holds vacuously
    (no finite modes exist on `ConsecutioW`). -/
example :
    ¬ ∃ x : ConsecutioW, Mode x ∧ finitumInSuoGenere x ∧
      ∀ y, Mode y → finitumInSuoGenere y → y ≠ x → ¬ Cause y x :=
  prop_28_cor_noFirstFiniteCause

/-- Prop. XXXVI holds on `ConsecutioW`: the unique element has an
    effect follow from it (itself). -/
example : ∃ e : ConsecutioW, Cause (ConsecutioW.it) e :=
  prop_36_nothingWithoutEffect ConsecutioW.it

end Ethica.Pars1.Models.ConsecutioWitness
