/-
  Spinoza, *Ethica* Pars I — Axiomata.

  Latin (I-VII):

    I. Omnia, quae sunt, vel in se, vel in alio sunt.
   II. Id, quod per aliud non potest concipi, per se concipi debet.
  III. Ex data causa determinata necessario sequitur effectus, et
       contra, si nulla detur determinata causa, impossibile est ut
       effectus sequatur.
   IV. Effectus cognitio a cognitione causae dependet et eandem
       involvit.
    V. Quae nihil commune cum se invicem habent, etiam per se invicem
       intelligi non possunt, sive conceptus unius alterius conceptum
       non involvit.
   VI. Idea vera debet cum suo ideato convenire.
  VII. Quicquid ut non existens potest concipi, ejus essentia non
       involvit existentiam.

  Auxiliary axioms beyond Spinoza's seven (A1ₑ, A8-A11) are commitments
  the modern reading of Pars I forces; each is justified in
  `docs/auxiliary_axioms.md` and tracked through `docs/gaps.md`.
-/
import Ethica.Pars1.Definitions

namespace Ethica.Pars1

universe u

variable {Thing : Type u} [EthicaWorld Thing]
open EthicaWorld

/-- The axiomatic backbone of Pars I, encoded as a typeclass that any
    `EthicaWorld` ascribing to Spinoza's metaphysics must satisfy.

    Renamed from `Axioms` to `Pars1Axioms` to avoid namespace
    collisions when Mathlib (or other libraries) is imported.

    Keeping these as a class (rather than as raw `axiom` declarations)
    has two advantages:
      1. Soundness — concrete `Thing` types with explicit
         interpretations can witness the axioms (see
         `Ethica/Pars1/Models/SingleSubstance.lean`).
      2. Pedagogy — readers can swap out one axiom (e.g. drop A6 to
         see which propositions break) and trace the dependency. -/
class Pars1Axioms (Thing : Type u) [EthicaWorld Thing] : Prop where
  /-- A1: Everything that is, is either in itself or in another. -/
  ax1_inItselfOrInAnother :
    ∀ x : Thing, inItself x ∨ inAnother x

  /-- A1ₑ (exclusivity rider): "in se" and "in alio" do not co-apply.
      Spinoza's text states the disjunction without qualifying its
      mood, but the chain of *demonstrationes* in Pars I (especially
      P1, P4, P5) requires it to be exclusive: an inclusive reading
      would leave open cases the proofs silently rule out. We make
      the exclusivity an explicit commitment so Prop. I's
      disjointness part goes through without sleight of hand.
      Closes GAP-1. -/
  ax1_exclusive :
    ∀ x : Thing, ¬ (inItself x ∧ inAnother x)

  /-- A2: What cannot be conceived through another must be conceived
      through itself.

      Spinoza's literal form is `¬ conceivedThroughAnother x →
      perSeConceived x`. Under classical logic (which Lean's `Prop`
      gives us by default for excluded-middle decidable instances)
      this is *equivalent* to the disjunctive form below — not
      weaker. We use the disjunction because it is more directly
      consumable by `rcases` in downstream proofs.

      The encoding does **not** commit us to the *exclusivity* of the
      two clauses. The `inItself`/`inAnother` exclusivity is A1ₑ; the
      `perSeConceived`/`conceivedThroughAnother` exclusivity falls out
      automatically from A1ₑ + A8 + A9 (parallelism transfer), so no
      separate axiom is needed. -/
  ax2_perSeOrThroughAnother :
    ∀ x : Thing, perSeConceived x ∨ conceivedThroughAnother x

  /-- A3 (**content-free placeholder, GAP-7**): from a determinate
      cause an effect necessarily follows. The substantive form
      requires the modal layer's "necessary in every world" relation
      and is not yet implementable here.

      ⚠ DO NOT REFERENCE in proofs. The field exists only so the
      `Pars1Axioms` API surface mirrors Spinoza's seven; appealing to
      it via `Pars1Axioms.ax3_causationDeterminate` discharges to
      `trivial : True` and proves nothing about causation. Use
      `CausalAxioms.ax4_effectIntelligibleThroughCause` for
      A4-flavoured arguments; A3 proper awaits `ModalForm.lean`.

      (Note: Lean 4 does not permit `@[deprecated]` on class fields
      directly, so the discipline is documentary; any proof that
      destructures or names this field should be considered suspect.) -/
  ax3_causationDeterminate : True

  /-- A4 (**content-free placeholder**): knowledge of an effect
      involves knowledge of its cause. The substantive form is in
      `Causation.lean` (`CausalAxioms.ax4_effectIntelligibleThroughCause`).

      ⚠ DO NOT REFERENCE in proofs. Same discipline as A3. -/
  ax4_effectKnowledgeFromCause : True

  /-- A5 (**content-free placeholder**): things with nothing in common
      cannot be understood through one another. The substantive form
      is in `Causation.lean` (`CausalAxioms.ax5_noCommonNoIntelligibility`),
      properly typed against `intelligibleThrough` and restricted to
      substances (a soundness requirement; see `Causation.lean`).

      ⚠ DO NOT REFERENCE in proofs. -/
  ax5_nothingInCommonNoUnderstanding : True

  /-- A6 (**content-free placeholder**): a true idea agrees with its
      object. The substantive form requires the idea/ideatum
      machinery introduced in Pars II.

      ⚠ DO NOT REFERENCE in proofs. -/
  ax6_trueIdeaAgreesWithIdeatum : True

  /-- A7: Whatever can be conceived as non-existent, its essence does
      not involve existence. The contrapositive is the engine of
      Prop. VII (every substance exists necessarily). -/
  ax7_conceivableAsNonExistent :
    ∀ x : Thing,
      ¬ natureRequiresExistence x → ¬ involvesExistence x

  /-- A8 (parallelism, in/perSe): being "in itself" and being
      "conceived through itself" are coextensive. Spinoza uses this
      bridge tacitly throughout — Def. III pairs the two clauses but
      never asserts the iff explicitly. This is a *PSR-flavoured*
      reading (Della Rocca, Curley); Bennett 1984 §16 declines the
      coextension. Closes GAP-4 (in-half). -/
  ax_inItself_iff_perSeConceived :
    ∀ x : Thing, inItself x ↔ perSeConceived x

  /-- A9 (parallelism, alio/throughAnother): being "in another" and
      being "conceived through another" are coextensive. The mode-side
      counterpart of A8; same PSR caveat. Closes GAP-4 (alio-half). -/
  ax_inAnother_iff_conceivedThroughAnother :
    ∀ x : Thing, inAnother x ↔ conceivedThroughAnother x

  /-- A10 (attribute–substance identity-of-conception): every attribute
      *of a substance* is itself per se conceived. The hypothesis is
      the full `Attribute a s` (which carries `Substance s`) rather
      than an arbitrary `intellectPerceivesAsEssence` perception:
      the weaker hypothesis would let A10 fire on spurious
      essence-attributions, beyond what the Della Rocca / Garrett
      reading licenses. Closes GAP-5. -/
  ax_attribute_perSe :
    ∀ a s : Thing, Attribute a s → perSeConceived a

  /-- A11 (causa-sui clause-equivalence): the two clauses of Def. I —
      "involves existence" and "nature requires existence" — are
      coextensive (Spinoza's "sive" read as "id est", per Curley 1985
      p. 408). Lets `causaSui` be defined as the single clause
      `involvesExistence` while the second clause is recoverable on
      demand. -/
  ax_causaSui_iff :
    ∀ x : Thing, involvesExistence x ↔ natureRequiresExistence x

  /-- A12 (indiscernibility of substance by attribute): two substances
      sharing an attribute are identical. Adopted as an axiom rather
      than derived because Spinoza's *demonstratio* of Prop. V is
      widely judged to require additional commitment to go through
      (Bennett 1984 §17, Garrett 1990, Della Rocca 2008 ch. 2 — see
      `auxiliary_axioms.md` Section III).

      This is a **substantive metaphysical commitment**, qualitatively
      different from the definitional bridges A1ₑ / A8 / A9 / A10 / A11.
      Hypothesis is the full `Attribute a _` in both arguments; the
      redundant `Substance _` hypotheses are not needed (Attribute
      carries them).

      Closes the Prop. V mechanisation gap. Related: GAP-11 — modal
      derivation of A12, *not guaranteed to succeed* (Bennett-honest
      scoping). -/
  ax_substanceIdByAttribute :
    ∀ s₁ s₂ a : Thing,
      Attribute a s₁ → Attribute a s₂ → s₁ = s₂

  /-- A14 (substance has at least one attribute): every substance
      has at least one attribute. The Defs. III + IV pair *suggests*
      this (Def. IV defines an attribute *as* what the intellect
      perceives in a substance as constituting its essence; one
      expects a substance therefore to have *something* the intellect
      can so perceive), but the bare definitions do not entail
      `∃ a, intellectPerceivesAsEssence s a`.

      **Why an axiom**: Della Rocca 2008 ch. 2 takes this for granted
      under PSR; Bennett 1984 §17 treats it as an independent
      commitment of Spinoza's metaphysics. We commit visibly. This
      is a Section III axiom (substantive metaphysical commitment;
      see `auxiliary_axioms.md`). The explicit-hypothesis A14-candidate
      form is promoted to a committed axiom here.

      Closes GAP-13. -/
  ax_substance_has_attribute :
    ∀ s : Thing, Substance s → ∃ a, Attribute a s

  /-- A15 (universality of God's attributes): if `g` is God and `s`
      is any substance with attribute `a`, then `g` also has `a`.
      This is the substantive form of Def. VI's *infinitis
      attributis* clause for the universality reading (GAP-8b);
      cardinality (GAP-8a) remains separately tracked.

      **Why an axiom**: Bennett 1984 §18 flags this universality
      clause as a substantive metaphysical commitment in its own
      right. Della Rocca 2008 ch. 2 derives it from PSR + plenitude.
      Either way the commitment is real. We commit visibly. This
      is a Section III axiom; the explicit-hypothesis A15-candidate
      form is promoted to a committed axiom here.

      **Counter-bench**: `Models/TwoSubstance.lean` is a
      Bennett-style multi-substance world that **falsifies** A15.
      Promoting A15 here therefore removes TwoSubstance's
      `Pars1Axioms` instance — TwoSubstance becomes a non-Spinoza
      "Bennett-line" model documenting what the commitment costs.

      Closes GAP-8b. -/
  ax_IsGod_has_attribute_of :
    ∀ g s a : Thing, IsGod g → Substance s → Attribute a s →
      Attribute a g

  /-- A13 (substance involves existence): every substance's essence
      involves existence. This *is* the content of Prop. VII
      ("Ad naturam substantiae pertinet existere") adopted as an
      axiom rather than derived.

      **Why an axiom**: Spinoza's *demonstratio* of Prop. VII chains
      Prop. VI corollary ("substance cannot be produced by anything")
      with an unstated PSR-flavoured commitment ("every substance
      has *some* cause; if not by another, then by self"). Both
      links are gaps:

      - Prop. VI corollary's mode-extension ("substance not produced
        by a mode either") is asserted by Spinoza by appeal to the
        ontology (only substances + modes exist) but the contradiction
        in the mode case is not actually shown in the *corollarium*;
        Spinoza's *aliter* (alternative) appeal to A4 + Def. III is
        cleaner but still requires a conceptual-uniqueness bridge
        we have not axiomatised.
      - The "no external cause ⇒ self-caused" step is the PSR move
        Della Rocca 2008 ch. 2 makes explicit; without PSR, "no
        external cause" leaves the existence of substance unexplained
        rather than self-explained.

      We commit visibly: A13 axiomatises Prop. VII directly. Bennett
      1984 §17 also flags Prop. VII's *demonstratio* as gap-laden,
      so the pattern of Section III commitments matches A12 exactly.

      Combined with A11 (`ax_causaSui_iff`), the *natureRequiresExistence*
      half of Def. I is recoverable on demand. -/
  ax_substance_involves_existence :
    ∀ s : Thing, Substance s → involvesExistence s

/-- **The stated-axiom register**: Spinoza's seven axioms A1–A7 plus
    the Section I definitional bridges (A1ₑ, A8–A11) and the Section II
    placeholders, *without* the Section III substantive commitments
    (A12 / A13 / A14 / A15).

    This is `Pars1Axioms` minus its Section III fields. We keep it as a
    *separate* class — not as a parent of `Pars1Axioms` — for one
    structural reason that is itself the point of the demote project:

    A counter-model for "A12 is not derivable from the stated register
    plus PSR" must be an instance of a typeclass that contains the
    stated register but **not** A12. A `Pars1Axioms` instance is
    impossible for such a model, because A12
    (`ax_substanceIdByAttribute`) is a *field* of `Pars1Axioms`: any
    `Pars1Axioms` instance satisfies A12 by construction, so it could
    never falsify it. `StatedAxioms` is exactly the register against
    which the Section III axioms can be shown non-derivable at kernel
    level (`Models/Counterexamples.lean`).

    The A1–A11 field signatures duplicate those of `Pars1Axioms`
    verbatim; the duplication is deliberate and documents the
    register boundary. Every `Pars1Axioms` instance trivially yields a
    `StatedAxioms` instance (drop the Section III fields), but the
    converse fails — witnessed by the counter-models. -/
class StatedAxioms (Thing : Type u) [EthicaWorld Thing] : Prop where
  /-- A1: everything is in itself or in another. -/
  ax1_inItselfOrInAnother :
    ∀ x : Thing, inItself x ∨ inAnother x
  /-- A1ₑ: "in se" and "in alio" do not co-apply. -/
  ax1_exclusive :
    ∀ x : Thing, ¬ (inItself x ∧ inAnother x)
  /-- A2: what cannot be conceived through another is conceived
      through itself. -/
  ax2_perSeOrThroughAnother :
    ∀ x : Thing, perSeConceived x ∨ conceivedThroughAnother x
  /-- A3 placeholder (substantive form in `ModalForm.lean`). -/
  ax3_causationDeterminate : True
  /-- A4 placeholder (substantive form in `Causation.lean`). -/
  ax4_effectKnowledgeFromCause : True
  /-- A5 placeholder (substantive form in `Causation.lean`). -/
  ax5_nothingInCommonNoUnderstanding : True
  /-- A6 placeholder (idea/ideatum machinery is Pars II). -/
  ax6_trueIdeaAgreesWithIdeatum : True
  /-- A7: whatever is conceivable as non-existent has an essence not
      involving existence. -/
  ax7_conceivableAsNonExistent :
    ∀ x : Thing,
      ¬ natureRequiresExistence x → ¬ involvesExistence x
  /-- A8 (Section I): in-itself and per-se-conceived are coextensive. -/
  ax_inItself_iff_perSeConceived :
    ∀ x : Thing, inItself x ↔ perSeConceived x
  /-- A9 (Section I): in-another and conceived-through-another are
      coextensive. -/
  ax_inAnother_iff_conceivedThroughAnother :
    ∀ x : Thing, inAnother x ↔ conceivedThroughAnother x
  /-- A10 (Section I): every attribute of a substance is per se
      conceived (Spinoza Ip10). -/
  ax_attribute_perSe :
    ∀ a s : Thing, Attribute a s → perSeConceived a
  /-- A11 (Section I): the two clauses of Def. I are coextensive. -/
  ax_causaSui_iff :
    ∀ x : Thing, involvesExistence x ↔ natureRequiresExistence x

end Ethica.Pars1
