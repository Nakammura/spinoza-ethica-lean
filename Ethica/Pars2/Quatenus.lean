/-
  Spinoza, *Ethica* Pars II — the *quatenus* layer (Props. V, VI).
  Batch 1.2.

  Props. V and VI both turn on a construction Pars I never needed:
  causation **relativised to an attribute**. Spinoza's phrase is
  "*Deum quatenus tantum ut res cogitans consideratur*" — God *insofar
  as* he is considered a thinking thing — and the force of both
  propositions lies in the exclusion clause, "*et non quatenus alio
  attributo explicatur*".

  Three new primitives carry it: `modeUnder x a` (`x` is a mode of
  attribute `a`), `causeUnder c e a` (`c` causes `e` insofar as
  considered under `a`), and `involvesConceptOf x a` (`x` involves
  the concept of `a`). None is definable from what came before —
  attribute-relativised causation is a genuinely ternary relation,
  the same shape GAP-22 flagged as missing when A41 had to flatten
  Prop. I.XXII's ternary statement to a binary `followsFrom`.

  **What is derived rather than committed.** Prop. VI's structure in
  Spinoza is: each attribute is conceived through itself (Prop.
  I.10); hence the modes of an attribute involve the concept of
  their own attribute and not of another; hence (Ax. I.4) they have
  God for cause only under that attribute. The middle sentence is
  A51 and the inference step is A52 — both Section II, both stated
  by Spinoza in the *demonstratio* itself. Given them, **the
  exclusion clause is a genuine derivation**, and so is the positive
  clause, which comes from `prop_16_cor1_godEfficientCause` (Prop.
  I.16 cor. I, already mechanised) refined by A53.

  So Props. V and VI cost **no new Section III commitment**. That is
  unusual in this project and worth recording: the *quatenus*
  machinery is expensive in primitives and cheap in metaphysics.

  Prop. V is then a specialisation of Prop. VI to ideas, via A54
  (ideas are modes of thought) — exactly Spinoza's own second
  *demonstratio*, which routes Prop. V through Prop. I.10 and Ax.
  I.4 in the same way Prop. VI does.

  A55 additionally closes half of GAP-27: the **converse** direction
  of the parallelism, licensed by Spinoza's own "*idem est*". The
  identity reading proper (the scholium's "*una eademque res sed
  duobus modis expressa*") remains open as GAP-27b.
-/
import Ethica.Pars1.Definitions
import Ethica.Pars1.Axioms
import Ethica.Pars1.Causation
import Ethica.Pars1.Propositions
import Ethica.Pars1.Inherence
import Ethica.Pars1.Consecutio
import Ethica.Attributum.Core
import Ethica.Attributum.Axioms
import Ethica.Pars2.Idea

namespace Ethica.Pars2

open Ethica.Pars1
open Ethica.Pars1.EthicaWorld
open Ethica.Attributum

universe u v

/-- The *quatenus* world: a Pars II world with attribute-relativised
    modehood, causation and conception.

    All three primitives are ternary-in-spirit — they relativise a
    notion to an attribute — which is precisely what Pars I could not
    express. `Ethica/Pars1/Consecutio.lean`'s A41 had to flatten
    Prop. I.XXII's genuinely ternary statement ("*ex aliquo Dei
    attributo quatenus modificatum*") into a binary `followsFrom` for
    exactly this reason; GAP-22 tracks that flattening. This layer
    supplies the missing shape. -/
class QuatenusWorld (Thing : Type u) (Attr : outParam (Type v))
    extends Pars2World Thing Attr where
  /-- `modeUnder x a` : `x` is a mode *of the attribute* `a`
      ("*cujuscunque attributi modi*"). -/
  modeUnder : Thing → Attr → Prop
  /-- `causeUnder c e a` : `c` is the cause of `e` *insofar as* `c` is
      considered under the attribute `a` ("*quatenus … sub illo
      attributo … consideratur*"). -/
  causeUnder : Thing → Thing → Attr → Prop
  /-- `involvesConceptOf x a` : the concept of `x` involves the
      concept of the attribute `a` ("*conceptum sui attributi …
      involvunt*"). -/
  involvesConceptOf : Thing → Attr → Prop

section quatenus_axioms

variable {Thing : Type u} {Attr : Type v} [QuatenusWorld Thing Attr]
open Pars2World QuatenusWorld

/-- The *quatenus* axiom register. Five bridges, **all Section II** —
    each is a sentence Spinoza states in the relevant
    *demonstratio*, promoted to usable content, not a reconstruction
    of a missing step. No Section III commitment is added by this
    batch. -/
class QuatenusAxioms (Thing : Type u) (Attr : outParam (Type v))
    [QuatenusWorld Thing Attr]
    extends Pars2Axioms Thing Attr : Prop where
  /-- A51 (Section II — Prop. VI's *demonstratio*, second sentence):
      the modes of an attribute involve the concept of *their own*
      attribute and of no other.

      Spinoza: "*uniuscujusque attributi modi conceptum sui
      attributi, non autem alterius involvunt*". The two clauses are
      one sentence in the Latin and are kept as one conjunctive field
      here. The first clause is what Prop. I.10 (each attribute
      conceived through itself) extends to modes; the second is the
      exclusion that gives Props. V and VI their whole force. -/
  ax_modeUnder_conceptum :
    ∀ (x : Thing) (a : Attr), modeUnder x a →
      involvesConceptOf x a ∧ ∀ b : Attr, b ≠ a → ¬ involvesConceptOf x b

  /-- A52 (Section II — Axiom I.4, relativised): what is caused under
      an attribute involves the concept of that attribute.

      Spinoza closes both *demonstrationes* with "*per axioma 4
      partis I*" — knowledge of an effect involves knowledge of its
      cause. A4ₛ (`ax4_effectIntelligibleThroughCause`) states that
      for the binary `Cause`/`intelligibleThrough` pair; this is the
      attribute-relativised form the *quatenus* clause needs, and it
      is the direction Spinoza actually uses (from cause-under to
      concept-involvement, so that the *absence* of the concept rules
      out the causal claim). -/
  ax_causeUnder_involvesConcept :
    ∀ (c e : Thing) (a : Attr), causeUnder c e a → involvesConceptOf e a

  /-- A53 (Section II — Prop. I.25cor, relativised): God's causation
      of a mode is causation *under* that mode's own attribute.

      Prop. I.25's corollary reads particular things as "*Dei
      attributorum affectiones sive modi quibus Dei attributa certo
      et determinato modo exprimuntur*" — modes express a definite
      attribute. Combined with `prop_16_cor1_godEfficientCause` (God
      is efficient cause of every mode), this refines the bare causal
      claim into the *quatenus* form. It adds relativisation, not
      causation: the causal fact itself is already a Pars I
      theorem. -/
  ax_cause_refines_to_attribute :
    ∀ (g x : Thing) (a : Attr),
      CausalWorld.Cause g x → modeUnder x a → causeUnder g x a

  /-- A54 (Section II — Prop. V, first *demonstratio*): ideas are
      modes of thought.

      Spinoza: "*Esse formale idearum modus est cogitandi (ut per se
      notum)*" — that the formal being of an idea is a mode of
      thinking is, he says, self-evident. We record it as the bridge
      it is. This is what turns Prop. VI into Prop. V. -/
  ax_idea_modeUnder_cogitatio :
    ∀ i x : Thing, ideaOf i x → modeUnder i (cogitatio Thing)

  /-- A55 (Section II — Prop. VII's "*idem est*"): the causal order
      among ideas transfers *back* to things.

      A50 (`Pars2Axioms`) carries the order from things to ideas,
      which is the direction Prop. VII's *demonstratio* establishes.
      But Spinoza's statement is an identity — "*ordo et connexio
      idearum **idem est ac** ordo et connexio rerum*" — and an
      identity is symmetric. This axiom is the other direction, and
      together with A50 it delivers the biconditional
      `prop_2_7_ordoEtConnexio_iff` below. Closes GAP-27a.

      **What this still does not give** is the scholium's stronger
      identity claim, that a mode of extension and its idea are "*una
      eademque res sed duobus modis expressa*" — one and the same
      *thing*, not two things in matching orders. That needs
      cross-attribute identity of modes and remains GAP-27b. -/
  ax_idea_order_reflects :
    ∀ ic ie : Thing, CausalWorld.Cause ic ie →
      ∀ c e : Thing, ideaOf ic c → ideaOf ie e → CausalWorld.Cause c e

end quatenus_axioms

section quatenus_theorems

variable {Thing : Type u} {Attr : Type v}
  [instW : QuatenusWorld Thing Attr] [instAx : QuatenusAxioms Thing Attr]
open Pars2World QuatenusWorld

/-! ## Propositio VI

  Latin: *Cujuscunque attributi modi Deum quatenus tantum sub illo
         attributo cujus modi sunt et non quatenus sub ullo alio
         consideratur, pro causa habent.*
  Elwes: "The modes of any given attribute are caused by God, in so
          far as he is considered through the attribute of which they
          are modes, and not in so far as he is considered through
          any other attribute."

  Demonstratio: *Unumquodque enim attributum per se absque alio
  concipitur (per propositionem 10 partis I). Quare uniuscujusque
  attributi modi conceptum sui attributi, non autem alterius
  involvunt adeoque (per axioma 4 partis I) Deum quatenus tantum sub
  illo attributo cujus modi sunt … pro causa habent.*

  **What is mechanised**: both clauses, and both are derivations.

  - *positive clause*: God causes the mode under its own attribute —
    `prop_16_cor1_godEfficientCause` (Prop. I.16 cor. I) supplies the
    causal fact, A53 relativises it.
  - *exclusion clause*: God does not cause it under any other
    attribute — A51's second conjunct denies the mode the concept of
    any other attribute, and A52 says causation-under would require
    exactly that concept. The contradiction is the proof.

  No Section III commitment is used. -/

/-- Prop. II.VI: the modes of an attribute have God as cause under
    that attribute, **and under no other**.

    Both clauses derived; see the block comment above. -/
theorem prop_2_6_modiSubSuoAttributo (g : Thing) (hgod : IsGod g)
    (x : Thing) (hmode : Mode x) (a : Attr) (hxa : modeUnder x a) :
    causeUnder g x a ∧ ∀ b : Attr, b ≠ a → ¬ causeUnder g x b := by
  refine ⟨?_, ?_⟩
  · exact QuatenusAxioms.ax_cause_refines_to_attribute g x a
      (prop_16_cor1_godEfficientCause g hgod x hmode) hxa
  · intro b hb hcu
    exact (QuatenusAxioms.ax_modeUnder_conceptum x a hxa).2 b hb
      (QuatenusAxioms.ax_causeUnder_involvesConcept g x b hcu)

/-! ### Corollarium to Prop. VI

  Latin: *Hinc sequitur quod esse formale rerum quæ modi non sunt
  cogitandi, non sequitur ideo ex divina natura quia res prius
  cognovit …*

  **What is mechanised**: the negative half — a mode belonging to an
  attribute other than thought is *not* caused by God qua thinking
  thing, so its being does not flow from God's prior cognition of it.
  This is a direct specialisation of Prop. VI's exclusion clause.

  **Not mechanised**: the positive half's comparative claim ("*eodem
  modo eademque necessitate*" — ideata follow from their attributes
  in the same way ideas follow from thought), which is a statement
  about the *manner* of following and needs the identity reading
  (GAP-27b). -/

/-- Prop. II.VI cor.: what is not a mode of thought is not caused by
    God *qua* thinking thing. Immediate from Prop. VI's exclusion
    clause. -/
theorem prop_2_6_cor_nonPerCogitationem (g : Thing) (hgod : IsGod g)
    (x : Thing) (hmode : Mode x) (a : Attr) (hxa : modeUnder x a)
    (hne : a ≠ cogitatio Thing) : ¬ causeUnder g x (cogitatio Thing) :=
  (prop_2_6_modiSubSuoAttributo g hgod x hmode a hxa).2
    (cogitatio Thing) (Ne.symm hne)

/-! ## Propositio V

  Latin: *Esse formale idearum Deum quatenus tantum ut res cogitans
         consideratur, pro causa agnoscit et non quatenus alio
         attributo explicatur.*
  Elwes: "The actual being of ideas owns God as its cause, only in so
          far as he is considered as a thinking thing, not in so far
          as he is unfolded in any other attribute."

  **What is mechanised**: the proposition's main clause, in both its
  positive and exclusion halves — as a **specialisation of Prop. VI**
  to `a := cogitatio`, licensed by A54 (ideas are modes of thought).
  This mirrors Spinoza's own second *demonstratio*, which runs Prop.
  V through Prop. I.10 and Ax. I.4 exactly as Prop. VI does.

  **Not mechanised**: the *hoc est* gloss — that ideas do not have
  their own *ideata* as efficient cause. That is a claim about the
  ideatum rather than about the attribute, and needs a principle
  ruling out mode-to-mode causation across attributes which this
  layer does not commit. Tracked as GAP-28. -/

/-- Prop. II.V: the formal being of ideas has God as cause *qua*
    thinking thing, and under no other attribute.

    Specialisation of Prop. VI via A54. -/
theorem prop_2_5_ideaeSubCogitatione (g : Thing) (hgod : IsGod g)
    (i x : Thing) (hidea : ideaOf i x) (hmode : Mode i) :
    causeUnder g i (cogitatio Thing) ∧
      ∀ b : Attr, b ≠ cogitatio Thing → ¬ causeUnder g i b :=
  prop_2_6_modiSubSuoAttributo g hgod i hmode (cogitatio Thing)
    (QuatenusAxioms.ax_idea_modeUnder_cogitatio i x hidea)

/-- Prop. II.V, exclusion half applied to extension: ideas are not
    caused by God *qua* extended thing — provided extension is not
    thought, which A48 guarantees. -/
theorem prop_2_5_cor_nonSubExtensione (g : Thing) (hgod : IsGod g)
    (i x : Thing) (hidea : ideaOf i x) (hmode : Mode i) :
    ¬ causeUnder g i (extensio Thing) :=
  (prop_2_5_ideaeSubCogitatione g hgod i x hidea hmode).2
    (extensio Thing) (Ne.symm Pars2Axioms.ax_cogitatio_ne_extensio)

/-! ## Propositio VII, completed — GAP-27a closed

  A50 gave the transfer from the order of things to the order of
  ideas; A55 gives it back. Together they deliver the biconditional
  Spinoza's "*idem est*" asserts. -/

/-- Prop. II.VII (biconditional form): the causal order among things
    and the causal order among their ideas coincide.

    Forward: `prop_2_7_ordoEtConnexio` (A4ₛ + A50). Backward: A55.
    Closes GAP-27a; the scholium's identity reading remains
    GAP-27b. -/
theorem prop_2_7_ordoEtConnexio_iff (c e ic ie : Thing)
    (hic : ideaOf ic c) (hie : ideaOf ie e) :
    CausalWorld.Cause c e ↔ CausalWorld.Cause ic ie :=
  ⟨fun h => prop_2_7_ordoEtConnexio c e h ic ie hic hie,
   fun h => QuatenusAxioms.ax_idea_order_reflects ic ie h c e hic hie⟩

end quatenus_theorems

end Ethica.Pars2
