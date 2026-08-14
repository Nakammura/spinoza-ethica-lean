/-
  Spinoza, *Ethica* Pars II — the *esse objectivum* layer
  (Prop. VII cor., Props. VIII–IX). Batch 1.3.

  Batch 1.2 established that the order of ideas and the order of
  things coincide (`prop_2_7_ordoEtConnexio_iff`). This batch asks
  what that order *contains*: which ideas exist, what it is for an
  idea to exist, and what causes a particular idea. Spinoza's answers
  are Props. VIII and IX, and Prop. IX is the *idea ideae in
  infinitum* stated as doctrine — the very structure batch 1.2 found
  was already forced on any model by A45 + A49 + A54.

  **The blocker this batch had to clear first.** Pars I's Def. II is
  mechanised as

      finitumInSuoGenere x ≝ ∃ y, x ≠ y ∧ sameNature x y ∧ limitedBy x y

  and `sameNature` is, following Della Rocca (GAP-2 path (b)),
  `∃ a, Attribute a x ∧ Attribute a y` — where `Attribute a s` carries
  `Substance s`. So `finitumInSuoGenere x` **entails** `Substance x`,
  and since substances and modes are provably disjoint
  (`prop_1_substanceDisjointFromModes`), *no mode is ever
  finite-after-its-kind*. `pars1_prop_28_vacuous_for_modes` below
  proves this in Pars I's own vocabulary.

  The casualty is A42, whose docstring calls it "the backbone of
  finite-mode causation that Pars II–V consume throughout": its
  hypothesis `Mode x ∧ finitumInSuoGenere x` is unsatisfiable in
  *every* `Pars1Axioms` world. Prop. I.XXVIII is mechanised, but
  vacuously; and Prop. II.IX, whose *demonstratio* cites Prop. I.28
  by name, could not have been derived from it.

  `Definitions.lean` foresaw exactly this ("*For inter-mode or
  mode-vs-substance 'same kind' comparisons … a separate
  `hasAttribute` relation will be added at the modal layer*"), and
  `gaps.md`'s GAP-2 caveat records the promise. This batch keeps it.
  The *quatenus* layer already supplies the missing relation:
  `modeUnder x a` says which attribute a mode is a mode *of*. So

      sameNatureUnder x y ≝ ∃ a : Attr, modeUnder x a ∧ modeUnder y a

  is the mode-level counterpart of `sameNature`, and `ResSingularis`
  (Pars II Def. VII, *res singulares*) is Def. II rebuilt on it. The
  repair costs no primitive — only a definition over machinery batch
  1.2 already paid for.

  **What this batch mechanises**:

  - Prop. VII cor. — the *formaliter/objective* transfer, **derived**
    from A38 + Prop. VII (no new axiom)
  - Prop. VIII + cor. — the *esse objectivum* of non-existent singular
    things (A56, A57)
  - Prop. IX — the idea of a singular thing is caused by another idea,
    *et sic in infinitum*: a **genuine derivation** from A59 + A49 +
    A58 + Prop. VII + A45, mirroring Spinoza's own *demonstratio*
    step for step
  - Prop. IX cor. — partially (the *quatenus tantum ejusdem objecti
    ideam habet* fine-graining is GAP-29)

  **The accounting**: four new axioms, three of them Section II. The
  single Section III commitment is A59, and it is not new content —
  it is A42's content restated on a predicate that is not vacuous.
  The honest way to read this batch is: Pars I already paid for
  Prop. XXVIII, but paid into an account that could not be drawn on.
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
import Ethica.Pars2.Quatenus

namespace Ethica.Pars2

open Ethica.Pars1
open Ethica.Attributum

universe u v

/-! ## *Res singulares* — Def. II repaired at the modal layer

  Pars II Def. VII: *Per res singulares intelligo res quæ finitæ sunt
  et determinatam habent existentiam.* Spinoza's "*finitæ*" is Pars I
  Def. II, and Pars I Def. II needs a notion of *same nature* that
  applies to modes. The three definitions below supply it, entirely
  from batch 1.2's `modeUnder`; none of them is an axiom. -/

section singularia

variable {Thing : Type u} {Attr : Type v} [QuatenusWorld Thing Attr]
open QuatenusWorld

/-- `sameNatureUnder x y` : `x` and `y` are modes of a common
    attribute.

    The mode-level counterpart of `Ethica.Pars1.sameNature`, and the
    `hasAttribute` relation `Definitions.lean` promised "*at the modal
    layer*". Where `sameNature` routes through `Attribute a x`, which
    carries `Substance x` and so silently restricts the notion to
    substances, this routes through `modeUnder x a`, which carries
    nothing. Closes the GAP-2 caveat. -/
def sameNatureUnder (x y : Thing) : Prop :=
  ∃ a : Attr, modeUnder x a ∧ modeUnder y a

/-- Def. II, rebuilt: `x` can be limited by *another* thing of the
    same nature, where "same nature" is now `sameNatureUnder`.

    Identical in shape to `Ethica.Pars1.finitumInSuoGenere` — same
    `≠` clause, same `limitedBy` primitive — differing only in which
    sameness-of-nature relation it consumes. That single substitution
    is what makes the predicate satisfiable by modes. -/
def finitumInSuoGenereModal (x : Thing) : Prop :=
  ∃ y : Thing, x ≠ y ∧ sameNatureUnder (Attr := Attr) x y ∧
    EthicaWorld.limitedBy x y

/-- Pars II Def. VII: a *res singularis* is a finite mode.

    "*Res quæ finitæ sunt et determinatam habent existentiam*" — the
    finitude clause is `finitumInSuoGenereModal`; the modehood is
    Pars I Def. V. The "*determinatam habent existentiam*" clause is
    carried separately by `durat` (below), because Prop. VIII turns
    on singular things that are *not* currently existing, so
    singularity and duration must be able to come apart. -/
def ResSingularis (x : Thing) : Prop :=
  Mode x ∧ finitumInSuoGenereModal (Attr := Attr) x

end singularia

/-! ## The world -/

/-- The *esse objectivum* world: a *quatenus* world that can also say
    which things actually endure, where a formal essence is
    contained, and when one idea is comprehended in another.

    `durat` is Pars II Def. V (*Duratio est indefinita existendi
    continuatio*) taken as a predicate of actual existence — the
    distinction Prop. VIII's whole point rests on, between a singular
    thing as *contained in God's attributes* and the same thing as
    *enduring*.

    `essentiaFormalisIn x a` is "*rerum singularium essentiæ formales
    in Dei attributis continentur*", and it is `Thing → Attr → Prop`
    for the same reason `modeUnder` is: attributes were re-typed off
    the `Thing` universe in Fase 0.

    `comprehensaIn i j` is "*comprehendi in Dei infinita idea*" — the
    containment relation *between ideas*, which is not `inheresIn`
    (that relates a mode to its substance) and not `Cause`. Spinoza's
    Prop. VIII is precisely the claim that this third relation runs
    parallel to the second. -/
class ParallelismusWorld (Thing : Type u) (Attr : outParam (Type v))
    extends QuatenusWorld Thing Attr where
  /-- `durat x` : `x` actually exists — endures — as opposed to being
      merely contained in God's attributes (Pars II Def. V). -/
  durat : Thing → Prop
  /-- `essentiaFormalisIn x a` : the formal essence of `x` is
      contained in the attribute `a`. -/
  essentiaFormalisIn : Thing → Attr → Prop
  /-- `comprehensaIn i j` : the idea `i` is comprehended in the idea
      `j`. -/
  comprehensaIn : Thing → Thing → Prop

section parallelismus_axioms

variable {Thing : Type u} {Attr : Type v} [ParallelismusWorld Thing Attr]
open Pars2World QuatenusWorld ParallelismusWorld

/-- The *esse objectivum* register: A56–A59.

    Three Section II bridges and one Section III commitment (A59),
    and the Section III one is A42's content on a non-vacuous
    predicate rather than a fresh metaphysical claim. -/
class ParallelismusAxioms (Thing : Type u) (Attr : outParam (Type v))
    [ParallelismusWorld Thing Attr]
    extends QuatenusAxioms Thing Attr : Prop where
  /-- A56 (Section II — Prop. VIII, 📜): the ideas of non-existent
      singular things are comprehended in God's infinite idea exactly
      as those things' formal essences are contained in God's
      attributes.

      Spinoza: "*Ideæ rerum singularium sive modorum non existentium
      ita debent comprehendi in Dei infinita idea ac rerum
      singularium sive modorum essentiæ formales in Dei attributis
      continentur.*" The "*ita … ac*" is a comparison of manner, and
      the content it carries — the one the corollary then draws on —
      is that the two hold together. That is what this field says:
      for a singular thing that does not endure, its idea is
      comprehended in God's infinite idea **iff** its formal essence
      is contained in some attribute.

      It is Section II rather than Section III because Spinoza's own
      *demonstratio* is "*Hæc propositio patet ex præcedenti*" — it
      is offered as a restatement of Prop. VII in the register of
      containment, not as a new commitment. What is *not* claimed
      here is the manner-comparison itself ("in the same way as"),
      which would need a notion of sameness of manner this layer
      does not have.

      God's infinite idea is not a new primitive: it is the idea of
      God, which A49 guarantees exists. The `IsGod g` and `ideaOf ig
      g` hypotheses pick it out. -/
  ax_prop8_esseObjectivum :
    ∀ (x i ig g : Thing), ResSingularis (Attr := Attr) x → ¬ durat x →
      ideaOf i x → IsGod g → ideaOf ig g →
        (comprehensaIn i ig ↔ ∃ a : Attr, essentiaFormalisIn x a)

  /-- A57 (Section II — Prop. VIII cor.): an idea endures exactly
      when its object endures.

      Spinoza's corollary states both halves. Negatively: "*quamdiu
      res singulares non existunt nisi quatenus in Dei attributis
      comprehenduntur, earum esse objectivum sive ideæ non existunt
      nisi quatenus infinita Dei idea existit*". Positively: "*ubi
      res singulares dicuntur existere … earum ideæ etiam
      existentiam per quam durare dicuntur, involvent*". A
      biconditional is the compact form of the pair.

      Note what this does *not* say: nothing here makes `durat`
      interesting on its own. A model may have `durat` empty, or
      universal; A57 only ties the two sides together. The witness in
      `Models/MensWitness.lean` deliberately makes it split the
      carrier, so that Prop. VIII's hypothesis is met by some things
      and not others. -/
  ax_idea_durat_iff :
    ∀ i x : Thing, ideaOf i x → (durat i ↔ durat x)

  /-- A58 (Section II — Prop. IX's *demonstratio*, first sentence):
      the idea of a singular thing is itself a singular thing.

      Spinoza: "*Idea rei singularis actu existentis modus singularis
      cogitandi est et a reliquis distinctus.*" The modehood and the
      attribute are already available (A54 makes every idea a mode of
      thought); what is added here is the **finitude** — that the
      idea is limited by other ideas, hence a *res singularis* in the
      sense of `ResSingularis`. Without it the regress of Prop. IX
      could not stay inside the class of singular things, and A59
      could not be reapplied. -/
  ax_idea_singularis :
    ∀ i x : Thing, ideaOf i x → ResSingularis (Attr := Attr) x →
      ResSingularis (Attr := Attr) i

  /-- A59 (Section III — substantive metaphysical commitment,
      📜-pattern): every singular thing is caused by another,
      distinct singular thing.

      **This is A42 repaired, not A42 duplicated.** A42
      (`ax_finiteMode_causedByFiniteMode`) states exactly this claim
      using Pars I's `finitumInSuoGenere`, whose hypothesis
      `Mode x ∧ finitumInSuoGenere x` is unsatisfiable in every
      `Pars1Axioms` world — see `pars1_prop_28_vacuous_for_modes`
      below. So A42 commits Prop. I.XXVIII's content and delivers
      none of it. This field is the same commitment on
      `ResSingularis`, which modes can actually satisfy.

      Everything A42's docstring says about the *demonstratio*
      applies verbatim: Spinoza chains Props. XXI and XXII with the
      trichotomy of Prop. XXIII, which is not mechanised, so the
      conclusion is committed directly rather than routed through
      unavailable machinery.

      Why not simply strengthen A42? Because `Ethica/Pars1/` is
      frozen at v1.0.0 — the published irreducibility results are
      anchored to that register. The repair goes in the parallel
      branch, exactly as GAP-25's did. -/
  ax_singulare_causatum :
    ∀ x : Thing, ResSingularis (Attr := Attr) x →
      ∃ y : Thing, ResSingularis (Attr := Attr) y ∧ y ≠ x ∧
        CausalWorld.Cause y x

end parallelismus_axioms

section parallelismus_theorems

variable {Thing : Type u} {Attr : Type v}
  [instW : ParallelismusWorld Thing Attr] [instAx : ParallelismusAxioms Thing Attr]
open Pars2World QuatenusWorld ParallelismusWorld

/-! ## Propositio VII — Corollarium

  Latin: *Hinc sequitur quod Dei cogitandi potentia æqualis est
         ipsius actuali agendi potentiæ. Hoc est quicquid ex infinita
         Dei natura sequitur formaliter, id omne ex Dei idea eodem
         ordine eademque connexione sequitur in Deo objective.*
  Elwes: "Hence God's power of thinking is equal to his realized
          power of action — that is, whatsoever follows from the
          infinite nature of God in the world of extension, follows
          without exception in the same order and connection from the
          idea of God in the world of thought."

  **What is mechanised**: the "*hoc est*" clause, which is the one
  Spinoza actually uses downstream. Whatever follows formally from
  God, its idea stands to the idea of God in the corresponding causal
  relation. A **derivation**, costing no axiom: A38
  (`ax_consecution_causation`) turns consecution into causation, A49
  supplies the two ideas, and Prop. VII transfers the causal fact.

  **Not mechanised**: the first clause, the equality of God's power
  of thinking with his power of acting. That is a claim about
  *potentia*, the machinery that also blocks Props. I.XXXIV–XXXV and
  is deferred to the Pars V batch. There is no `power` primitive
  anywhere in this project, and inventing one to route a single
  corollary is exactly what A43's docstring declines to do. -/

/-- Prop. II.VII cor. (the *hoc est* clause): what follows formally
    from God, follows objectively from the idea of God.

    Derived — A38, then A49 twice, then `prop_2_7_ordoEtConnexio`. -/
theorem prop_2_7_cor_ordoObjectivus (g x : Thing)
    (hfollows : ConsecutioWorld.followsFrom x g) :
    ∃ ix ig : Thing, ideaOf ix x ∧ ideaOf ig g ∧ CausalWorld.Cause ig ix := by
  obtain ⟨ix, hix⟩ := prop_2_3_ideaOmnium (Attr := Attr) x
  obtain ⟨ig, hig⟩ := prop_2_3_ideaOmnium (Attr := Attr) g
  refine ⟨ix, ig, hix, hig, ?_⟩
  exact prop_2_7_ordoEtConnexio g x
    (ConsecutioAxioms.ax_consecution_causation x g hfollows) ig ix hig hix

/-! ## Propositio VIII

  Latin: *Ideæ rerum singularium sive modorum non existentium ita
         debent comprehendi in Dei infinita idea ac rerum singularium
         sive modorum essentiæ formales in Dei attributis
         continentur.*
  Elwes: "The ideas of particular things, or of modes, that do not
          exist, must be comprehended in the infinite idea of God, in
          the same way as the formal essences of particular things or
          modes are contained in the attributes of God."

  Demonstratio: *Hæc propositio patet ex præcedenti sed intelligitur
  clarius ex præcedenti scholio.*

  **What is mechanised**: the biconditional content — for a singular
  thing that does not endure, its idea is comprehended in God's
  infinite idea iff its formal essence is contained in an attribute.
  Direct invocation of A56.

  **Not mechanised**: the "*ita … ac*" as a comparison of *manner*.
  Spinoza's scholium illustrates it with the rectangles inscribed in
  a circle, and the force of the illustration is that the two
  containments are the same *kind* of containment. Capturing that
  would need a sameness-of-manner relation over the two containment
  predicates; it is not committed here. -/

/-- Prop. II.VIII: the idea of a non-enduring singular thing is
    comprehended in God's infinite idea exactly when that thing's
    formal essence is contained in an attribute. -/
theorem prop_2_8_ideaeRerumNonExistentium (g ig x i : Thing)
    (hgod : IsGod g) (hig : ideaOf ig g)
    (hx : ResSingularis (Attr := Attr) x) (hnd : ¬ durat x)
    (hi : ideaOf i x) :
    comprehensaIn i ig ↔ ∃ a : Attr, essentiaFormalisIn x a :=
  ParallelismusAxioms.ax_prop8_esseObjectivum x i ig g hx hnd hi hgod hig

/-! ### Corollarium to Prop. VIII

  Latin: *Hinc sequitur quod quamdiu res singulares non existunt nisi
  quatenus in Dei attributis comprehenduntur, earum esse objectivum
  sive ideæ non existunt nisi quatenus infinita Dei idea existit et
  ubi res singulares dicuntur existere … earum ideæ etiam existentiam
  per quam durare dicuntur, involvent.*

  **What is mechanised**: both halves, as the two directions of A57.
  An idea comes into and goes out of existence with its object. -/

/-- Prop. II.VIII cor.: an idea endures iff its object endures — the
    negative half ("as long as the thing does not exist, its idea
    does not") and the positive half ("when it is said to endure, its
    idea involves that existence") in one statement. -/
theorem prop_2_8_cor_esseObjectivum (i x : Thing) (hidea : ideaOf i x) :
    (durat i ↔ durat x) :=
  ParallelismusAxioms.ax_idea_durat_iff i x hidea

/-- The negative half, spelled out — the form the *demonstratio* of
    Prop. IX uses. -/
theorem prop_2_8_cor_nonExistente (i x : Thing) (hidea : ideaOf i x)
    (hnd : ¬ durat x) : ¬ durat i :=
  fun h => hnd ((prop_2_8_cor_esseObjectivum i x hidea).mp h)

/-! ## Propositio IX — *et sic in infinitum*

  Latin: *Idea rei singularis actu existentis Deum pro causa habet
         non quatenus infinitus est sed quatenus alia rei singularis
         actu existentis idea affectus consideratur cujus etiam Deus
         est causa quatenus alia tertia affectus est et sic in
         infinitum.*
  Elwes: "The idea of an individual thing actually existing has God
          for its cause, not in so far as he is infinite, but in so
          far as he is considered as affected by another idea of a
          thing actually existing, of which he is the cause, in so
          far as he is affected by a third idea, and so on to
          infinity."

  Demonstratio: *Idea rei singularis actu existentis modus singularis
  cogitandi est et a reliquis distinctus (per cor. et schol. prop. 8)
  adeoque (per prop. 6 hujus) Deum quatenus est tantum res cogitans,
  pro causa habet. At non (per prop. 28 partis I) quatenus est res
  absolute cogitans sed quatenus alio cogitandi modo affectus
  consideratur … Atqui ordo et connexio idearum (per prop. 7 hujus)
  idem est ac ordo et connexio causarum; ergo unius singularis ideæ
  alia idea … est causa.*

  **What is mechanised**: the whole of the propositional content, and
  it is a **derivation that follows the *demonstratio* step for
  step**:

  1. the idea of a singular thing is a singular mode of thought — A58
     plus A54;
  2. so God causes it *qua* thinking thing and under no other
     attribute — Prop. VI, via Prop. V
     (`prop_2_9_deusQuatenusCogitans`);
  3. but not *qua* absolutely thinking: Prop. I.XXVIII (here A59,
     the repaired form) gives the object another singular cause;
  4. A49 gives that cause an idea, and Prop. VII carries the causal
     fact across (`prop_2_9_ideaSingularisAbAliaIdea`);
  5. A45 makes the two ideas distinct, since their objects are.

  The "*et sic in infinitum*" is the corollary
  `prop_2_9_cor_nullaPrimaIdea`, exactly as Prop. I.XXVIII's
  iteration is `prop_28_cor_noFirstFiniteCause` rather than part of
  the proposition.

  **What is not mechanised**: the *quatenus … affectus* locution as a
  relativisation of God to a particular idea. We render "God, in so
  far as he is affected by idea `j`, causes `i`" by its extension —
  God causes `i` under thought alone, and `j` causes `i` — which is
  what the *demonstratio* actually uses. A primitive relativising God
  to an individual mode (rather than to an attribute, which
  `causeUnder` already does) would be needed for the locution itself.
  Tracked as GAP-29. -/

/-- Prop. II.IX, first half: God causes the idea of a singular thing
    *qua* thinking thing, and under no other attribute.

    Specialisation of Prop. V, whose `Mode i` hypothesis comes from
    A58. -/
theorem prop_2_9_deusQuatenusCogitans (g : Thing) (hgod : IsGod g)
    (i x : Thing) (hidea : ideaOf i x) (hx : ResSingularis (Attr := Attr) x) :
    causeUnder g i (cogitatio Thing) ∧
      ∀ b : Attr, b ≠ cogitatio Thing → ¬ causeUnder g i b :=
  prop_2_5_ideaeSubCogitatione g hgod i x hidea
    (ParallelismusAxioms.ax_idea_singularis i x hidea hx).1

/-- Prop. II.IX, second half — *non quatenus infinitus est sed
    quatenus alia idea affectus*: the idea of a singular thing has
    **another idea** for its cause, and that idea is itself the idea
    of a singular thing.

    Fully derived. A59 gives the object `x` another singular cause
    `y`; A49 gives `y` an idea `j`; A58 makes `j` singular; Prop. VII
    transfers `Cause y x` to `Cause j i`; A45 forces `j ≠ i` from
    `y ≠ x`. No step of this proof is a commitment. -/
theorem prop_2_9_ideaSingularisAbAliaIdea (i x : Thing)
    (hidea : ideaOf i x) (hx : ResSingularis (Attr := Attr) x) :
    ∃ j y : Thing,
      ResSingularis (Attr := Attr) y ∧ y ≠ x ∧ CausalWorld.Cause y x ∧
      ideaOf j y ∧ ResSingularis (Attr := Attr) j ∧ j ≠ i ∧
      CausalWorld.Cause j i := by
  obtain ⟨y, hy, hyne, hcause⟩ :=
    ParallelismusAxioms.ax_singulare_causatum (Attr := Attr) x hx
  obtain ⟨j, hj⟩ := prop_2_3_ideaOmnium (Attr := Attr) y
  refine ⟨j, y, hy, hyne, hcause, hj,
    ParallelismusAxioms.ax_idea_singularis j y hj hy, ?_, ?_⟩
  · intro hji
    exact hyne (Pars2Axioms.ax6_idea_unique_ideatum i y x (hji ▸ hj) hidea)
  · exact prop_2_7_ordoEtConnexio y x hcause j i hj hidea

/-- Prop. II.IX's "*et sic in infinitum*": there is no first idea of
    a singular thing — no singular idea whose every candidate
    singular cause fails to cause it.

    Same shape as `prop_28_cor_noFirstFiniteCause`, but with content:
    the hypothesis is satisfiable here, and it is refuted by
    `prop_2_9_ideaSingularisAbAliaIdea` rather than by an axiom
    applied to an empty class. -/
theorem prop_2_9_cor_nullaPrimaIdea :
    ¬ ∃ i x : Thing, ideaOf i x ∧ ResSingularis (Attr := Attr) x ∧
      ∀ j : Thing, ResSingularis (Attr := Attr) j → j ≠ i →
        ¬ CausalWorld.Cause j i := by
  rintro ⟨i, x, hidea, hx, hnone⟩
  obtain ⟨j, _, _, _, _, _, hjsing, hjne, hjc⟩ :=
    prop_2_9_ideaSingularisAbAliaIdea (Attr := Attr) i x hidea hx
  exact hnone j hjsing hjne hjc

/-! ### Corollarium to Prop. IX

  Latin: *Quicquid in singulari cujuscunque ideæ objecto contingit,
  ejus datur in Deo cognitio quatenus tantum ejusdem objecti ideam
  habet.*
  Elwes: "Whatsoever takes place in the individual object of any
          idea, the knowledge thereof is in God, in so far only as he
          has the idea of the object."

  **What is mechanised**: that the knowledge is in God, and that God
  holds it *under thought alone*. The localisation is Prop. II.III's
  (`prop_2_3_ideaInDeo`, itself derived from Prop. I.XV); the
  exclusion is Prop. V's.

  **Not mechanised**: "*quatenus tantum ejusdem objecti ideam
  habet*" — that God has it in so far as he has *that particular*
  idea. As with Prop. IX's main clause, this needs God relativised to
  an individual mode rather than to an attribute. GAP-29. -/

/-- Prop. II.IX cor. (partial): whatever happens in a singular
    object, God has an idea of it, that idea is in God, and God
    causes it under thought alone. -/
theorem prop_2_9_cor_cognitioInDeo (g : Thing) (hgod : IsGod g)
    (x : Thing) (hx : ResSingularis (Attr := Attr) x) :
    ∃ i : Thing, ideaOf i x ∧ (i = g ∨ InherenceWorld.inheresIn i g) ∧
      causeUnder g i (cogitatio Thing) ∧
      ∀ b : Attr, b ≠ cogitatio Thing → ¬ causeUnder g i b := by
  obtain ⟨i, hi, hloc⟩ := prop_2_3_ideaInDeo (Attr := Attr) g hgod x
  exact ⟨i, hi, hloc, prop_2_9_deusQuatenusCogitans g hgod i x hi hx⟩

end parallelismus_theorems

/-! ## Why the repair was necessary — Pars I's finitude is
     substance-only

  The two theorems below are stated entirely in **Pars I's**
  vocabulary and use only Pars I's register. Together they show that
  `finitumInSuoGenere` cannot hold of a mode, so A42's hypothesis is
  never met and Prop. I.XXVIII, though mechanised, is vacuous.

  This is not a defect of Spinoza's Def. II. It is a consequence of
  GAP-2's resolution path (b), which *defined* `sameNature` through
  `Attribute` — a good move for Prop. II, whose whole subject is
  substances, and one whose cost `Definitions.lean` flagged in the
  same breath. The cost falls due here.

  Compare `pars2_props_1_2_collapse_under_pars1_typing` in
  `Idea.lean`: same idiom, same purpose — record what the frozen
  register does and does not deliver, in its own terms, rather than
  quietly working around it. -/

section pars1_finitude

variable {Thing : Type u} [EthicaWorld Thing]

/-- Anything finite-after-its-kind is a substance.

    Purely definitional, no axioms used: `finitumInSuoGenere` unfolds
    to a `sameNature`, `sameNature` to a pair of `Attribute`s, and
    `Attribute a x` carries `Substance x` by Def. IV. -/
theorem finitumInSuoGenere_implies_substance (x : Thing)
    (h : finitumInSuoGenere x) : Substance x := by
  obtain ⟨_, _, ⟨_, hax, _⟩, _⟩ := h
  exact hax.1

variable [Pars1Axioms Thing]

/-- **No mode is finite-after-its-kind.** Def. II, as mechanised in
    Pars I, cannot apply to a single one of the modes Spinoza uses it
    of. -/
theorem pars1_mode_not_finitum (x : Thing) (hmode : Mode x) :
    ¬ finitumInSuoGenere x := fun h =>
  prop_1_substanceDisjointFromModes x
    (finitumInSuoGenere_implies_substance x h) hmode

/-- **A42's hypothesis is unsatisfiable**, hence Prop. I.XXVIII is
    mechanised vacuously in the Pars I register.

    A42's own docstring calls it "the backbone of finite-mode
    causation that Pars II–V consume throughout". It is not usable as
    such: no world satisfying `Pars1Axioms` contains a finite mode,
    so the axiom never fires. A59 above is the repair. -/
theorem pars1_prop_28_vacuous_for_modes :
    ¬ ∃ x : Thing, Mode x ∧ finitumInSuoGenere x := by
  rintro ⟨x, hmode, hfin⟩
  exact pars1_mode_not_finitum x hmode hfin

end pars1_finitude

end Ethica.Pars2
