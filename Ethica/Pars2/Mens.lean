/-
  Spinoza, *Ethica* Pars II — the human-mind layer (Props. X–XIII).
  Batch 1.4.

  This is where Pars II stops being about God's idea in general and
  starts being about *us*. Four propositions, three corollaries, and
  the first appearance of `Homo` in the project.

  **Eight new axioms, and not one Section III commitment.** Five of
  them are Spinoza's **own five axioms of Pars II**, promoted from
  nothing (Pars I carried A1–A7; Pars II's axiomata had never been
  entered at all):

  | | Latin | Field |
  |---|---|---|
  | Ax. I | *Hominis essentia non involvit necessariam existentiam* | A60 |
  | Ax. II | *Homo cogitat* | A61 |
  | Ax. III | *Modi cogitandi … idea natura prior est* | A63 |
  | Ax. IV | *Nos corpus quoddam multis modis affici sentimus* | A64 |
  | Ax. V | *Nullas res singulares præter corpora et cogitandi modos sentimus* | — see below |

  Ax. V is **not** entered, and that is a result rather than an
  omission: the work Spinoza gives it — securing the "*et nihil
  aliud*" of Prop. XIII — is already done by A45 (an idea has at most
  one object). See `prop_2_13_objectumUnicum`. Spinoza argues the
  point empirically; on our reading of his Ax. VI it is analytic.

  The other three are A62 (Def. II applied to the mind), A65 and A66
  (the two halves of Prop. IX's corollary that batch 1.3 could state
  but not consume), and A67, a typing bridge.

  **Two definitions and no primitives for three notions.** Pars II's
  Def. I, Def. II, and Prop. XII's own gloss on "*percipi*" all turn
  out to be definable from machinery already paid for:

      Corpus b             ≝ modeUnder b extensio            (Def. I)
      pertinetAdEssentiam m x ≝ (durat m ↔ durat x)          (Def. II)
      percipit m a         ≝ ∃ i, ideaOf i a ∧ comprehensaIn i m

  The third is Spinoza's own gloss — "*id ab humana mente debet
  percipi **sive ejus rei dabitur in mente necessario idea***" — and
  it reuses batch 1.3's `comprehensaIn`, the containment relation
  built for Prop. VIII. Only three genuinely new primitives are
  introduced: `Homo`, `mensHominis`, `affectio`.

  **Every proposition in this batch is a derivation.** Prop. X falls
  out of Pars II Ax. I against Prop. I.VII; its corollary out of Prop.
  I.XXV cor.; Prop. XI out of Ax. II + Ax. III + **Prop. VIII's
  corollary**, which is exactly the step Spinoza cites ("*At non idea
  rei non existentis. Nam tum (per corollarium propositionis 8
  hujus)…*"); Prop. XII out of A66; Prop. XIII out of Ax. IV + A65,
  following the *demonstratio*'s reductio.
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
import Ethica.Pars2.Parallelismus

namespace Ethica.Pars2

open Ethica.Pars1
open Ethica.Attributum

universe u v

/-! ## Pars II's Def. I and Def. II, as definitions

  Neither needs a primitive. Def. I reads a body off `modeUnder`;
  Def. II reads essence-pertinence off `durat`. -/

section definitiones

variable {Thing : Type u} {Attr : Type v} [ParallelismusWorld Thing Attr]
open Pars2World QuatenusWorld ParallelismusWorld

/-- Pars II Def. I: *Per corpus intelligo modum qui Dei essentiam
    quatenus ut res extensa consideratur, certo et determinato modo
    exprimit.*

    "A mode expressing God's essence in so far as he is considered an
    extended thing" is, in the *quatenus* vocabulary, exactly
    `modeUnder b extensio`. Spinoza's cross-reference is to Prop.
    I.XXV cor., which is where `modeUnder` gets its content (A53,
    A67). No primitive needed. -/
def Corpus (b : Thing) : Prop := modeUnder b (extensio Thing)

/-- Pars II Def. II, first clause: *Ad essentiam alicujus rei id
    pertinere dico quo dato res necessario ponitur et quo sublato res
    necessario tollitur.*

    Given `m`, `x` is necessarily posited; `m` removed, `x` is
    necessarily removed. With `durat` (batch 1.3) for "is posited",
    that is a biconditional between the two things' actual existence.

    **What is not captured**: Def. II's second clause, the "*vel*"
    variant — "*id sine quo res et vice versa id quod sine re nec esse
    nec concipi potest*" — which is a claim about *conception*, not
    about existence. It would need the `conceivedThroughAnother`
    channel and a converse of it. Not committed; nothing in this batch
    consumes it. -/
def pertinetAdEssentiam (m x : Thing) : Prop := durat m ↔ durat x

/-- Perception, in Spinoza's own gloss.

    Prop. XII states the notion and immediately defines it: "*id ab
    humana mente debet percipi **sive ejus rei dabitur in mente
    necessario idea***" — to be perceived by a mind is for there to
    be, in that mind, an idea of the thing. `comprehensaIn` (batch
    1.3, built for Prop. VIII) is the in-an-idea relation, so this is
    a definition rather than a primitive. -/
def percipit (m a : Thing) : Prop :=
  ∃ i : Thing, ideaOf i a ∧ comprehensaIn i m

end definitiones

/-! ## The world -/

/-- The human-mind world: an *esse objectivum* world that can also say
    who is a man, which idea is whose mind, and what is an affection
    of what.

    Three primitives, and each earns its place.

    `Homo` is unavoidable: nothing in the register up to here
    distinguishes a man from any other finite mode, and Pars II's
    axioms are all about men.

    `mensHominis m h` ("`m` is the mind of `h`") is likewise not
    definable in advance. It is *tempting* to define the human mind as
    the idea of the human body — but that identification is Prop.
    XIII's **content**, and defining it away would turn the
    proposition into a tautology. Spinoza proves it; so do we.

    `affectio a b` ("`a` is an affection of `b`") is the relation
    Props. XII and XIII quantify over ("*quicquid in objecto …
    contingit*", "*ideas affectionum corporis habemus*") and the one
    the whole of Props. XIV–XXXI will consume. -/
class MensWorld (Thing : Type u) (Attr : outParam (Type v))
    extends ParallelismusWorld Thing Attr where
  /-- `Homo h` : `h` is a man. -/
  Homo : Thing → Prop
  /-- `mensHominis m h` : `m` is the mind of the man `h`. -/
  mensHominis : Thing → Thing → Prop
  /-- `affectio a b` : `a` is an affection of `b` — something that
      happens *in* `b`. -/
  affectio : Thing → Thing → Prop

section mens_axioms

variable {Thing : Type u} {Attr : Type v} [MensWorld Thing Attr]
open Pars2World QuatenusWorld ParallelismusWorld MensWorld

/-- The human-mind register: A60–A67.

    **Seven Section II and one Section I; no Section III.** Five of
    the eight are Spinoza's own axioms of Pars II, entered here for
    the first time. -/
class MensAxioms (Thing : Type u) (Attr : outParam (Type v))
    [MensWorld Thing Attr]
    extends ParallelismusAxioms Thing Attr : Prop where
  /-- A60 (Section II — **Pars II, Axioma I**): *Hominis essentia non
      involvit necessariam existentiam.*

      "The essence of man does not involve necessary existence" —
      that is, it may or may not be the case that this or that man
      exists. Rendered on `natureRequiresExistence`, which is the
      predicate Prop. I.VII's corollary
      (`prop_7_natureRequiresExistence`) establishes of substances.
      Setting the two side by side is precisely Prop. X's argument.

      This is the first of Spinoza's Pars II axioms to be entered.
      Pars I's register carried A1–A7 from the start; Pars II's five
      axiomata had never been entered at all, which is why Props.
      X–XIII could not be attempted before this batch. -/
  ax2_hominis_essentia_non_involvit_existentiam :
    ∀ h : Thing, Homo h → ¬ EthicaWorld.natureRequiresExistence h

  /-- A61 (Section II — **Pars II, Axioma II**): *Homo cogitat.*

      Two words in the Latin, and Spinoza offers no gloss. What Prop.
      XI's *demonstratio* uses it for is the claim that a man's
      essence is constituted by modes **of thinking** — so the
      minimal content is that a man has a mind at all. That is what
      is entered here; the "of thinking" half follows from A63 plus
      A54 rather than being assumed.

      Note that A46's docstring already flagged this axiom as the
      empirical premise Spinoza leans on for Prop. II.I, and declined
      to import it there. Here it is imported — but for its own
      proposition, and as the axiom Spinoza states rather than as a
      hidden step. -/
  ax2_homo_cogitat :
    ∀ h : Thing, Homo h → ∃ m : Thing, mensHominis m h

  /-- A62 (Section II — Pars II Def. II applied to the mind, via
      Prop. X cor.): a man's mind pertains to his essence.

      Prop. X's corollary establishes that a man's essence is
      constituted by modes; Ax. II says one of them is his mind;
      Def. II says what "pertains to the essence" means. Putting the
      three together gives `pertinetAdEssentiam m h`, i.e.
      `durat m ↔ durat h`.

      Spinoza does not write this sentence, which is why it is worth
      being explicit that it is a **composition** of three things he
      does write, not a quotation. It is Section II rather than III
      because each component is his and the composition is the one
      Prop. XI's *demonstratio* performs. -/
  ax_mens_pertinet_ad_essentiam :
    ∀ h m : Thing, Homo h → mensHominis m h → pertinetAdEssentiam m h

  /-- A63 (Section II — **Pars II, Axioma III**): the mind is an
      idea, and an idea of a singular thing.

      Spinoza: "*Modi cogitandi ut amor, cupiditas vel quicunque
      nomine affectus animi insigniuntur, non dantur nisi in eodem
      individuo detur idea rei amatæ, desideratæ etc. At idea potest
      dari quamvis nullus alius detur cogitandi modus.*" The axiom's
      content is the **priority of the idea** among modes of
      thinking: an idea can be given without any other mode of
      thinking, but no other mode of thinking without an idea. Prop.
      XI turns that priority into "the first thing constituting the
      mind is an idea".

      The `ResSingularis x` conjunct carries Prop. XI's "*rei
      alicujus singularis*". Spinoza gets it by excluding the
      infinite case ("*At non rei infinitæ. Res namque infinita … debet
      semper necessario existere; atqui hoc (per axioma 1 hujus) est
      absurdum*") — an argument that routes through Props. I.XXI and
      I.XXII in a form this formalisation does not have, so it is
      folded into the axiom rather than faked. Recorded rather than
      hidden.

      What is **not** folded in is actual existence: `durat x` is
      *derived* in `prop_2_11_mensEstIdeaReiSingularis`, from A62 and
      **A57** (Prop. VIII's corollary), which is exactly the step
      Spinoza cites. -/
  ax2_idea_natura_prior :
    ∀ h m : Thing, Homo h → mensHominis m h →
      ∃ x : Thing, ideaOf m x ∧ ResSingularis (Attr := Attr) x

  /-- A64 (Section II — **Pars II, Axioma IV**): *Nos corpus quoddam
      multis modis affici sentimus.*

      "We feel that a certain body is affected in many ways." The
      form entered is the one Prop. XIII's *demonstratio* consumes —
      "*atqui (per axioma 4 hujus) ideas affectionum corporis
      habemus*": the mind perceives an affection of some actually
      existing body.

      The plurality ("*multis modis*") is dropped: it is a claim
      about how many affections, and nothing in this batch counts
      them. One suffices for Prop. XIII. -/
  ax2_corpus_affici_sentimus :
    ∀ h m : Thing, Homo h → mensHominis m h →
      ∃ b a : Thing, Corpus (Attr := Attr) b ∧ durat b ∧
        affectio a b ∧ percipit m a

  /-- A65 (Section II — Prop. IX cor.'s *quatenus tantum*, exclusion
      half): a mind perceives affections of **its own object only**.

      Prop. IX's corollary reads "*ejus datur in Deo cognitio
      **quatenus tantum** ejusdem objecti ideam habet*" — God has the
      knowledge in so far only as he has the idea of *that* object.
      Batch 1.3 mechanised the positive half of that corollary and
      left the *quatenus tantum* out, because relativising God to an
      individual idea rather than to an attribute is exactly what
      **GAP-29** tracks as missing.

      This field is that exclusion, stated where it is used rather
      than where it is blocked: if a mind perceives an affection of
      `b`, then `b` is the mind's own object. It is Section II —
      Spinoza writes the sentence — and it is committed rather than
      derived only because GAP-29 is open. When GAP-29 closes, this
      should become a theorem. -/
  ax_mens_percipit_sui_objecti :
    ∀ h m x a b : Thing, Homo h → mensHominis m h → ideaOf m x →
      percipit m a → affectio a b → b = x

  /-- A66 (Section II — Prop. IX cor., positive half, in the
      containment register): the idea of an affection of `x` is
      comprehended in the idea of `x`.

      Prop. IX's corollary says the knowledge of whatever happens in
      an object is in God in so far as he has that object's idea.
      Batch 1.3 could state that only up to the *quatenus* clause
      (GAP-29 again). `comprehensaIn` gives the containment reading
      of "in so far as he has that object's idea": the idea of the
      affection sits **inside** the idea of the object.

      This is what makes Prop. XII a derivation rather than a
      commitment, and it is the only place in this batch where
      batch 1.3's `comprehensaIn` does load-bearing work outside
      Prop. VIII. -/
  ax_idea_affectionis_in_idea :
    ∀ a x i ix : Thing, affectio a x → ideaOf i a → ideaOf ix x →
      comprehensaIn i ix

  /-- A67 (Section I — definitional bridge): every mode is a mode of
      some attribute.

      Prop. I.XXV cor. reads particular things as "*Dei attributorum
      affectiones sive modi quibus Dei attributa certo et determinato
      modo exprimuntur*" — every mode expresses *some* attribute.
      Pars I mechanises the untyped half of that corollary
      (`prop_25_cor_everythingGodOrMode`: everything is God or a
      mode); this bridges it to the `Attr`-typed `modeUnder` the
      Attributum layer introduced.

      Section I rather than II: it makes no claim beyond the typing.
      Anything the untyped `Mode` predicate holds of, the typed one
      also holds of, for some attribute. It is the same kind of
      statement as A10′/A12′/A14′/A15′ in the Attributum layer. -/
  ax_mode_has_attribute :
    ∀ x : Thing, Mode x → ∃ a : Attr, modeUnder x a

end mens_axioms

section mens_theorems

variable {Thing : Type u} {Attr : Type v}
  [instW : MensWorld Thing Attr] [instAx : MensAxioms Thing Attr]
open Pars2World QuatenusWorld ParallelismusWorld MensWorld

/-! ## Propositio X

  Latin: *Ad essentiam hominis non pertinet esse substantiæ sive
         substantia formam hominis non constituit.*
  Elwes: "The being of substance does not appertain to the essence of
          man — in other words, substance does not constitute the
          actual being of man."

  Demonstratio: *Esse enim substantiæ involvit necessariam
  existentiam (per propositionem 7 partis I). Si igitur ad hominis
  essentiam pertineret esse substantiæ, data ergo substantia, daretur
  necessario homo et consequenter homo necessario existeret, quod (per
  axioma 1 hujus) est absurdum.*

  **What is mechanised**: the *sive* clause — substance does not
  constitute the being of man, i.e. no man is a substance. A genuine
  derivation, and it is Spinoza's argument with one step removed:
  Prop. I.VII's corollary (`prop_7_natureRequiresExistence`) says a
  substance's nature requires existence, Pars II Ax. I (A60) says a
  man's does not.

  **Not mechanised**: the *ad essentiam* form. "*Esse substantiæ*" —
  the being of substance — would have to be an object that
  `pertinetAdEssentiam` could take as an argument, and the language
  has no such object. Spinoza's own detour through Def. II ("*data
  ergo substantia, daretur necessario homo*") is what our shorter
  route avoids, at the cost of stating the weaker of the two forms
  he offers. He offers both, in the same sentence, as equivalent. -/

/-- Prop. II.X: no man is a substance. -/
theorem prop_2_10_substantiaNonConstituitHominem (h : Thing)
    (hh : Homo h) : ¬ Substance h := fun hs =>
  MensAxioms.ax2_hominis_essentia_non_involvit_existentiam (Attr := Attr) h hh
    (prop_7_natureRequiresExistence h hs)

/-! ### Corollarium to Prop. X

  Latin: *Hinc sequitur essentiam hominis constitui a certis Dei
  attributorum modificationibus.*

  Demonstratio: *Nam esse substantiæ (per propositionem præcedentem)
  ad essentiam hominis non pertinet. Est ergo (per propositionem 15
  partis I) aliquid quod in Deo est … sive (per corollarium
  propositionis 25 partis I) affectio sive modus qui Dei naturam certo
  et determinato modo exprimit.*

  **What is mechanised**: both clauses, both derived. That a man is a
  mode comes from Prop. X plus `prop_25_cor_everythingGodOrMode`
  (Prop. I.XXV cor., already in Pars I); that he is a mode *of an
  attribute* comes from A67, the typing bridge. Spinoza's route is
  the same, via the same two propositions. -/

/-- Prop. II.X cor.: a man is a mode, and a mode of some attribute of
    God. -/
theorem prop_2_10_cor_essentiaHominisModis (g : Thing) (hgod : IsGod g)
    (h : Thing) (hh : Homo h) :
    Mode h ∧ ∃ a : Attr, modeUnder h a := by
  have hmode : Mode h := by
    rcases prop_25_cor_everythingGodOrMode g hgod h with heq | hm
    · subst heq
      exact absurd hgod.1 (prop_2_10_substantiaNonConstituitHominem (Attr := Attr) h hh)
    · exact hm
  exact ⟨hmode, MensAxioms.ax_mode_has_attribute h hmode⟩

/-! ## Propositio XI

  Latin: *Primum quod actuale mentis humanæ esse constituit, nihil
         aliud est quam idea rei alicujus singularis actu existentis.*
  Elwes: "The first element, which constitutes the actual being of the
          human mind, is the idea of some particular thing actually
          existing."

  Demonstratio: *Essentia hominis (per corollarium præcedentis
  propositionis) a certis Dei attributorum modis constituitur nempe
  (per axioma 2 hujus) a modis cogitandi quorum omnium (per axioma 3
  hujus) idea natura prior est … Atque adeo idea primum est quod
  humanæ mentis esse constituit. At non idea rei non existentis. Nam
  tum (per corollarium propositionis 8 hujus) ipsa idea non potest
  dici existere; erit ergo idea rei actu existentis.*

  **What is mechanised**: the whole statement, and the actual-existence
  clause is a **derivation along Spinoza's own citation**. He gets
  "not the idea of a non-existent thing" from Prop. VIII's corollary;
  we get it from **A57**, which is Prop. VIII's corollary. A62 gives
  `durat m ↔ durat h`, so an existing man has an existing mind; A57
  gives `durat m ↔ durat x`, so that mind's object exists too.

  Batch 1.3's `durat` was introduced for Prop. VIII and is doing its
  second job here, in the proposition Spinoza wrote it for.

  **Folded into A63 rather than derived**: the "*rei alicujus
  singularis*" clause. Spinoza excludes the infinite case via Props.
  I.XXI and I.XXII plus Ax. I; those are mechanised only in the
  eternity/infinity vocabulary of `Consecutio.lean`, not in a form
  that connects to `ResSingularis`. See A63's docstring. -/

/-- Prop. II.XI: the mind of an actually existing man is the idea of
    a singular, actually existing thing. -/
theorem prop_2_11_mensEstIdeaReiSingularis (h m : Thing)
    (hh : Homo h) (hm : mensHominis m h) (hdur : durat h) :
    ∃ x : Thing, ideaOf m x ∧ ResSingularis (Attr := Attr) x ∧ durat x := by
  obtain ⟨x, hx, hsing⟩ :=
    MensAxioms.ax2_idea_natura_prior (Attr := Attr) h m hh hm
  have hmdur : durat m :=
    (MensAxioms.ax_mens_pertinet_ad_essentiam (Attr := Attr) h m hh hm).mpr hdur
  exact ⟨x, hx, hsing,
    (ParallelismusAxioms.ax_idea_durat_iff m x hx).mp hmdur⟩

/-! ### Corollarium to Prop. XI

  Latin: *Hinc sequitur mentem humanam partem esse infiniti intellectus
  Dei ac proinde cum dicimus mentem humanam hoc vel illud percipere,
  nihil aliud dicimus quam quod Deus … quatenus humanæ mentis
  essentiam constituit, hanc vel illam habet ideam.*

  **What is mechanised**: that the human mind is a mode of thought
  and is in God. Three derivations: A63 gives the mind an object,
  **A58** (batch 1.3) makes the mind itself a *res singularis* and so
  a mode, **A54** puts it under `cogitatio`, and `prop_15_allInGod`
  (Prop. I.XV) localises it — the same route Prop. II.III's
  localisation took in batch 1.2.

  **Not mechanised**: "*pars*". Spinoza says the mind is a **part**
  of God's infinite intellect, and this project does have a
  mereological layer (`Ethica/Pars1/Mereology.lean`, with
  `properPart`) — but `MereologyWorld` sits outside the Pars II class
  chain, and importing it would drag in A32, a Section III commitment
  about the indivisibility of substance, for the sake of one
  corollary. Tracked as **GAP-30**.

  Also not mechanised: the inadequacy clause of the corollary's
  second half ("*tum dicimus mentem humanam rem ex parte sive
  inadæquate percipere*"), which is the first appearance of
  adequacy — Def. IV's machinery, deferred to the cognition batch. -/

/-- Prop. II.XI cor. (partial): the human mind is a mode of thought,
    and it is in God. -/
theorem prop_2_11_cor_mensInDeo (g : Thing) (hgod : IsGod g)
    (h m : Thing) (hh : Homo h) (hm : mensHominis m h) :
    Mode m ∧ modeUnder m (cogitatio Thing) ∧
      (m = g ∨ InherenceWorld.inheresIn m g) := by
  obtain ⟨x, hx, hsing⟩ :=
    MensAxioms.ax2_idea_natura_prior (Attr := Attr) h m hh hm
  refine ⟨(ParallelismusAxioms.ax_idea_singularis m x hx hsing).1,
    QuatenusAxioms.ax_idea_modeUnder_cogitatio m x hx,
    prop_15_allInGod g hgod m⟩

/-! ## Propositio XII

  Latin: *Quicquid in objecto ideæ humanam mentem constituentis
         contingit, id ab humana mente debet percipi sive ejus rei
         dabitur in mente necessario idea; hoc est si objectum ideæ
         humanam mentem constituentis sit corpus, nihil in eo corpore
         poterit contingere quod a mente non percipiatur.*
  Elwes: "Whatsoever comes to pass in the object of the idea
          constituting the human mind must be perceived by the human
          mind."

  Demonstratio: *Quicquid enim in objecto cujuscunque ideæ contingit,
  ejus rei datur necessario in Deo cognitio (per corollarium
  propositionis 9 hujus) quatenus ejusdem objecti idea affectus
  consideratur hoc est (per propositionem 11 hujus) quatenus mentem
  alicujus rei constituit … hoc est (per corollarium propositionis 11
  hujus) ejus rei cognitio erit necessario in mente sive mens id
  percipit.*

  **What is mechanised**: the proposition, as a **derivation** —
  A49 gives the affection an idea, A66 puts that idea inside the idea
  of the object, and `percipit` is defined as exactly that
  containment. The *demonstratio*'s two citations are to Prop. IX cor.
  and Prop. XI cor.; A66 is the first of those in the containment
  register, and `percipit`'s definition is the second.

  **Not mechanised**: the exclusion the *demonstratio* passes through
  — that God has the knowledge *qua* constituting **this** mind and
  not another. That is the *quatenus* relativisation to an individual
  idea, GAP-29. A65 states its consequence where Prop. XIII needs it,
  rather than pretending the route is available. -/

/-- Prop. II.XII: whatever happens in the object of the idea
    constituting the human mind is perceived by that mind. -/
theorem prop_2_12_quicquidInObjectoPercipitur (h m x a : Thing)
    (_hh : Homo h) (_hm : mensHominis m h) (hx : ideaOf m x)
    (haff : affectio a x) : percipit m a := by
  obtain ⟨i, hi⟩ := prop_2_3_ideaOmnium (Attr := Attr) a
  exact ⟨i, hi, MensAxioms.ax_idea_affectionis_in_idea a x i m haff hi hx⟩

/-! ## Propositio XIII

  Latin: *Objectum ideæ humanam mentem constituentis est corpus sive
         certus extensionis modus actu existens et nihil aliud.*
  Elwes: "The object of the idea constituting the human mind is the
          body — in other words, a certain mode of extension which
          actually exists, and nothing else."

  Demonstratio: *Si enim corpus non esset humanæ mentis objectum, ideæ
  affectionum corporis non essent in Deo … quatenus mentem nostram sed
  quatenus alterius rei mentem constitueret … atqui (per axioma 4
  hujus) ideas affectionum corporis habemus. Ergo objectum ideæ
  humanam mentem constituentis est corpus idque (per propositionem 11
  hujus) actu existens. Deinde si præter corpus etiam aliud esset
  mentis objectum … (per axioma 5 hujus) nulla ejus idea datur.*

  **What is mechanised**: all three clauses, all derived.

  - *corpus*: Ax. IV (A64) says the mind perceives an affection of
    some actually existing body; A65 — the exclusion half of Prop. IX
    cor. — says the thing so affected must be the mind's own object.
    This is Spinoza's reductio, run forwards.
  - *actu existens*: comes with the body from A64. (Prop. XI supplies
    it independently, by the route above.)
  - *et nihil aliud*: **A45**. An idea has at most one object, so the
    mind — being one idea — has one object and no other.

  **The interesting bit is the third clause.** Spinoza argues it
  empirically, and it is the only work his Axioma V does: nothing
  exists without some effect (Prop. I.XXXVI), so a second object would
  give the mind an idea of that effect (Prop. XII), and "*atqui per
  axioma 5 nulla ejus idea datur*" — we perceive no singular things
  besides bodies and modes of thinking. On our reading of his Axioma
  VI (A45, an idea has a unique ideatum) the clause is **analytic**,
  and Axioma V is not needed at all. It is therefore not entered in
  the register. That is a small result about the *Ethica*'s own
  economy: one of Pars II's five axioms is redundant given another.
  See `prop_2_13_objectumUnicum`. -/

/-- Prop. II.XIII: the object of the idea constituting the human mind
    is an actually existing body. -/
theorem prop_2_13_objectumMentisEstCorpus (h m x : Thing)
    (hh : Homo h) (hm : mensHominis m h) (hx : ideaOf m x) :
    Corpus (Attr := Attr) x ∧ durat x := by
  obtain ⟨b, a, hcorp, hbdur, haff, hperc⟩ :=
    MensAxioms.ax2_corpus_affici_sentimus (Attr := Attr) h m hh hm
  have hbx : b = x :=
    MensAxioms.ax_mens_percipit_sui_objecti h m x a b hh hm hx hperc haff
  subst hbx
  exact ⟨hcorp, hbdur⟩

/-- Prop. II.XIII's "*et nihil aliud*": the mind has **one** object.

    Direct from A45. Spinoza reaches the same conclusion through Prop.
    I.XXXVI, Prop. XII and his Axioma V; on our reading of his Axioma
    VI it needs none of them — see the block comment above. -/
theorem prop_2_13_objectumUnicum (m x y : Thing)
    (hx : ideaOf m x) (hy : ideaOf m y) : x = y :=
  Pars2Axioms.ax6_idea_unique_ideatum (Attr := Attr) m x y hx hy

/-! ### Corollarium to Prop. XIII

  Latin: *Hinc sequitur hominem mente et corpore constare et corpus
  humanum prout ipsum sentimus existere.*

  **What is mechanised**: both clauses, as a package — a man has a
  mind, that mind is the idea of a body, and that body actually
  exists. Assembled from Ax. II (A61), A63 and Prop. XIII. -/

/-- Prop. II.XIII cor.: a man consists of a mind and a body, and the
    body actually exists. -/
theorem prop_2_13_cor_homoMenteEtCorpore (h : Thing) (hh : Homo h) :
    ∃ m b : Thing, mensHominis m h ∧ ideaOf m b ∧
      Corpus (Attr := Attr) b ∧ durat b := by
  obtain ⟨m, hm⟩ := MensAxioms.ax2_homo_cogitat (Attr := Attr) h hh
  obtain ⟨b, hb, _⟩ :=
    MensAxioms.ax2_idea_natura_prior (Attr := Attr) h m hh hm
  obtain ⟨hcorp, hdur⟩ :=
    prop_2_13_objectumMentisEstCorpus (Attr := Attr) h m b hh hm hb
  exact ⟨m, b, hm, hb, hcorp, hdur⟩

/-- The mind of an existing man is itself an existing idea of an
    existing body — Props. XI and XIII in one statement, which is the
    form Props. XIV onwards will consume. -/
theorem prop_2_13_mensEstIdeaCorporisExistentis (h m : Thing)
    (hh : Homo h) (hm : mensHominis m h) (hdur : durat h) :
    ∃ b : Thing, ideaOf m b ∧ Corpus (Attr := Attr) b ∧ durat b ∧
      ResSingularis (Attr := Attr) b ∧ durat m := by
  obtain ⟨b, hb, hsing, hbdur⟩ :=
    prop_2_11_mensEstIdeaReiSingularis (Attr := Attr) h m hh hm hdur
  obtain ⟨hcorp, _⟩ :=
    prop_2_13_objectumMentisEstCorpus (Attr := Attr) h m b hh hm hb
  exact ⟨b, hb, hcorp, hbdur, hsing,
    (MensAxioms.ax_mens_pertinet_ad_essentiam (Attr := Attr) h m hh hm).mpr hdur⟩

end mens_theorems

end Ethica.Pars2
