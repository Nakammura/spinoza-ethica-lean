/-
  Spinoza, *Ethica* Pars II — the composite-body layer (Props. XIV,
  XV, XVI + cor. I), and the closure of GAP-30. Batch 1.5.

  Props. XV and XVI are the first propositions in Pars II whose
  *demonstrationes* cite the **physical digression** — the lemmata,
  axiomata and postulata Spinoza inserts after Prop. XIII. Two of
  those enter the register here: Postulatum I (the human body is
  composed of many individuals) and the Axioma I that follows Lemma
  III's corollary (*Omnes modi quibus corpus aliquod ab alio afficitur
  ab alio, ex natura corporis affecti et simul ex natura corporis
  afficientis sequuntur*).

  **GAP-30 closes here, and it costs one axiom rather than a
  register.** Prop. XI's corollary says the human mind is a *part* of
  God's infinite intellect. Batch 1.4 could not say "part" at all:
  `Ethica/Pars1/Mereology.lean` has `properPart`, but `MereologyWorld`
  sat outside the Pars II class chain, and importing it looked like it
  meant importing `MereologyAxioms` with its Section III commitment
  A32 (a proper part of a substance is itself a substance).

  That was the wrong reading of the obstacle. `MereologyWorld` is a
  **data** class; `MereologyAxioms` is a separate `Prop` class. Taking
  the first without the second is exactly GAP-30's resolution path
  (b), and it costs nothing:

      class CorpusWorld … extends MensWorld Thing Attr, MereologyWorld Thing

  A32 is not imported, `prop_12_substanceIndivisible` is not in scope,
  and `properPart` is. The diamond through `EthicaWorld` resolves the
  same way `Pars2World`'s did, by `Attr` being an `outParam`.

  **What `properPart` immediately buys.** Prop. XV — the mind is not
  simple but composed of many ideas — becomes a two-step derivation
  ending in `Divisible m`, reusing the predicate `Mereology.lean`
  already defines. And Prop. XI's corollary gets its missing clause
  (A72).

  **A note on two senses of *affectio*.** Pars I Def. V reads modes as
  "*substantiæ affectiones*", which invites the bridge `Mode x →
  affectio x g`. That bridge is **inconsistent with A65** (a mind
  perceives affections of its own object only): if every mode were an
  affection of God, then any affection a mind perceives would witness
  God as its object. So the `affectio` of Props. XII–XVI is *not* Def.
  V's *affectio substantiæ*, and the register now proves that they
  cannot be identified. Recorded in `gaps.md` under GAP-30's closure
  note rather than as a new gap, since nothing needs the identification.
-/
import Ethica.Pars1.Definitions
import Ethica.Pars1.Axioms
import Ethica.Pars1.Causation
import Ethica.Pars1.Propositions
import Ethica.Pars1.Inherence
import Ethica.Pars1.Consecutio
import Ethica.Pars1.Mereology
import Ethica.Attributum.Core
import Ethica.Attributum.Axioms
import Ethica.Pars2.Idea
import Ethica.Pars2.Quatenus
import Ethica.Pars2.Parallelismus
import Ethica.Pars2.Mens

namespace Ethica.Pars2

open Ethica.Pars1
open Ethica.Attributum

universe u v

/-- The composite-body world: a human-mind world that can also speak
    of parts and of one thing involving another's nature.

    `MereologyWorld Thing` is taken as a **data** parent only.
    `MereologyAxioms` — and with it A32 — is deliberately left out:
    nothing in Pars II needs the indivisibility of substance, and
    paying a Section III axiom to obtain a relation would be the trade
    A43's docstring declines. See GAP-30.

    `involvitNaturam x y` is the one new primitive: "`x` involves the
    nature of `y`". Spinoza uses it of modes ("*modi … ex natura
    corporis affecti … sequuntur*") and of their ideas ("*eorum idea
    … utriusque corporis naturam necessario involvet*"), which is why
    it relates two `Thing`s rather than being restricted to ideas. -/
class CorpusWorld (Thing : Type u) (Attr : outParam (Type v))
    extends MensWorld Thing Attr, MereologyWorld Thing where
  /-- `involvitNaturam x y` : `x` involves the nature of `y`. -/
  involvitNaturam : Thing → Thing → Prop

section corpus_axioms

variable {Thing : Type u} {Attr : Type v} [CorpusWorld Thing Attr]
open Pars2World QuatenusWorld ParallelismusWorld MensWorld CorpusWorld

/-- The composite-body register: A68–A72. **All Section II**, and
    three of the five are sentences from the physical digression that
    Props. XIV–XVI cite by name. -/
class CorpusAxioms (Thing : Type u) (Attr : outParam (Type v))
    [CorpusWorld Thing Attr]
    extends MensAxioms Thing Attr : Prop where
  /-- A68 (Section II — **Pars II, the Axioma I after Lemma III's
      corollary**): *Omnes modi quibus corpus aliquod ab alio
      afficitur corpore, ex natura corporis affecti et simul ex natura
      corporis afficientis sequuntur.*

      Every mode by which one body is affected by another follows from
      the nature of the affected body **and** the nature of the
      affecting one. This is the first axiom of the physical
      digression to enter the register, and Prop. XVI cites it by
      name ("*per axioma 1 post corollarium lemmatis 3*").

      "Follows from the nature of" is rendered as `involvitNaturam`
      rather than as `followsFrom`: Spinoza's *sequuntur* here is a
      claim about what the affection's nature contains, and the
      consecution relation of `Consecutio.lean` is the God-to-mode one
      A37/A38 govern. Keeping them apart avoids importing the
      Pars I consecution machinery into a physical claim.

      The clause dropped is the *ita ut* tail (one body moves
      differently according to the diversity of the moving bodies),
      which is a claim about variation and needs the counting
      framework GAP-8a tracks. -/
  ax2_affectio_ex_utraque_natura :
    ∀ a b e : Thing, affectio a b → CausalWorld.Cause e a →
      involvitNaturam a b ∧ involvitNaturam a e

  /-- A69 (Section II — Prop. XVI's *demonstratio*, via Ax. I.4): what
      a thing involves, its idea involves.

      Spinoza's step is "*quare eorum idea (per axioma 4 partis I)
      utriusque corporis naturam necessario involvet*" — the idea of
      the affection involves both natures **because** knowledge of an
      effect involves knowledge of its cause. A4ₛ
      (`ax4_effectIntelligibleThroughCause`) states that for the
      `Cause`/`intelligibleThrough` pair; this is the nature-involving
      form the *demonstratio* uses.

      It is a transfer principle, not a new content claim: whatever
      natures a thing involves, its idea involves the same ones. -/
  ax_idea_involvit_naturam :
    ∀ x y i : Thing, involvitNaturam x y → ideaOf i x → involvitNaturam i y

  /-- A70 (Section II — **Pars II, Postulatum I**): *Corpus humanum
      componitur ex plurimis (diversæ naturæ) individuis quorum
      unumquodque valde compositum est.*

      The human body is composed of many individuals. What is entered
      is that it has **a** proper part; the "*plurimis*" and the
      recursive "*quorum unumquodque valde compositum*" are again
      counting claims (GAP-8a's family), and Prop. XV needs only one
      part to conclude non-simplicity.

      This is the first *postulatum* to enter the register. Spinoza
      marks the physical digression's postulates as empirical in the
      same way Ax. II and Ax. IV are, which is why this is Section II
      and not I. -/
  ax2_corpus_humanum_compositum :
    ∀ b : Thing, Corpus (Attr := Attr) b → ∃ p : Thing, MereologyWorld.properPart p b

  /-- A71 (Section II — Prop. XV's *demonstratio*): the idea of a
      part of a body is a part of that body's idea.

      Spinoza: "*At cujuscunque individui corpus componentis datur
      necessario (per corollarium propositionis 8 hujus) in Deo idea;
      ergo (per propositionem 7 hujus) idea corporis humani ex
      plurimis hisce partium componentium ideis est composita.*" The
      inference from "each part has an idea" to "the whole's idea is
      composed of them" is licensed by the parallelism (Prop. VII),
      but the parallelism as mechanised relates *causal* orders, not
      part-whole ones. So the mereological transfer is entered as its
      own bridge.

      **Restricted to bodies** on purpose. The unrestricted form is
      false in the consistency witness: `Models/MensWitness.lean` gives
      the human mind a part in God's infinite idea (A72), and
      transferring *that* parthood up the idea ladder would require
      God's idea to be a part of the idea of God's idea, which the
      model does not provide. Whether the unrestricted form is
      *Spinoza's* is a separate question the text does not settle; he
      states it of the body. -/
  ax_idea_partis_pars_ideae :
    ∀ b p ip ib : Thing, Corpus (Attr := Attr) b →
      MereologyWorld.properPart p b → ideaOf ip p → ideaOf ib b →
        MereologyWorld.properPart ip ib

  /-- A72 (Section II — Prop. XI cor., the *pars* clause): the human
      mind is a proper part of God's infinite idea.

      *Mentem humanam partem esse infiniti intellectus Dei.* Batch 1.4
      derived everything else in this corollary — that the mind is a
      mode of thought, and that it is in God — and left "*pars*"
      open as GAP-30 because `properPart` was out of scope. It is in
      scope now, and this field supplies the clause.

      **Why it is not derived.** The natural route would be through
      `comprehensaIn`, the containment relation of batch 1.3: God's
      infinite idea contains every idea, so a bridge
      `comprehensaIn i j → i ≠ j → properPart i j` would do it. Two
      things block that. A56 gives containment in God's infinite idea
      only for the ideas of things that do **not** endure, and the
      mind of a living man endures; and the bridge itself is not
      innocent, since `comprehensaIn` is also the relation A66 uses
      for affections, where parthood is not obviously the right
      reading. Committing the corollary's own sentence is the smaller
      claim. Closes GAP-30. -/
  ax_mens_pars_intellectus_dei :
    ∀ h m g ig : Thing, Homo h → mensHominis m h → IsGod g →
      ideaOf ig g → MereologyWorld.properPart m ig

end corpus_axioms

section corpus_theorems

variable {Thing : Type u} {Attr : Type v}
  [instW : CorpusWorld Thing Attr] [instAx : CorpusAxioms Thing Attr]
open Pars2World QuatenusWorld ParallelismusWorld MensWorld CorpusWorld

/-! ## Propositio XIV

  Latin: *Mens humana apta est ad plurima percipiendum et eo aptior
         quo ejus corpus pluribus modis disponi potest.*
  Elwes: "The human mind is capable of perceiving a great number of
          things, and is so in proportion as its body is capable of
          receiving a great number of impressions."

  Demonstratio: *Corpus enim humanum (per postulata 3 et 6) plurimis
  modis a corporibus externis afficitur … At omnia quæ in corpore
  humano contingunt (per propositionem 12 hujus) mens humana percipere
  debet.*

  **What is mechanised**: the monotone half — the mind perceives
  *every* affection of its body, so the more affections the body
  admits, the more the mind perceives. That is Prop. XII quantified
  over affections, and it is what the *demonstratio* actually
  establishes.

  **Not mechanised**: the comparative "*eo aptior quo … pluribus
  modis*". It compares two counts (of affections, and of
  perceptions), and this formalisation has no cardinality framework —
  the same obstacle that keeps Def. VI's "*infinitis attributis*"
  partial (GAP-8a) and that dropped the "*multis modis*" of Ax. IV
  and the "*plurimis*" of Postulate I. Recorded rather than
  approximated. -/

/-- Prop. II.XIV (monotone form): the human mind perceives every
    affection of its body. -/
theorem prop_2_14_mensAptaAdPlurima (h m x : Thing)
    (hh : Homo h) (hm : mensHominis m h) (hx : ideaOf m x) :
    ∀ a : Thing, affectio a x → percipit m a := fun a haff =>
  prop_2_12_quicquidInObjectoPercipitur (Attr := Attr) h m x a hh hm hx haff

/-! ## Propositio XV

  Latin: *Idea quæ esse formale humanæ mentis constituit non est
         simplex sed ex plurimis ideis composita.*
  Elwes: "The idea, which constitutes the actual being of the human
          mind, is not simple, but compounded of a great number of
          ideas."

  Demonstratio: *Idea quæ esse formale humanæ mentis constituit, est
  idea corporis (per propositionem 13 hujus) quod (per postulatum 1)
  ex plurimis valde compositis individuis componitur. At cujuscunque
  individui corpus componentis datur necessario … in Deo idea; ergo …
  idea corporis humani ex plurimis hisce partium componentium ideis
  est composita.*

  **What is mechanised**: the *non simplex* clause, which is what
  every later proposition uses. Three steps, and each is a citation
  Spinoza makes: Prop. XIII says the mind's object is a body; A70
  (Postulate I) gives that body a part; A49 gives the part an idea;
  A71 makes that idea a part of the mind. The conclusion is
  `Divisible m` — the predicate `Ethica/Pars1/Mereology.lean` already
  defines, here applied to a mode rather than to a substance.

  **Not mechanised**: "*ex plurimis … composita*" as a count, for the
  reason given under Prop. XIV.

  Note that `Divisible m` is perfectly consistent with Pars I's
  `prop_12_substanceIndivisible` — that theorem is about substances,
  and the mind is a mode. The two never meet, which is also why this
  layer can take `MereologyWorld` without `MereologyAxioms`. -/

/-- Prop. II.XV: the idea constituting the human mind is not simple —
    it has a proper part. -/
theorem prop_2_15_mensNonSimplex (h m b : Thing)
    (hh : Homo h) (hm : mensHominis m h) (hb : ideaOf m b) :
    Divisible m := by
  obtain ⟨hcorp, _⟩ :=
    prop_2_13_objectumMentisEstCorpus (Attr := Attr) h m b hh hm hb
  obtain ⟨p, hp⟩ :=
    CorpusAxioms.ax2_corpus_humanum_compositum (Attr := Attr) b hcorp
  obtain ⟨ip, hip⟩ := prop_2_3_ideaOmnium (Attr := Attr) p
  exact ⟨ip, CorpusAxioms.ax_idea_partis_pars_ideae b p ip m hcorp hp hip hb⟩

/-! ## Propositio XI, corollarium — completed

  With `properPart` in scope, the clause batch 1.4 had to leave open
  can be stated. **GAP-30 closed.** -/

/-- Prop. II.XI cor., full form: the human mind is a mode of thought,
    it is in God, and it is a **proper part** of God's infinite idea.

    The first two conjuncts are batch 1.4's derivation; the third is
    A72. Closes GAP-30. -/
theorem prop_2_11_cor_mensParsIntellectusDei (g ig : Thing) (hgod : IsGod g)
    (hig : ideaOf ig g) (h m : Thing) (hh : Homo h) (hm : mensHominis m h) :
    Mode m ∧ modeUnder m (cogitatio Thing) ∧
      (m = g ∨ InherenceWorld.inheresIn m g) ∧
      MereologyWorld.properPart m ig := by
  obtain ⟨hmode, hcog, hloc⟩ :=
    prop_2_11_cor_mensInDeo (Attr := Attr) g hgod h m hh hm
  exact ⟨hmode, hcog, hloc,
    CorpusAxioms.ax_mens_pars_intellectus_dei h m g ig hh hm hgod hig⟩

/-! ## Propositio XVI

  Latin: *Idea cujuscunque modi quo corpus humanum a corporibus
         externis afficitur, involvere debet naturam corporis humani
         et simul naturam corporis externi.*
  Elwes: "The idea of every mode, in which the human body is affected
          by external bodies, must involve the nature of the human
          body, and also the nature of the external body."

  Demonstratio: *Omnes enim modi quibus corpus aliquod afficitur ex
  natura corporis affecti et simul ex natura corporis afficientis
  sequuntur (per axioma 1 post corollarium lemmatis 3) : quare eorum
  idea (per axioma 4 partis I) utriusque corporis naturam necessario
  involvet.*

  **What is mechanised**: the whole proposition, and it is a
  **derivation in exactly two steps, matching the two citations**.
  A68 is the physical Axioma I; A69 is the transfer to ideas that
  Spinoza licenses by Ax. I.4. Neither step is a reconstruction.

  This is the first proposition in Pars II whose *demonstratio* rests
  on the physical digression, and it is worth noting how cheap that
  turned out to be: one axiom of the digression, entered verbatim
  minus its counting tail. -/

/-- Prop. II.XVI: the idea of an affection of a body by another body
    involves the nature of both. -/
theorem prop_2_16_ideaAffectionisUtramqueNaturam (a b e i : Thing)
    (haff : affectio a b) (hcause : CausalWorld.Cause e a)
    (hi : ideaOf i a) :
    involvitNaturam i b ∧ involvitNaturam i e := by
  obtain ⟨hb, he⟩ :=
    CorpusAxioms.ax2_affectio_ex_utraque_natura (Attr := Attr) a b e haff hcause
  exact ⟨CorpusAxioms.ax_idea_involvit_naturam a b i hb hi,
    CorpusAxioms.ax_idea_involvit_naturam a e i he hi⟩

/-! ### Corollarium I to Prop. XVI

  Latin: *Hinc sequitur primo mentem humanam plurimorum corporum
  naturam una cum sui corporis natura percipere.*

  **What is mechanised**: that the mind perceives an affection whose
  idea involves the nature of the external body *together with* that
  of its own — the "*una cum*" that makes the corollary a claim about
  simultaneity rather than a list. Assembled from Prop. XIV (the mind
  perceives every affection of its body) and Prop. XVI.

  **Not mechanised**: "*plurimorum*", for the same counting reason. -/

/-- Prop. II.XVI cor. I: the mind perceives the nature of an external
    body together with the nature of its own. -/
theorem prop_2_16_cor1_naturamAlienamUnaCumSua (h m b a e : Thing)
    (hh : Homo h) (hm : mensHominis m h) (hb : ideaOf m b)
    (haff : affectio a b) (hcause : CausalWorld.Cause e a) :
    percipit m a ∧ ∃ i : Thing, ideaOf i a ∧
      involvitNaturam i b ∧ involvitNaturam i e := by
  obtain ⟨i, hi⟩ := prop_2_3_ideaOmnium (Attr := Attr) a
  exact ⟨prop_2_14_mensAptaAdPlurima (Attr := Attr) h m b hh hm hb a haff,
    i, hi, prop_2_16_ideaAffectionisUtramqueNaturam (Attr := Attr) a b e i
      haff hcause hi⟩

/-! ### Corollarium II to Prop. XVI — not mechanised

  Latin: *Sequitur secundo quod ideæ quas corporum externorum habemus,
  **magis** nostri corporis constitutionem **quam** corporum
  externorum naturam indicant.*

  This is a **comparative** claim — our ideas of external bodies
  indicate our own body's constitution *more than* the external
  bodies' nature — and it needs a degree-of-indication relation this
  formalisation does not have. It is not a counting claim like Prop.
  XIV's tail; it is a claim about which of two natures an idea
  represents better, and it is the epistemological seed of Props.
  XXIV–XXXI (all the "*adæquatam cognitionem non involvit*" results).

  It is recorded here and left for the adequacy layer, where the
  vocabulary to state it will exist. Spinoza himself defers the
  explanation ("*quod in appendice partis primæ multis exemplis
  explicui*"), which is a fair warning that no *demonstratio* is on
  offer. -/

end corpus_theorems

end Ethica.Pars2
