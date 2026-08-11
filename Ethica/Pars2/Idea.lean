/-
  Spinoza, *Ethica* Pars II — De natura et origine mentis.
  Batch 1.1: the idea layer (Props. I, II, III, VII).

  This is the first module outside Pars I. It rests on the Attributum
  layer, and could not have been written before it: Pars II opens by
  asserting that Thought and Extension are **two distinct attributes
  of God**, which `Ethica/Pars1/Realitas.lean`'s
  `god_no_two_attributes` proves impossible in the Pars I register.
  `pars2_props_1_2_collapse_under_pars1_typing` at the end of this
  file records that impossibility in Pars I's own vocabulary; the
  layer built here avoids it by typing attributes separately, per
  GAP-25's route (iii).

  **What this batch mechanises**:

  - Prop. I  — *Cogitatio attributum Dei est* (📜, A46)
  - Prop. II — *Extensio attributum Dei est* (📜, A47)
  - **the pair**, i.e. that God has at least two attributes — a
    genuine derivation from A46 + A47 + A48, and the first theorem in
    the project that Pars I's register actively refutes
  - Prop. III — *In Deo datur necessario idea…* (📜, A49)
  - Prop. VII — *Ordo et connexio idearum idem est ac ordo et
    connexio rerum*, the **parallelism** — a genuine derivation from
    A4ₛ + A50, mirroring Spinoza's own one-line *demonstratio*
    ("*Patet ex axiomate 4 partis I*")

  **What is deferred to batch 1.2** (the *quatenus* layer): Props. V
  and VI both turn on attribute-relativised causation ("*Deum
  quatenus tantum ut res cogitans consideratur*"), which needs a
  ternary `causeUnder : Thing → Thing → Attr → Prop` primitive not
  introduced here — the same ternary-relativisation prerequisite
  GAP-22 already tracks for Prop. I.XXII. Prop. IV is deferred
  further: its *demonstratio* routes through Prop. I.XXX, which is
  itself ⏳ deferred (it needs A6-plus-Pars II machinery that only
  batch 1.4 supplies).

  **Structural note (the `outParam`)**. `Pars2World` extends both
  `AttrWorld Thing Attr` and `CausalWorld Thing`. Since `CausalWorld`
  does not mention `Attr`, the generated `toCausalWorld` projection
  leaves `Attr` a metavariable and Lean cannot find a synthesization
  order — exactly the failure `ModalForm.lean`'s §B.1 note describes
  for the modal layer, which chose to keep the classes separate.
  Here the two really must be combined (Prop. VII needs `Cause` and
  `Attributum` in one statement), so `Attr` is declared an
  `outParam`: a world determines its own attribute universe, which is
  both true and what makes instance resolution go through.
-/
import Ethica.Pars1.Definitions
import Ethica.Pars1.Axioms
import Ethica.Pars1.Causation
import Ethica.Pars1.Propositions
import Ethica.Pars1.Realitas
import Ethica.Attributum.Core
import Ethica.Attributum.Axioms

namespace Ethica.Pars2

open Ethica.Pars1
open Ethica.Pars1.EthicaWorld
open Ethica.Attributum

-- `Ethica.Pars1.CausalWorld` is deliberately *not* opened: `Pars2World`
-- flattens its fields, so `Cause` and `intelligibleThrough` would
-- resolve ambiguously between `Pars2World.Cause` and
-- `CausalWorld.Cause`. Inside the sections below they come from
-- `open Pars2World`, which is the same field.

universe u v

/-- The Pars II world: an Attributum world that also carries the
    causal primitives, plus the idea relation and the two attributes
    Spinoza names.

    `ideaOf i x` reads "`i` is the idea of `x`" (Def. III: *Per ideam
    intelligo mentis conceptum quem mens format propterea quod res
    est cogitans*). Ideas are things — modes of the attribute of
    thought — so `ideaOf : Thing → Thing → Prop` is right: unlike
    attributes, ideas genuinely *are* items in the universe of
    things, which Def. III's "*mentis conceptum*" makes explicit.

    `cogitatio` and `extensio` are distinguished *elements of `Attr`*,
    not predicates. This is the payoff of the Attributum layer: in
    Pars I they would have had to be things, and
    `god_is_own_only_attribute` would have identified both with
    God. -/
class Pars2World (Thing : Type u) (Attr : outParam (Type v))
    extends AttrWorld Thing Attr, CausalWorld Thing where
  /-- `ideaOf i x` : `i` is the idea of `x` (Def. III). -/
  ideaOf : Thing → Thing → Prop
  /-- *Cogitatio* — the attribute of thought (Prop. I). -/
  cogitatio : Attr
  /-- *Extensio* — the attribute of extension (Prop. II). -/
  extensio : Attr

section pars2_axioms

variable {Thing : Type u} {Attr : Type v} [Pars2World Thing Attr]
open Pars2World AttrStructure

/-- The Pars II axiom register for the idea layer.

    Extends `CausalAxioms` (hence `Pars1Axioms` — Pars II's
    *demonstrationes* cite Props. I.10, I.14, I.15, I.16 and I.25cor
    throughout) and `AttrAxioms` (the re-typed attribute register).

    Note that carrying `Pars1Axioms` is harmless here even though it
    contains the collapse-driving A12/A14/A15: those govern the
    `Thing`-typed attribution channel, which the collapse theorem
    forces to be degenerate (`god_is_own_only_attribute`), while the
    load-bearing attribute structure lives in `Attr`. The two coexist
    — `Models/MensWitness.lean` exhibits a single world satisfying
    Pars I's impossibility *and* Pars II's requirement
    simultaneously. -/
class Pars2Axioms (Thing : Type u) (Attr : outParam (Type v))
    [Pars2World Thing Attr]
    extends CausalAxioms Thing, AttrAxioms Thing Attr : Prop where
  /-- A45 (Section II — substantive promotion of Spinoza's **A6**):
      an idea has at most one object.

      Pars I carried A6 (*Idea vera debet cum suo ideato convenire*)
      as a `True` placeholder, annotated "idea/ideatum machinery is
      Pars II" (`Axioms.lean`). This is that promotion, and it
      retires the oldest placeholder in the project.

      **Honest scoping of the reading**: "*convenire*" is here read
      as *functionality* — an idea determines its object uniquely.
      That is the weakest content the word can carry and all this
      batch consumes. The stronger correspondence content (an
      adequate idea shares its object's intrinsic denominations,
      Def. IV *idea adæquata*) needs the adequacy machinery of batch
      1.4 and is **not** claimed here. -/
  ax6_idea_unique_ideatum :
    ∀ i x y : Thing, ideaOf i x → ideaOf i y → x = y

  /-- A46 (Section III — substantive metaphysical commitment,
      📜-pattern): *Cogitatio* is an attribute of God (Prop. II.I).

      Spinoza's *demonstratio* runs: singular thoughts are modes
      expressing God's nature (Prop. I.25cor); therefore God has an
      attribute whose concept every singular thought involves
      (Def. I.5); therefore thought is one of God's infinite
      attributes (Def. I.6). The step that is not available to us is
      the first premise's existential import — that there *are*
      singular thoughts. Spinoza supplies it from Pars II's own
      Axiom II (*Homo cogitat*), an avowedly empirical premise, and
      the scholium offers an independent route through conceiving an
      infinite thinking being.

      Rather than smuggle in an empirical axiom or reconstruct the
      scholium's argument, we commit the conclusion directly — the
      same 📜-pattern as A13/A27/A35/A40/A41. Bennett 1984 §36
      discusses the peculiar status of Pars II's opening propositions
      at length. -/
  ax_cogitatio_attributum :
    ∀ g : Thing, IsGodAttr (Attr := Attr) g → Attributum (cogitatio Thing) g

  /-- A47 (Section III — substantive metaphysical commitment,
      📜-pattern): *Extensio* is an attribute of God (Prop. II.II).

      Spinoza's *demonstratio* is one sentence — "*Hujus eodem modo
      procedit ac demonstratio præcedentis propositionis*" — so this
      axiom stands or falls exactly with A46. -/
  ax_extensio_attributum :
    ∀ g : Thing, IsGodAttr (Attr := Attr) g → Attributum (extensio Thing) g

  /-- A48 (Section III — substantive metaphysical commitment): thought
      and extension are **distinct** attributes.

      Spinoza never states this as a proposition; it is presupposed
      by the entire architecture of Pars II — by the parallelism
      (Prop. VII), which would be vacuous if the two orders were one,
      and by Prop. VI's insistence that modes of one attribute have
      God as cause *only* under that attribute.

      **This axiom is why the Attributum layer had to be built.**
      Under Pars I's typing, A46 + A47 + A48 are jointly
      inconsistent with the existence of a God: see
      `pars2_props_1_2_collapse_under_pars1_typing` below, which
      derives `cog = ext` from `god_is_own_only_attribute`. The
      inconsistency is not a defect of Spinoza's commitments but of
      the Prop. X scholium reading that puts attributes in `Thing`;
      GAP-25. -/
  ax_cogitatio_ne_extensio : (cogitatio Thing : Attr) ≠ extensio Thing

  /-- A49 (Section III — substantive metaphysical commitment,
      📜-pattern): everything has an idea (Prop. II.III).

      Spinoza's *demonstratio*: God can form the idea of his essence
      and of everything following from it (Prop. II.I + Prop. I.16);
      whatever is in God's power necessarily is (Prop. I.35);
      therefore such an idea necessarily exists, and only in God
      (Prop. I.15). The load-bearing middle step is Prop. I.35, which
      is ⏳ deferred in this formalisation (it needs the *potentia*
      machinery, along with Prop. I.34). So the conclusion is
      committed directly rather than derived through unavailable
      machinery — the same discipline A42's docstring applies to
      Prop. XXVIII.

      **What is not claimed**: the *in Deo* localisation ("*non nisi
      in Deo*"). Stating it needs `inheresIn`, i.e. the Inherence
      layer, which this batch does not import. Tracked as GAP-26. -/
  ax_god_has_idea_of_all :
    ∀ x : Thing, ∃ i : Thing, ideaOf i x

  /-- A50 (Section II — bridge, licensed by Spinoza's own
      *demonstratio* of Prop. VII): the idea order tracks
      intelligibility.

      Prop. VII's entire *demonstratio* is "*Patet ex axiomate 4
      partis I. Nam cujuscunque causati idea a cognitione causæ cujus
      est effectus, dependet*" — it follows from A4, because the idea
      of anything caused depends on knowledge of its cause. A4ₛ
      (`ax4_effectIntelligibleThroughCause`) delivers the
      intelligibility half; this axiom supplies the step Spinoza
      states in the second sentence, from intelligibility-dependence
      among *things* to causal dependence among their *ideas*.

      Committing it as Section II rather than Section III is
      deliberate: Spinoza asserts precisely this sentence as the
      content of his demonstration, so it is a promotion of stated
      material, not a reconstruction of a missing step. -/
  ax_idea_tracks_intelligibility :
    ∀ e c : Thing, intelligibleThrough e c →
      ∀ ie ic : Thing, ideaOf ie e → ideaOf ic c → Cause ic ie

end pars2_axioms

section pars2_theorems

variable {Thing : Type u} {Attr : Type v}
  [instW : Pars2World Thing Attr] [instAx : Pars2Axioms Thing Attr]
open Pars2World AttrStructure

/-! ## Propositio I

  Latin: *Cogitatio attributum Dei est sive Deus est res cogitans.*
  Elwes: "Thought is an attribute of God, or God is a thinking
          thing."

  **What is mechanised**: the proposition in full. It is a direct
  invocation of A46 (📜-pattern) — see that axiom's docstring for why
  the *demonstratio*'s existential premise is not reconstructed. -/

/-- Prop. II.I: thought is an attribute of God. -/
theorem prop_2_1_cogitatioAttributumDei (g : Thing)
    (hgod : IsGodAttr (Attr := Attr) g) : Attributum (cogitatio Thing) g :=
  Pars2Axioms.ax_cogitatio_attributum g hgod

/-! ## Propositio II

  Latin: *Extensio attributum Dei est sive Deus est res extensa.*
  Elwes: "Extension is an attribute of God, or God is an extended
          thing." -/

/-- Prop. II.II: extension is an attribute of God. -/
theorem prop_2_2_extensioAttributumDei (g : Thing)
    (hgod : IsGodAttr (Attr := Attr) g) : Attributum (extensio Thing) g :=
  Pars2Axioms.ax_extensio_attributum g hgod

/-! ## Propositions I and II together — the two-attribute result

  Neither proposition alone is remarkable; their **conjunction** is
  the structural claim of Pars II, and it is the first theorem in
  this project that the Pars I register actively *refutes*. The proof
  is a genuine derivation: A46 and A47 supply the two attributes, A48
  supplies their distinctness, and the `Fin 2` injection of
  `hasAtLeastNAttrs` packages them.

  Compare `Ethica.Pars1.god_no_two_attributes`. Same claim, opposite
  verdict; the sole difference is whether attributes share a type
  with substances. -/

/-- **God has at least two attributes.** Derived from A46 + A47 +
    A48.

    The Pars I analogue of this statement is refuted by
    `god_no_two_attributes`; see
    `pars2_props_1_2_collapse_under_pars1_typing` below. -/
theorem prop_2_1_2_deusHabetDuoAttributa (g : Thing)
    (hgod : IsGodAttr (Attr := Attr) g) :
    hasAtLeastNAttrs (Attr := Attr) g 2 := by
  refine ⟨fun i => if i.val = 0 then cogitatio Thing else extensio Thing, ?_, ?_⟩
  · intro i
    dsimp only
    split
    · exact prop_2_1_cogitatioAttributumDei g hgod
    · exact prop_2_2_extensioAttributumDei g hgod
  · intro i j h
    dsimp only at h
    have hi := i.isLt
    have hj := j.isLt
    apply Fin.eq_of_val_eq
    split at h <;> split at h
    · omega
    · exact absurd h Pars2Axioms.ax_cogitatio_ne_extensio
    · exact absurd h.symm Pars2Axioms.ax_cogitatio_ne_extensio
    · omega

/-! ## Propositio III

  Latin: *In Deo datur necessario idea tam ejus essentiæ quam omnium
         quæ ex ipsius essentia necessario sequuntur.*
  Elwes: "In God there is necessarily the idea not only of his own
          essence, but also of all things which necessarily follow
          from his essence."

  **What is mechanised**: the existential clause — everything has an
  idea. **Not mechanised**: the *in Deo* localisation, which needs
  the Inherence layer (GAP-26). -/

/-- Prop. II.III: every thing has an idea. Direct invocation of
    A49. -/
theorem prop_2_3_ideaOmnium (x : Thing) : ∃ i : Thing, ideaOf i x :=
  Pars2Axioms.ax_god_has_idea_of_all x

/-! ## Propositio VII — *the parallelism*

  Latin: *Ordo et connexio idearum idem est ac ordo et connexio
         rerum.*
  Elwes: "The order and connection of ideas is the same as the order
          and connection of things."

  Demonstratio: *Patet ex axiomate 4 partis I. Nam cujuscunque
  causati idea a cognitione causæ cujus est effectus, dependet.*

  **What is mechanised**: the causal-order transfer — if `c` causes
  `e`, then the idea of `c` causes the idea of `e`. This is the
  directional content the *demonstratio* actually establishes, and
  the proof mirrors it exactly: A4ₛ gives intelligibility-dependence
  among things, A50 carries it to causal dependence among ideas.
  A genuine derivation, not a commitment.

  **Not mechanised**: the converse direction, and the identity
  reading of "*idem est*" — that the two orders are *the same*
  order, not merely parallel. The scholium's stronger claim (a mode
  of extension and its idea are "*una eademque res sed duobus modis
  expressa*") needs the *quatenus* machinery of batch 1.2 plus
  cross-attribute identity. Tracked as GAP-27. -/

/-- Prop. II.VII (parallelism, directional form): the causal order
    among ideas tracks the causal order among things.

    Genuine derivation: A4ₛ (`ax4_effectIntelligibleThroughCause`)
    then A50 (`ax_idea_tracks_intelligibility`). -/
theorem prop_2_7_ordoEtConnexio (c e : Thing) (hce : Cause c e)
    (ic ie : Thing) (hic : ideaOf ic c) (hie : ideaOf ie e) :
    Cause ic ie :=
  Pars2Axioms.ax_idea_tracks_intelligibility e c
    (CausalAxioms.ax4_effectIntelligibleThroughCause c e hce) ie ic hie hic

/-- Prop. II.VII, applied: every causal pair has a corresponding
    causal pair among ideas. Combines the parallelism with A49's
    guarantee that ideas exist. -/
theorem prop_2_7_cor_ideaePariter (c e : Thing) (hce : Cause c e) :
    ∃ ic ie : Thing, ideaOf ic c ∧ ideaOf ie e ∧ Cause ic ie := by
  obtain ⟨ic, hic⟩ := prop_2_3_ideaOmnium (Attr := Attr) c
  obtain ⟨ie, hie⟩ := prop_2_3_ideaOmnium (Attr := Attr) e
  exact ⟨ic, ie, hic, hie, prop_2_7_ordoEtConnexio c e hce ic ie hic hie⟩

end pars2_theorems

/-! ## The contrast: why Pars II could not be built on Pars I's typing

  The theorem below is stated entirely in **Pars I's** vocabulary and
  uses only Pars I's register. It says that under the Prop. X
  scholium reading — attributes inhabit `Thing` — Props. II.I and
  II.II cannot both hold of distinct attributes: thought and
  extension would have to be *the same* attribute, and indeed both
  identical to God.

  This is the precise sense in which the Attributum layer was a
  prerequisite rather than a refinement. -/

section pars1_contrast

variable {Thing : Type u} [EthicaWorld Thing] [Pars1Axioms Thing]

/-- Under Pars I's typing, "thought" and "extension" collapse into
    one another.

    Given a God `g` and two `Thing`-typed attributes of it,
    `god_is_own_only_attribute` identifies each with `g`, hence with
    each other. Props. II.I and II.II are therefore jointly
    unavailable in the Pars I register on any reading that takes them
    to concern *distinct* attributes. -/
theorem pars2_props_1_2_collapse_under_pars1_typing
    (g : Thing) (hgod : IsGod g) (cog ext : Thing)
    (hcog : Attribute cog g) (hext : Attribute ext g) : cog = ext :=
  (god_is_own_only_attribute g hgod cog hcog).trans
    (god_is_own_only_attribute g hgod ext hext).symm

/-- The same result in refutation form: the Pars II opening triple
    (thought is an attribute of God; extension is an attribute of
    God; they are distinct) is inconsistent with Pars I's register
    once a God exists. -/
theorem pars2_opening_triple_inconsistent_in_pars1
    (g : Thing) (hgod : IsGod g) :
    ¬ ∃ cog ext : Thing, Attribute cog g ∧ Attribute ext g ∧ cog ≠ ext := by
  rintro ⟨cog, ext, hcog, hext, hne⟩
  exact hne (pars2_props_1_2_collapse_under_pars1_typing g hgod cog ext hcog hext)

end pars1_contrast

end Ethica.Pars2
