/-
  Spinoza, *Ethica* Pars I — Consecutio (the "follows from the
  necessity of the divine nature" arc).

  This module mechanises the consecution arc that carries Pars I from
  God's uniqueness/inherence (Props. XIV/XV, `Propositions.lean` /
  `Inherence.lean`) through the great causal cascade of Props.
  XVI–XXXVI: Prop. XVI (partial — "ex necessitate divinae naturae
  infinita infinitis modis … sequi debent"), Prop. XX (partial — "Dei
  existentia ejusque essentia unum et idem sunt"), Prop. XXI ("ex
  absoluta natura … semper et infinita existere debuerunt"), Prop.
  XXII (the modified-attribute transfer of eternity/infinity), Prop.
  XXV corollary ("res particulares nihil sunt nisi Dei attributorum
  affectiones"), Prop. XXVIII ("quodcunque singulare … non potest
  existere … nisi ab alia causa … finita … determinetur"), and Prop.
  XXXVI ("nihil existit ex cujus natura aliquis effectus non
  sequatur").

  Spinoza's "*ex necessitate naturae … sequitur*" is a relation
  distinct from both inherence ("*in alio esse*", `inheresIn`,
  `Inherence.lean`) and bare causation (`Cause`, `Causation.lean`),
  even though the three are tightly bound together in the
  demonstrationes of XVI–XVIII. We introduce two new primitives:

    - `followsFrom x y` : "x follows from the necessity of the nature
      of y" ("ex necessitate naturae ejus sequitur").
    - `followsAbsolutely x y` : "x follows from the ABSOLUTE nature of
      y" — Prop. XXI's "ex absoluta natura alicujus attributi Dei
      sequi", as opposed to following from y insofar as y is
      *modified* (Prop. XXII's and Prop. XXVIII's route, "quatenus
      modificatum est").

  Following the `CausalWorld`/`CausalAxioms` and
  `InherenceWorld`/`InherenceAxioms` pattern, the new primitives live
  in `ConsecutioWorld` (extending `InherenceWorld`) and the new axioms
  — **A37–A43** — live in `ConsecutioAxioms` (extending
  `InherenceAxioms`).
-/
import Ethica.Pars1.Definitions
import Ethica.Pars1.Axioms
import Ethica.Pars1.Causation
import Ethica.Pars1.Propositions
import Ethica.Pars1.Theologia
import Ethica.Pars1.Inherence

namespace Ethica.Pars1

universe u

/-- The consecution layer: `InherenceWorld` plus the two primitives
    Props. XVI–XXXVI need.

    `followsFrom x y` reads "x follows from the necessity of the
    nature of y" ("ex necessitate naturae ejus sequitur"), kept
    primitive and deliberately distinct from both `inheresIn` and
    `Cause` — A37/A38 below state exactly how the three connect,
    rather than silently identifying them.

    `followsAbsolutely x y` reads "x follows from the ABSOLUTE nature
    of y" (Prop. XXI's "ex absoluta natura alicujus attributi Dei
    sequi"), as opposed to following from y insofar as y is
    *modified* by some further modification (Prop. XXII's and Prop.
    XXVIII's route). -/
class ConsecutioWorld (Thing : Type u) extends InherenceWorld Thing where
  /-- `followsFrom x y` : x follows from the necessity of the nature
      of y ("ex necessitate naturae ejus sequitur"). -/
  followsFrom : Thing → Thing → Prop
  /-- `followsAbsolutely x y` : x follows from the ABSOLUTE nature of
      y ("ex absoluta natura … sequi"), as opposed to following from
      y insofar as y is modified. -/
  followsAbsolutely : Thing → Thing → Prop

variable {Thing : Type u} [ConsecutioWorld Thing]
open EthicaWorld CausalWorld InherenceWorld ConsecutioWorld

/-- The consecution axiomatic layer: `InherenceAxioms` plus
    **A37–A43**, the seven commitments needed to mechanise Props.
    XVI (partial), XX (partial), XXI, XXII, XXV corollary, XXVIII, and
    XXXVI. -/
class ConsecutioAxioms (Thing : Type u) [ConsecutioWorld Thing]
    extends InherenceAxioms Thing : Prop where
  /-- A37 (Section II — substantive promotion): what is in another
      follows from the necessity of that other's nature.

      Della Rocca 2008 ch. 2 reads inherence, causation, and
      consecution as facets of one underlying conceptual-dependence
      relation; Spinoza himself glides between "*in Deo est*" and "*ex
      necessitate divinae naturae sequitur*" without separate argument
      across the demonstrationes of Props. XVI–XVIII (compare Prop.
      XVIII's *demonstratio*, which moves from "in Deo sunt" straight
      to a causal conclusion via Prop. 16 Cor. I, treating the two as
      interchangeable). We make the bridge from `inheresIn` to
      `followsFrom` a visible commitment rather than an unstated
      identification. -/
  ax_inherence_consecution :
    ∀ x y : Thing, inheresIn x y → followsFrom x y

  /-- A38 (Section II — substantive promotion): consecution entails
      causation.

      Prop. XVI Corollary I's move: from "*ex necessitate divinae
      naturae infinita infinitis modis … sequi debent*" Spinoza
      concludes "*Deum omnium rerum … esse causam efficientem*" —
      consecution entails efficient causation, without further
      argument. We commit to that entailment directly.

      **Note**: A37 and A38 jointly make A34 (`InherenceAxioms.
      ax_inherence_causation`, "inherence entails causation") a
      *derivable* consequence: `inheresIn x y → followsFrom x y →
      Cause y x`. A34 is nonetheless retained as its own field in
      `InherenceAxioms` for backward compatibility with existing
      proofs (`prop_18_godImmanentCause` et al.) that consume it
      directly without going through the consecution layer; the
      resulting redundancy is intentional and is recorded in
      `docs/auxiliary_axioms.md` (tracked by the documentation batch,
      not resolved here). -/
  ax_consecution_causation :
    ∀ x y : Thing, followsFrom x y → Cause y x

  /-- A39 (Section I — definitional bridge): following absolutely is a
      way of following.

      "*Absoluta natura*" specialises, and never contradicts, bare
      "*natura*": whatever follows from the absolute nature of a
      thing follows, full stop, from the necessity of that thing's
      nature. This is the definitional relationship between the two
      consecution primitives, not a further metaphysical commitment. -/
  ax_absolute_consecution :
    ∀ x y : Thing, followsAbsolutely x y → followsFrom x y

  /-- A40 (Section III — substantive metaphysical commitment,
      📜-pattern; same honest-promotion device as A13 in
      `Axioms.lean`): whatever follows from the absolute nature of an
      attribute of God is eternal and not finite-after-its-kind.

      This IS Prop. XXI's content, adopted directly as an axiom.
      Spinoza's *demonstratio* is a two-part reductio run through
      *duration* (a mode supposed finite and of "determinatam
      existentiam sive durationem") and the finitude-limitation
      machinery (a mode limited, at some point, "aliquando non
      exstitisse vel non exstitura") that this base layer simply does
      not have — there are no temporal operators anywhere in
      `EthicaWorld`. We commit to the conclusion directly rather than
      construct a proof the layer cannot support.

      **Honest caveat**: the `Eternal` primitive used here is the
      same one Def. VIII supplies for God's own essence-grounded
      eternity (`prop_19_godIsEternal`); Prop. XXI's "aeterna" for
      infinite modes is arguably a *derivative* sempiternity-through-a-
      cause rather than the essence-grounded eternity of God himself
      (a distinction Spinoza's own text glosses over via "*per idem
      attributum aeterna*"). Disentangling the two senses awaits the
      modal layer's world-relative existence machinery
      (`ModalForm.lean`); this axiom conflates them, as Spinoza's text
      itself invites. -/
  ax_absoluteConsecution_eternalInfinite :
    ∀ x a g : Thing, IsGod g → Attribute a g → followsAbsolutely x a →
      Eternal x ∧ ¬ finitumInSuoGenere x

  /-- A41 (Section III — substantive metaphysical commitment,
      📜-pattern): whatever follows from an eternal, non-finite mode
      is itself eternal and non-finite.

      This IS Prop. XXII's content. Spinoza's own *demonstratio*
      simply refers back to Prop. XXI's ("*eodem modo*"), but the
      statement itself is genuinely ternary: "*ex aliquo Dei
      attributo, quatenus modificatum est modificatione quae …*" — a
      thing following from an *attribute-as-modified-by-a-
      modification*, not simply from a modification taken on its own.
      The present `ConsecutioWorld` only has the binary
      `followsFrom : Thing → Thing → Prop`, so the attribute-
      relativisation ("*ex aliquo Dei attributo quatenus
      modificatum*") cannot be represented; we flatten Prop. XXII to a
      binary transfer directly along `followsFrom` from the infinite
      mode itself. A ternary consecution relation (thing / attribute /
      modification) would be needed to capture the full statement —
      not introduced here. -/
  ax_infiniteModeTransfer :
    ∀ x m : Thing, Mode m → Eternal m → ¬ finitumInSuoGenere m →
      followsFrom x m → Eternal x ∧ ¬ finitumInSuoGenere x

  /-- A42 (Section III — substantive metaphysical commitment,
      📜-pattern): every finite mode is caused by some other, distinct
      finite mode.

      This IS Prop. XXVIII's content, in its non-iterated single-step
      form (the "*et sic in infinitum*" iteration is the content of
      `prop_28_cor_noFirstFiniteCause` below, not of this axiom
      itself). Spinoza's *demonstratio* chains Prop. XXI and Prop.
      XXII with an exhaustiveness premise — every mode follows either
      absolutely, or via an infinite modification, or via a finite one
      (the trichotomy Prop. XXIII itself asserts) — to rule out the
      first two horns and land on the third. Prop. XXIII is not
      mechanised in this batch (it is itself uncommitted machinery,
      deferred), so that exhaustiveness reasoning is not available
      here. The direct commitment to Prop. XXVIII's conclusion is the
      honest minimal form: rather than fake a derivation through an
      unavailable trichotomy, we commit to the destination directly.
      This axiom is the backbone of finite-mode causation that Pars
      II–V consume throughout. -/
  ax_finiteMode_causedByFiniteMode :
    ∀ x : Thing, Mode x → finitumInSuoGenere x →
      ∃ y, Mode y ∧ finitumInSuoGenere y ∧ y ≠ x ∧ Cause y x

  /-- A43 (Section III — substantive metaphysical commitment,
      📜-pattern): everything that exists has something follow from
      it.

      This IS Prop. XXXVI's content ("*nihil existit ex cujus natura
      aliquis effectus non sequatur*"). Spinoza's *demonstratio*
      routes through Prop. XXV Corollary ("*quicquid existit, Dei
      naturam … certo et determinato modo exprimit*") plus Prop.
      XXXIV ("*Dei potentia est ipsa ipsius essentia*") to conclude,
      via Prop. XVI, that an effect must follow — the whole argument
      turns on the *potentia* ("power") machinery of Props. XXXIV–XXXV,
      which is not formalised anywhere in this project (those
      propositions are deferred; there is no `power`/`potentia`
      primitive at this layer). Rather than fabricate a power relation
      solely to route this one proof, we commit to the consecution
      conclusion directly. -/
  ax_omnia_effectum :
    ∀ x : Thing, ∃ e, followsFrom e x

section consecutio_theorems
variable {Thing : Type u} [ConsecutioWorld Thing] [ConsecutioAxioms Thing]
open EthicaWorld CausalWorld InherenceWorld ConsecutioWorld

/-! ## Propositio XVI (partial)

  Latin: *Ex necessitate divinae naturae infinita infinitis modis (hoc
         est omnia quae sub intellectum infinitum cadere possunt)
         sequi debent.*
  Elwes: "From the necessity of the divine nature must follow an
          infinite number of things in infinite ways — that is, all
          things which can fall within the sphere of infinite
          intellect."

  Demonstratio: *Haec propositio unicuique manifesta esse debet si
  modo ad hoc attendat quod ex data cujuscunque rei definitione plures
  proprietates intellectus concludit … Cum autem natura divina
  infinita absolute attributa habeat (per definitionem 6) quorum etiam
  unumquodque infinitam essentiam in suo genere exprimit, ex ejusdem
  ergo necessitate infinita infinitis modis … necessario sequi
  debent.*

  **What is mechanised**: the universal consecution of every mode
  from the divine nature — "*ex necessitate divinae naturae … sequi
  debent*" restricted to the modes actually in the domain. The
  "*infinita infinitis modis*" cardinality clause (a claim about *how
  many* things follow, and in how many ways) awaits the counting
  framework already flagged for Def. VI's "*infinitis attributis*"
  (the GAP-8a family); what is mechanised is the qualitative content —
  every mode follows from God — not the cardinality claim.

  Mechanisation: by `prop_15_allInGod g hgod x`, either `x = g` or
  `inheresIn x g`. The `x = g` branch is vacuous: rewriting `Mode x`
  along `x = g` would give `Mode g`, contradicting
  `prop_1_substanceDisjointFromModes g hgod.1`. The `inheresIn x g`
  branch closes via A37. -/

/-- Prop. XVI (partial — qualitative clause): every mode follows from
    the necessity of the divine nature. -/
theorem prop_16_modesFollowFromGod (g : Thing) (hgod : IsGod g) :
    ∀ x : Thing, Mode x → followsFrom x g := by
  intro x hmode
  rcases prop_15_allInGod g hgod x with heq | hin
  · exact absurd (heq ▸ hmode) (prop_1_substanceDisjointFromModes g hgod.1)
  · exact ConsecutioAxioms.ax_inherence_consecution x g hin

/-! ## Propositio XVI — Corollarium I

  Latin: *Hinc sequitur Deum omnium rerum quae sub intellectum
         infinitum cadere possunt, esse causam efficientem.*
  Elwes: "Hence it follows, that God is the efficient cause of all
          that can fall within the sphere of an infinite intellect."

  Mechanisation: direct application of A38 to `prop_16_modesFollowFromGod`.
  This gives an alternative derivation of the causal conjunct of
  `prop_18_godImmanentCause`, now routed through consecution — exactly
  as Spinoza's own Corollary I derives it from Prop. XVI rather than
  from Prop. XV/XVIII directly. -/

/-- Prop. XVI Corollary I: God is the efficient cause of every mode. -/
theorem prop_16_cor1_godEfficientCause (g : Thing) (hgod : IsGod g) :
    ∀ x : Thing, Mode x → Cause g x := fun x hmode =>
  ConsecutioAxioms.ax_consecution_causation x g
    (prop_16_modesFollowFromGod g hgod x hmode)

/-! ## Propositio XX (partial)

  Latin: *Dei existentia ejusque essentia unum et idem sunt.*
  Elwes: "The existence of God and his essence are one and the same."

  Demonstratio: *Deus … ejusque omnia attributa sunt aeterna hoc est
  (per definitionem 8) unumquodque ejus attributorum existentiam
  exprimit. Eadem ergo Dei attributa quae (per definitionem 4) Dei
  aeternam essentiam explicant, ejus simul aeternam existentiam
  explicant …*

  **What is mechanised**: the two conjuncts Spinoza's *demonstratio*
  actually assembles — each attribute of God expresses both His
  essence (Def. IV: `Attribute`) and His necessary existence (A29,
  `TheologiaAxioms.ax_attribute_involvesExistence`). The full identity
  claim ("*unum et idem sunt*" — that essence and existence are
  literally *the same thing*, not merely that each attribute involves
  both) requires essence-as-object machinery (treating "God's essence"
  and "God's existence" as terms that can be asserted equal) not
  present at this layer; tracked as a gap for the documentation batch.
  What is mechanised is the conjunctive content the proof is built
  from, not the identity conclusion itself. -/

omit [ConsecutioAxioms Thing] in
/-- Prop. XX (partial): every attribute of God both expresses His
    essence (constitutively, via `Attribute`) and involves His
    existence (A29).

    **Note on the extra instance**: `TheologiaAxioms` is not an
    ancestor of `ConsecutioAxioms` in the class hierarchy (both extend
    `Pars1Axioms`/`CausalAxioms` independently — a diamond, as with
    `InherenceAxioms`; see `Models/CounterexamplesII.lean` for a world
    combining both siblings). A29 is only available from
    `TheologiaAxioms`, so this theorem takes it as an explicit extra
    instance rather than assuming it is reachable through
    `ConsecutioAxioms` alone. -/
theorem prop_20_partial_attributesExpressBoth [TheologiaAxioms Thing]
    (g : Thing) (hgod : IsGod g) :
    ∀ a : Thing, Attribute a g → involvesExistence a ∧ expressesEternalEssence a :=
  fun a ha =>
    ⟨TheologiaAxioms.ax_attribute_involvesExistence a g ha,
      hgod.2.2.2 a ha⟩

/-! ## Propositio XXI

  Latin: *Omnia quae ex absoluta natura alicujus attributi Dei
         sequuntur, semper et infinita existere debuerunt sive per
         idem attributum aeterna et infinita sunt.*
  Elwes: "All things which follow from the absolute nature of any
          attribute of God must always exist and be infinite, or, in
          other words, are eternal and infinite through the said
          attribute."

  Demonstratio: a two-part reductio, run through duration (a
  hypothesised finite thing with "determinatam … existentiam sive
  durationem") and through the possibility of a thing that "aliquando
  non exstitisse vel non exstitura" — machinery this base layer does
  not have (see A40's docstring above).

  Mechanisation: direct application of A40 (📜-pattern — this IS the
  proposition's content, adopted as an axiom exactly as A13 was for
  Prop. VII; see A40's docstring for why the two-part durational
  reductio does not mechanise without it). -/

/-- Prop. XXI: whatever follows from the absolute nature of an
    attribute of God is eternal and not finite-after-its-kind. -/
theorem prop_21_absoluteFollowersEternalInfinite
    (x a g : Thing) (hgod : IsGod g) (ha : Attribute a g)
    (hf : followsAbsolutely x a) : Eternal x ∧ ¬ finitumInSuoGenere x :=
  ConsecutioAxioms.ax_absoluteConsecution_eternalInfinite x a g hgod ha hf

/-! ## Propositio XXII

  Latin: *Quicquid ex aliquo Dei attributo quatenus modificatum est
         tali modificatione quae et necessario et infinita per idem
         existit, sequitur, debet quoque et necessario et infinitum
         existere.*
  Elwes: "Whatsoever follows from any attribute of God, in so far as
          it is modified by a modification, which exists necessarily
          and as infinite, through the said attribute, must also
          exist necessarily and as infinite."

  Demonstratio: *Hujus propositionis demonstratio procedit eodem modo
  ac demonstratio praecedentis* — Spinoza refers back to Prop. XXI's
  proof method without restating it.

  Mechanisation: direct application of A41 (📜-pattern; see A41's
  docstring above for the honest note on the flattening of Spinoza's
  ternary "attribute-as-modified-by-modification" form to the binary
  `followsFrom` transfer used here). -/

/-- Prop. XXII: whatever follows from an eternal, non-finite mode is
    itself eternal and non-finite. -/
theorem prop_22_infiniteModeTransfer
    (x m : Thing) (hm : Mode m) (he : Eternal m)
    (hinf : ¬ finitumInSuoGenere m) (hf : followsFrom x m) :
    Eternal x ∧ ¬ finitumInSuoGenere x :=
  ConsecutioAxioms.ax_infiniteModeTransfer x m hm he hinf hf

/-! ## Propositio XXV — Corollarium

  Latin: *Res particulares nihil sunt nisi Dei attributorum affectiones
         sive modi quibus Dei attributa certo et determinato modo
         exprimuntur.*
  Elwes: "Individual things are nothing but modifications of the
          attributes of God, or modes by which the attributes of God
          are expressed in a fixed and definite manner."

  Demonstratio: *Demonstratio patet ex propositione 15 et definitione
  5.*

  **What is mechanised**: the corollary's content — every particular
  thing is either God Himself or a mode. Prop. XXV proper ("*Deus non
  tantum est causa efficiens rerum existentiae sed etiam essentiae*",
  God as cause of the ESSENCE of things, not merely their existence)
  needs essence-as-object machinery not present at this layer, and is
  not mechanised here — only the corollary, which Spinoza himself
  proves from Prop. XV and Def. V directly (i.e. from material already
  available), independently of Prop. XXV's own harder essence-causation
  claim.

  Mechanisation: `prop_4_partition x` gives `Substance x ∨ Mode x`; the
  substance case collapses to `x = g` via `prop_14_onlyGodIsSubstance`. -/

/-- Prop. XXV corollary: every particular thing is either God or a
    mode. -/
theorem prop_25_cor_everythingGodOrMode (g : Thing) (hgod : IsGod g) :
    ∀ x : Thing, x = g ∨ Mode x := fun x =>
  (prop_4_partition x).imp (prop_14_onlyGodIsSubstance g hgod x) id

/-! ## Propositio XXVIII

  Latin: *Quodcunque singulare sive quaevis res quae finita est et
         determinatam habet existentiam, non potest existere nec ad
         operandum determinari nisi ad existendum et operandum
         determinetur ab alia causa quae etiam finita est et
         determinatam habet existentiam et rursus haec causa non
         potest etiam existere neque ad operandum determinari nisi ab
         alia quae etiam finita est et determinatam habet
         existentiam, determinetur ad existendum et operandum et sic
         in infinitum.*
  Elwes: "Every individual thing, or everything which is finite and
          has a conditioned existence, cannot exist or be conditioned
          to act, unless it be conditioned for existence and action by
          a cause other than itself, which also is finite, and has a
          conditioned existence; and likewise this cause cannot in its
          turn exist, or be conditioned to act, unless it be
          conditioned for existence and action by another cause, which
          also is finite, and has a conditioned existence, and so on
          to infinity."

  Demonstratio: chains Prop. XXI and Prop. XXII with the trichotomy of
  Prop. XXIII (every mode follows absolutely, or via an infinite
  modification, or via a finite one) to rule out the first two horns
  and land on the third — see A42's docstring above for why that
  trichotomy is not available at this layer.

  Mechanisation: direct application of A42 (📜-pattern — the
  single-step content of the proposition; the "*et sic in infinitum*"
  iteration is `prop_28_cor_noFirstFiniteCause` below). -/

/-- Prop. XXVIII (single-step form): every finite mode is caused by
    some other, distinct finite mode. -/
theorem prop_28_finiteModeCausedByFiniteMode
    (x : Thing) (hx : Mode x) (hfin : finitumInSuoGenere x) :
    ∃ y, Mode y ∧ finitumInSuoGenere y ∧ y ≠ x ∧ Cause y x :=
  ConsecutioAxioms.ax_finiteMode_causedByFiniteMode x hx hfin

/-- Prop. XXVIII's "*et sic in infinitum*" corollary: there is no
    first finite mode, i.e. no finite mode all of whose putative
    finite-mode causes would fail to actually cause it.

    Proof: were such an `x` to exist, A42 applied to `x` itself
    supplies a distinct finite-mode cause `y` of `x`, directly
    contradicting the universal clause of the hypothesis instantiated
    at `y`. -/
theorem prop_28_cor_noFirstFiniteCause :
    ¬ ∃ x : Thing, Mode x ∧ finitumInSuoGenere x ∧
      ∀ y, Mode y → finitumInSuoGenere y → y ≠ x → ¬ Cause y x := by
  rintro ⟨x, hx, hfin, hnone⟩
  obtain ⟨y, hy, hyfin, hne, hcause⟩ :=
    ConsecutioAxioms.ax_finiteMode_causedByFiniteMode x hx hfin
  exact hnone y hy hyfin hne hcause

/-! ## Propositio XXXVI

  Latin: *Nihil existit ex cujus natura aliquis effectus non sequatur.*
  Elwes: "There is no cause from whose nature some effect does not
          follow."

  Demonstratio: *Quicquid existit, Dei naturam sive essentiam certo et
  determinato modo exprimit (per corollarium propositionis 25) hoc est
  (per propositionem 34) quicquid existit, Dei potentiam quae omnium
  rerum causa est, certo et determinato modo exprimit adeoque (per
  propositionem 16) ex eo aliquis effectus sequi debet.*

  Mechanisation: A43 gives directly `∃ e, followsFrom e x`; A38 then
  converts `followsFrom e x` to `Cause x e`. A small but genuine
  derivation — the consecution content is committed by A43, and the
  causal form is *derived* from it, rather than separately committed. -/

/-- Prop. XXXVI: everything that exists has some effect follow from
    it. -/
theorem prop_36_nothingWithoutEffect (x : Thing) : ∃ e, Cause x e := by
  obtain ⟨e, hf⟩ := ConsecutioAxioms.ax_omnia_effectum (Thing := Thing) x
  exact ⟨e, ConsecutioAxioms.ax_consecution_causation e x hf⟩

end consecutio_theorems

end Ethica.Pars1
