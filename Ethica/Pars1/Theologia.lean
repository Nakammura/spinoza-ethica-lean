/-
  Spinoza, *Ethica* Pars I — Theologia (the theological arc).

  This module mechanises the theological arc of Pars I: Prop. XI
  ("Deus … necessario existit"), Prop. XVII ("Deus … agit … a nemine
  coactus"), and Prop. XIX ("Deus sive omnia Dei attributa sunt
  æterna"). Together these three propositions carry the demonstration
  from God's bare *definition* (Def. VI, already mechanised as
  `IsGod` in `Definitions.lean`) to God's *existence*, *freedom*, and
  *eternity*.

  Getting there requires five new auxiliary axioms, A27–A31, packaged
  as fields of a new typeclass `TheologiaAxioms` (which `extends
  Pars1Axioms`, following the `CausalAxioms` pattern in
  `Causation.lean`). Each is classified by the project's Section I /
  II / III scheme (`docs/auxiliary_axioms.md`):

    - Section I  (definitional bridge): A28, A30
    - Section II (substantive promotion): A29, A31
    - Section III (substantive metaphysical commitment): A27

  A27 in particular is the load-bearing one: it is the *instantiation*
  half of the ontological argument ("Deus datur"), and
  `Models/NoGod.lean` supplies the kernel-level witness that it is
  **not** derivable from `Pars1Axioms` (A1–A15) alone.
-/
import Ethica.Pars1.Definitions
import Ethica.Pars1.Axioms
import Ethica.Pars1.Propositions

namespace Ethica.Pars1

universe u

variable {Thing : Type u} [EthicaWorld Thing]
open EthicaWorld

/-- The theological layer: `Pars1Axioms` plus the five commitments
    (A27–A31) needed to mechanise Props. XI, XVII, and XIX. Following
    the `CausalAxioms` pattern, `TheologiaAxioms` extends `Pars1Axioms`
    rather than sitting beside it, so downstream theorems consume one
    typeclass instance instead of juggling two. -/
class TheologiaAxioms (Thing : Type u) [EthicaWorld Thing]
    extends Pars1Axioms Thing : Prop where
  /-- A27 (Section III — substantive metaphysical commitment): God
      exists.

      This is the *instantiation* commitment of the ontological
      argument ("Deus datur"). Spinoza's *demonstratio* of Prop. XI
      (the reductio: "Si negas, concipe, si fieri potest, Deum non
      existere. Ergo (per axioma 7) ejus essentia non involvit
      existentiam. Atqui hoc (per propositionem 7) est absurdum.")
      moves from *conceptual* necessity (essence involves existence —
      a conditional established by Prop. VII for anything that *is* a
      substance) to *instantiation* (some thing in the domain is
      God). That step is exactly the gap Gassendi and later Kant
      pressed against ontological arguments: Prop. VII yields "IF g
      is a substance THEN its essence involves existence", but
      nothing in A1–A15 puts a God-satisfying element in the domain.
      Bennett 1984 §18 catalogues four reading paths through the
      demonstratio; each needs at least one commitment beyond the
      stated axioms. A27 is the minimal direct form.

      Kernel-level irreducibility is witnessed by `Models/NoGod.lean`:
      a world satisfying ALL of `Pars1Axioms` (A1–A15, including the
      Section III commitments A12–A15) in which nothing is God. Note
      this baseline is *stronger* than the paper's A12/A15
      counter-models, which run against `StatedAxioms` only. -/
  ax_god_exists : ∃ g : Thing, IsGod g

  /-- A28 (Section I — definitional bridge): whatever's nature
      requires existence is eternal.

      Def. VIII *defines* eternity as "ipsam existentiam, quatenus ex
      sola rei aeternae definitione necessario sequi concipitur"; the
      bridge from `natureRequiresExistence` to `eternal` is the
      definitional unfolding Spinoza performs in Prop. XIX's
      demonstratio ("per definitionem 8"). -/
  ax_natureRequiresExistence_eternal :
    ∀ x : Thing, natureRequiresExistence x → eternal x

  /-- A29 (Section II — substantive promotion): every attribute of a
      substance involves existence.

      Prop. XIX's demonstratio argues the attributes of God "express
      existence" — each attribute expresses the eternal essence of
      substance (Def. VI) and substance's essence involves existence
      (Prop. VII); the transfer of `involvesExistence` from substance
      to its attributes is used by Spinoza without separate
      statement. Promoted to kernel-usable form. -/
  ax_attribute_involvesExistence :
    ∀ a s : Thing, Attribute a s → involvesExistence a

  /-- A30 (Section I — definitional bridge, Def. VII): a thing that is
      *causa sui* and unconstrained is free.

      Def. VII: free is what "ex sola suae naturae necessitate
      existit". `causaSui` supplies the necessity-of-own-nature half;
      `¬ constrained` supplies the "sola/alone" half; the bridge
      composes them into the `freelyExistent` primitive. -/
  ax_causaSui_unconstrained_free :
    ∀ x : Thing, causaSui x → ¬ constrained x → freelyExistent x

  /-- A31 (Section II — substantive promotion): no substance is
      constrained.

      Constraint (Def. VII) is determination *by another*. A
      substance cannot be produced/determined by another substance
      (Prop. VI), and determination by modes is excluded by the
      priority of substance over its affections (Prop. I). Spinoza
      uses this composite in Prop. XVII's demonstratio ("nulla res
      extra ipsum"). The mode-side exclusion outruns what Prop. I's
      mechanised disjointness fragment delivers, hence Section II
      promotion rather than derivation. -/
  ax_substance_not_constrained : ∀ s : Thing, Substance s → ¬ constrained s

section theologia_theorems

variable {Thing : Type u} [EthicaWorld Thing] [TheologiaAxioms Thing]
open EthicaWorld

/-! ## Propositio XI

  Latin: *Deus sive substantia constans infinitis attributis quorum
         unumquodque æternam et infinitam essentiam exprimit,
         necessario existit.*
  Elwes: "God, or substance, consisting of infinite attributes, of
          which each expresses eternal and infinite essentiality,
          necessarily exists."

  Demonstratio: *Si negas, concipe si fieri potest, Deum non existere.
  Ergo (per axioma 7) ejus essentia non involvit existentiam. Atqui
  hoc (per propositionem 7) est absurdum : ergo Deus necessario
  existit.*

  Mechanisation: A27 supplies the existential witness `g` with
  `IsGod g` directly (the instantiation step the reductio glosses
  over — see A27's docstring above). From `hgod.1 : Substance g`,
  A13 (`ax_substance_involves_existence`) gives `involvesExistence
  g`, and A11 (`ax_causaSui_iff`) converts this to
  `natureRequiresExistence g`. -/

/-- Prop. XI: God necessarily exists, and God's essence both involves
    existence and requires existence by God's very nature. -/
theorem prop_11_godNecessarilyExists :
    ∃ g : Thing, IsGod g ∧ involvesExistence g ∧ natureRequiresExistence g := by
  obtain ⟨g, hgod⟩ := TheologiaAxioms.ax_god_exists (Thing := Thing)
  have hinv : involvesExistence g :=
    Pars1Axioms.ax_substance_involves_existence g hgod.1
  have hnat : natureRequiresExistence g :=
    (Pars1Axioms.ax_causaSui_iff g).mp hinv
  exact ⟨g, hgod, hinv, hnat⟩

/-- Prop. XI corollary: God is *causa sui*, via Prop. VII
    (`prop_7_substanceIsCausaSui`) applied to God's substancehood. -/
theorem prop_11_godIsCausaSui (g : Thing) (hgod : IsGod g) : causaSui g :=
  prop_7_substanceIsCausaSui g hgod.1

/-! ## Propositio XVII

  Latin: *Deus ex solis suæ naturæ legibus et a nemine coactus agit.*
  Elwes: "God acts solely by the laws of his own nature, and is not
          constrained by anyone."

  Corollarium II: *Sequitur II. solum Deum esse causam liberam. Deus
  enim solus ex sola suæ naturæ necessitate existit (per
  propositionem 11 et corollarium I propositionis 14) et ex sola
  suæ naturæ necessitate agit (per propositionem præcedentem).
  Adeoque (per definitionem 7) solus est causa libera.*
  Elwes: "God is the sole free cause. For God alone exists by the
          sole necessity of his nature … and acts by the sole
          necessity of his own nature, wherefore God is (by Def.
          vii.) the sole free cause."

  Mechanisation: God is *causa sui* (Prop. VII, via `hgod.1 :
  Substance g`); God is not constrained (A31, via `hgod.1`); A30
  composes the two into `freelyExistent g`, i.e. `Free g`.

  **Textual scope note**: this mechanises Corollary II's content only
  in its *existence*-clause reading ("ex sola suæ naturæ necessitate
  existit"). The *action*-clause ("ad agendum a se solo
  determinatur") awaits Pars II's action machinery — same caveat as
  `Free`'s definition in `Definitions.lean` (GAP-9). -/

/-- Prop. XVII (existence-clause reading, via Cor. II): God is free.
    God is *causa sui* and not constrained, so A30 delivers
    `freelyExistent g`. -/
theorem prop_17_godIsFree (g : Thing) (hgod : IsGod g) : Free g := by
  have hcausaSui : causaSui g := prop_7_substanceIsCausaSui g hgod.1
  have hunconstrained : ¬ constrained g :=
    TheologiaAxioms.ax_substance_not_constrained g hgod.1
  exact TheologiaAxioms.ax_causaSui_unconstrained_free g hcausaSui
    hunconstrained

/-! ## Propositio XIX

  Latin: *Deus sive omnia Dei attributa sunt æterna.*
  Elwes: "God, and all the attributes of God, are eternal."

  Demonstratio: *Deus enim (per definitionem 6) est substantia quæ
  (per propositionem 11) necessario existit hoc est (per
  propositionem 7) ad cujus naturam pertinet existere sive (quod
  idem est) ex cujus definitione sequitur ipsum existere adeoque
  (per definitionem 8) est æternus. Deinde per Dei attributa
  intelligendum est id quod (per definitionem 4) divinæ substantiæ
  essentiam exprimit … Atqui ad naturam substantiæ … pertinet
  æternitas. Ergo unumquodque attributorum æternitatem involvere
  debet adeoque omnia sunt æterna.*
  Elwes: "God … is substance, which … necessarily exists, that is …
          existence appertains to its nature … therefore, God is
          eternal … Now eternity appertains to the nature of
          substance … therefore, eternity must appertain to each of
          the attributes, and thus all are eternal."

  Mechanisation, God's case: A13 gives `involvesExistence g` from
  `Substance g`; A11 converts to `natureRequiresExistence g`; A28
  converts that to `eternal g`.

  Mechanisation, attributes' case: A29 gives `involvesExistence a`
  from `Attribute a g`; A11 converts to `natureRequiresExistence a`;
  A28 converts that to `eternal a`. -/

/-- Prop. XIX (God's case): God is eternal. -/
theorem prop_19_godIsEternal (g : Thing) (hgod : IsGod g) : Eternal g := by
  have hinv : involvesExistence g :=
    Pars1Axioms.ax_substance_involves_existence g hgod.1
  have hnat : natureRequiresExistence g :=
    (Pars1Axioms.ax_causaSui_iff g).mp hinv
  exact TheologiaAxioms.ax_natureRequiresExistence_eternal g hnat

/-- Prop. XIX (attributes' case): every attribute of God is eternal.

    Note on the unused `_hgod` hypothesis: kept for textual fidelity to
    Spinoza's "Deus sive omnia Dei attributa" phrasing, even though
    the proof itself runs entirely through A29 on `ha : Attribute a
    g`, which already carries `Substance g`. Compare
    `prop_8_substanceIsNotFinite`'s signed-inconsistency note in
    `Propositions.lean` — the same stylistic choice is made here. -/
theorem prop_19_attributesAreEternal
    (g a : Thing) (_hgod : IsGod g) (ha : Attribute a g) : Eternal a := by
  have hinv : involvesExistence a :=
    TheologiaAxioms.ax_attribute_involvesExistence a g ha
  have hnat : natureRequiresExistence a :=
    (Pars1Axioms.ax_causaSui_iff a).mp hinv
  exact TheologiaAxioms.ax_natureRequiresExistence_eternal a hnat

end theologia_theorems

end Ethica.Pars1
