/-
  Spinoza, *Ethica* Pars I — Inherence layer ("everything is in God").

  This module mechanises the arc that carries Pars I from God's
  uniqueness (Prop. XIV, already mechanised in `Propositions.lean`)
  to the doctrine that everything whatsoever is *in* God and *caused
  by* God: Prop. XV ("Quicquid est, in Deo est"), Prop. XVIII ("Deus
  est omnium rerum causa immanens"), Prop. XXIV ("rerum a Deo
  productarum essentia non involvit existentiam"), Prop. XXVI
  (partial — the determination-by-God clause), and Prop. XXIX ("in
  rerum natura nullum datur contingens").

  The base layer's `inAnother` (Def. V, in `Definitions.lean`) is
  *unary* — it says a thing exists in another, without saying which
  other. Spinoza's Prop. XV needs the *binary* "in Deo est" relation:
  not merely that modes are in something, but that they are in God
  specifically. We introduce a new primitive `inheresIn : Thing →
  Thing → Prop` for this, together with four auxiliary axioms A33–A36
  that give it (and its interaction with causation, existence, and
  constraint) the content Props. XV/XVIII/XXIV/XXVI/XXIX actually
  need. Following the `CausalWorld`/`CausalAxioms` and
  `MereologyWorld`/`MereologyAxioms` pattern, the new primitive lives
  in `InherenceWorld` (extending `CausalWorld`) and the new axioms
  live in `InherenceAxioms` (extending `CausalAxioms`).
-/
import Ethica.Pars1.Definitions
import Ethica.Pars1.Axioms
import Ethica.Pars1.Causation
import Ethica.Pars1.Propositions

namespace Ethica.Pars1

universe u

/-- The inherence layer: `CausalWorld` plus the binary "is in"
    primitive Prop. XV needs.

    `inheresIn x y` reads "x is in y" — Spinoza's "in alio esse" made
    binary (Def. V speaks only of a mode being "in alio", i.e. "in
    another", without a further argument place for *which* other).
    Kept primitive and deliberately *not* tied to the unary
    `inAnother` of Def. V beyond what A33 states: this keeps the new
    commitment minimal and legible, rather than silently redefining
    Def. V's existing content. -/
class InherenceWorld (Thing : Type u) extends CausalWorld Thing where
  /-- `inheresIn x y` : `x` is in `y` (binary form of "in alio esse"). -/
  inheresIn : Thing → Thing → Prop

variable {Thing : Type u} [InherenceWorld Thing]
open EthicaWorld CausalWorld InherenceWorld

/-- The inherence axiomatic layer: `CausalAxioms` plus **A33–A36**,
    the four commitments needed to mechanise Props. XV, XVIII, XXIV,
    XXVI (partial), and XXIX. -/
class InherenceAxioms (Thing : Type u) [InherenceWorld Thing]
    extends CausalAxioms Thing : Prop where
  /-- A33 (Section II — substantive promotion of Def. V): every mode
      is in some substance.

      Def. V calls modes "*substantiæ affectiones, sive id quod in
      alio est*" — affections OF SUBSTANCE. The unary `inAnother`
      clause used to define `Mode` (Def. V's left conjunct) does not
      by itself say the "*alio*" a mode is in is a *substance*;
      Spinoza's usage throughout — especially Prop. XV's
      *demonstratio* ("*Modi autem [...] sine substantia nec esse
      nec concipi possunt*") — treats it as such without separate
      argument. We promote that usage to a kernel-usable binary
      axiom. -/
  ax_mode_inheres_in_substance :
    ∀ x : Thing, Mode x → ∃ s, Substance s ∧ inheresIn x s

  /-- A34 (Section II — substantive promotion): inherence entails
      causation.

      The bridge from "x is in y" to "y causes x" is exactly
      Curley's celebrated reading of Spinoza's "in" (Curley 1969,
      *Spinoza's Metaphysics*: to be in God is to be caused by God).
      Spinoza himself licenses the move in Prop. XVIII's
      *demonstratio*: "*omnia quæ sunt, in Deo sunt [...] adeoque
      [...] Deus rerum quæ in ipso sunt, est causa*" — "are in" is
      used to conclude "is the cause of". Without this bridge,
      Prop. XVIII's "*causa immanens*" would have no causal content
      at the level this layer works. -/
  ax_inherence_causation :
    ∀ x y : Thing, inheresIn x y → Cause y x

  /-- A35 (Section III — substantive metaphysical commitment; same
      honest-promotion pattern as A13): no mode's essence involves
      existence.

      This IS Prop. XXIV's content, adopted directly as an axiom.
      Spinoza's *demonstratio* is a single line — "*Patet ex
      definitione 1*" — reasoning that if a produced thing's essence
      involved existence, it would be *causa sui* and hence not
      produced by another. That inference needs a converse link
      ("produced by another ⇒ not *causa sui*") that the axioms
      stated so far do not deliver: A7 (`ax7_conceivableAsNonExistent`)
      runs the *other* direction (non-necessity of nature ⇒ no
      involved existence), and nothing else in `Pars1Axioms` or
      `CausalAxioms` connects being a mode to *not* involving
      existence. We commit visibly, exactly as A13 (Prop. VII's
      content) was committed in `Axioms.lean`. -/
  ax_mode_not_involvesExistence :
    ∀ x : Thing, Mode x → ¬ involvesExistence x

  /-- A36 (Section II — substantive promotion of Def. VII's second
      clause): every mode is constrained.

      Def. VII: "*coacta [...] quæ ab alio determinatur ad
      existendum et operandum*" — the constrained is what is
      determined *by another* to exist and to act. A mode, being in
      another and conceived through another (Def. V), is determined
      by that other in just this sense; Spinoza deploys the reading
      without separate argument in the demonstrationes of Props.
      XXVI and XXIX ("*Res quæ [...] determinata est*" /
      "*determinata sunt*"). The action-clause half of Def. VII
      ("*ad operandum*") awaits Pars II's action machinery (the
      GAP-9 family, already flagged for `Free`/`Constrained` in
      `Definitions.lean`); what is committed here is the
      existence-clause fragment. -/
  ax_mode_constrained :
    ∀ x : Thing, Mode x → constrained x

section inherence_theorems
variable {Thing : Type u} [InherenceWorld Thing] [InherenceAxioms Thing]
open EthicaWorld CausalWorld InherenceWorld

/-! ## Propositio XV

  Latin: *Quicquid est, in Deo est et nihil sine Deo esse neque
         concipi potest.*
  Elwes: "Whatsoever is, is in God, and without God nothing can be,
          or be conceived."

  Demonstratio: *Præter Deum nulla datur neque concipi potest
  substantia (per 14 propositionem) hoc est (per definitionem 3) res
  quæ in se est et per se concipitur. Modi autem (per definitionem 5)
  sine substantia nec esse nec concipi possunt; quare hi in sola
  divina natura esse et per ipsam solam concipi possunt. Atqui
  præter substantias et modos nil datur (per axioma 1). Ergo nihil
  sine Deo esse neque concipi potest.*

  **What is mechanised**: the *ontological* clause — every thing
  either is God or is in God. The second clause of the statement
  ("*nec concipi potest sine Deo*", "nor be conceived without God")
  is epistemic and awaits the conception machinery developed in Pars
  II; it is not mechanised here.

  Mechanisation: by `prop_4_partition x`, `x` is a substance or a
  mode. If a substance, `prop_14_onlyGodIsSubstance` forces `x = g`.
  If a mode, A33 supplies a substance `s` with `inheresIn x s`;
  `prop_14_onlyGodIsSubstance` forces `s = g`, and rewriting gives
  `inheresIn x g`. -/

/-- Prop. XV (ontological clause): everything is either God or in
    God. -/
theorem prop_15_allInGod (g : Thing) (hgod : IsGod g) :
    ∀ x : Thing, x = g ∨ inheresIn x g := by
  intro x
  rcases prop_4_partition x with hsub | hmode
  · left
    exact prop_14_onlyGodIsSubstance g hgod x hsub
  · right
    obtain ⟨s, hs, hin⟩ := InherenceAxioms.ax_mode_inheres_in_substance x hmode
    have hsg : s = g := prop_14_onlyGodIsSubstance g hgod s hs
    exact hsg ▸ hin

/-! ## Propositio XVIII

  Latin: *Deus est omnium rerum causa immanens, non vero transiens.*
  Elwes: "God is the indwelling and not the transient cause of all
          things."

  Demonstratio: *Omnia quæ sunt, in Deo sunt et per Deum concipi
  debent (per propositionem 15) adeoque [...] Deus rerum quæ in ipso
  sunt, est causa, quod est primum. Deinde extra Deum nulla potest
  dari substantia (per propositionem 14) hoc est (per definitionem 3)
  res quæ extra Deum in se sit, quod erat secundum. Deus ergo est
  omnium rerum causa immanens, non vero transiens.*

  Mechanisation: "immanent" is captured by the conjunction — God
  causes `x` AND `x` is in God (a transient/transitive cause's
  effects would lie *outside* it, which the conjunction rules out).
  From `prop_15_allInGod g hgod x`: if `x = g`, then substituting
  into `Mode x` would give `Mode g`, contradicting
  `prop_1_substanceDisjointFromModes g hgod.1`; so this case is
  vacuous. Otherwise `inheresIn x g`, and A34 gives `Cause g x`. -/

/-- Prop. XVIII: God is the immanent cause of every mode — God
    causes it, and it is in God. -/
theorem prop_18_godImmanentCause (g : Thing) (hgod : IsGod g) :
    ∀ x : Thing, Mode x → Cause g x ∧ inheresIn x g := by
  intro x hmode
  rcases prop_15_allInGod g hgod x with heq | hin
  · exact absurd (heq ▸ hmode) (prop_1_substanceDisjointFromModes g hgod.1)
  · exact ⟨InherenceAxioms.ax_inherence_causation x g hin, hin⟩

/-! ## Propositio XXIV

  Latin: *Rerum a Deo productarum essentia non involvit existentiam.*
  Elwes: "The essence of things produced by God does not involve
          existence."

  Demonstratio: *Patet ex definitione 1. Id enim cujus natura (in se
  scilicet considerata) involvit existentiam, causa est sui et ex
  sola suæ naturæ necessitate existit.*

  Mechanisation: direct application of A35 (which *is* this
  proposition's content, promoted to axiom status — the 📜-pattern
  also used for A13 in `Axioms.lean`; see A35's docstring above for
  why the one-line *demonstratio* does not mechanise without it). -/

/-- Prop. XXIV: no mode's essence involves existence. -/
theorem prop_24_producedEssenceNotInvolveExistence
    (x : Thing) (hx : Mode x) : ¬ involvesExistence x :=
  InherenceAxioms.ax_mode_not_involvesExistence x hx

/-! ## Propositio XXIV — Corollarium (fragment)

  Latin: *Hinc sequitur Deum non tantum esse causam ut res incipiant
         existere sed etiam ut in existendo perseverent [...]*
  Elwes: "Hence it follows that God is not only the cause of things
          beginning to exist, but also of their continuing to
          exist [...]"

  What is mechanised here is the narrower fragment the corollary's
  own reasoning starts from: a mode, not involving existence in its
  essence, is not *causa sui*. The corollary's further claim (God as
  cause of *perseverance* in existence, "*causa essendi*") needs a
  temporal/durational notion the base layer does not have, and is
  not mechanised. -/

/-- Prop. XXIV corollary (fragment): no mode is *causa sui*.
    `causaSui` unfolds to `involvesExistence`, so this is
    definitionally `prop_24_producedEssenceNotInvolveExistence`. -/
theorem prop_24_cor_modeNotCausaSui (x : Thing) (hx : Mode x) :
    ¬ causaSui x :=
  prop_24_producedEssenceNotInvolveExistence x hx

/-! ## Propositio XXVI (partial)

  Latin: *Res quæ ad aliquid operandum determinata est, a Deo
         necessario sic fuit determinata et quæ a Deo non est
         determinata, non potest se ipsam ad operandum determinare.*
  Elwes: "A thing which is conditioned to act in a particular
          manner, has necessarily been thus conditioned by God ; and
          that which has not been conditioned by God cannot
          condition itself to act."

  Demonstratio: *Id per quod res determinatæ ad aliquid operandum
  dicuntur, necessario quid positivum est [...] Adeoque tam ejus
  essentiæ quam existentiæ Deus ex necessitate suæ naturæ est causa
  efficiens (per propositiones 25 et 16) [...]*

  **What is mechanised**: mode is *determined* (A36), and *by God*
  specifically (`prop_18_godImmanentCause`'s causal clause) — i.e.
  the proposition's "*a Deo [...] determinata*" content restricted
  to the existence-side reading of `Constrained` (see A36's caveat).
  The "*ad aliquid operandum*"/self-determination clause (the
  second half of the statement, and the whole of Prop. XXVII) awaits
  Pars II's action machinery. Hence "partial". -/

/-- Prop. XXVI (partial): every mode is constrained, and by God. -/
theorem prop_26_modesDeterminedByGod (g : Thing) (hgod : IsGod g) :
    ∀ x : Thing, Mode x → Constrained x ∧ Cause g x := by
  intro x hmode
  refine ⟨InherenceAxioms.ax_mode_constrained x hmode, ?_⟩
  exact (prop_18_godImmanentCause g hgod x hmode).1

/-! ## Propositio XXIX

  Latin: *In rerum natura nullum datur contingens sed omnia ex
         necessitate divinæ naturæ determinata sunt ad certo modo
         existendum et operandum.*
  Elwes: "Nothing in the universe is contingent, but all things are
          conditioned to exist and operate in a particular manner by
          the necessity of the divine nature."

  Demonstratio: *Quicquid est in Deo est (per propositionem 15) :
  Deus autem non potest dici res contingens. Nam (per propositionem
  11) necessario, non vero contingenter existit. Modi deinde divinæ
  naturæ ex eadem etiam necessario, non vero contingenter secuti sunt
  (per propositionem 16) [...]*

  **What is mechanised**: the content actually available at this
  layer — every thing either exists from the necessity of its own
  nature (`causaSui`, the substance case, via A13) or is determined
  by another (`Constrained`, the mode case, via A36). This is the
  "nothing is contingent" reading in its disjunctive, non-modal
  form: `causaSui x ∨ Constrained x` exhausts the alternatives to
  contingency Spinoza's proof trades on. The "*ex necessitate
  divinæ naturæ*" strengthening — that the determination is
  specifically *by God* — is available by conjoining
  `prop_26_modesDeterminedByGod` whenever a witness for `IsGod` is
  in hand; it is not folded into this statement so the theorem holds
  for any `Thing`, God or not. -/

/-- Prop. XXIX: nothing is contingent — every thing either exists
    from the necessity of its own nature, or is determined by
    another. -/
theorem prop_29_nothingContingent (x : Thing) :
    causaSui x ∨ Constrained x := by
  rcases prop_4_partition x with hsub | hmode
  · exact Or.inl (Pars1Axioms.ax_substance_involves_existence x hsub)
  · exact Or.inr (InherenceAxioms.ax_mode_constrained x hmode)

end inherence_theorems

end Ethica.Pars1
