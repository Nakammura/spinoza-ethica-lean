/-
  Spinoza, *Ethica* Pars I — Mereology layer (divisibility of substance).

  This module mechanises the divisibility arc of Pars I: Prop. XII
  ("no attribute of substance can be truly conceived from which it
  follows that substance can be divided") and Prop. XIII ("substance
  absolutely infinite is indivisible"), together with Prop. XIII's
  corollary.

  Spinoza never states a mereology. His demonstrationes of XII and
  XIII quantify over "parts" (*partes*) of substance entirely
  informally — there is no prior definition of "part" anywhere in
  Pars I's Definitiones or Axiomata. We therefore introduce the
  minimal part-relation the two demonstrationes actually need, and a
  single new Section III commitment, A32, that encodes the
  load-bearing premise of both proofs. Following the `CausalAxioms` /
  `TheologiaAxioms` pattern, the new primitive lives in a typeclass
  `MereologyWorld` extending `EthicaWorld`, and the new axiom lives in
  a typeclass `MereologyAxioms` extending `Pars1Axioms`.
-/
import Ethica.Pars1.Definitions
import Ethica.Pars1.Axioms
import Ethica.Pars1.Propositions

namespace Ethica.Pars1

universe u

/-- The mereological layer: `EthicaWorld` plus the single primitive
    needed to state Props. XII/XIII — a proper-part relation. Kept
    deliberately thin: no mereological structure (transitivity, weak
    supplementation, antisymmetry, …) is assumed, because Props.
    XII/XIII need none of it — Spinoza's dilemma only ever asks
    whether a hypothesised part "retains the nature" of the whole. -/
class MereologyWorld (Thing : Type u) extends EthicaWorld Thing where
  /-- `properPart p x` : `p` is a proper part of `x`. Primitive; no
      further mereological axioms (transitivity, supplementation,
      …) are assumed at this layer. -/
  properPart : Thing → Thing → Prop

variable {Thing : Type u} [MereologyWorld Thing]
open EthicaWorld MereologyWorld

/-- `Divisible x` : `x` has some proper part. This is the mechanised
    reading of "*substantiam posse dividi*" (Prop. XII) / "*si
    divisibilis esset*" (Prop. XIII) — to be divisible is to have a
    proper part. -/
def Divisible (x : Thing) : Prop := ∃ p, properPart p x

/-- The mereological axiomatic layer: `Pars1Axioms` plus **A32**, the
    single substantive commitment Props. XII/XIII need.

    **A32** (Section III — substantive metaphysical commitment).

    Spinoza's *demonstratio* of Prop. XII runs a dilemma on a
    hypothesised division of substance into parts: either (i) the
    parts *retain* the nature of the substance — in which case two
    (or more) substances of the same nature would exist, absurd per
    Prop. V — or (ii) the parts do *not* retain that nature — in
    which case the substance could lose its nature and cease to
    exist, absurd per Prop. VII. Prop. XIII's *demonstratio* is the
    same dilemma re-run for absolutely infinite substance, with horn
    (i) landing on Prop. V and horn (ii) on Prop. XI (existence)
    instead of Prop. VII.

    Horn (ii) requires destruction/persistence machinery — a notion
    of a substance ceasing to exist over time or across possibility —
    that the base layer does not have (it belongs with the modal /
    temporal extensions, not here). Horn (i) is the load-bearing one
    for the actual contradiction in both proofs, and needs no such
    machinery: it is a purely synchronic claim about what a
    hypothesised part *would be*. A32 encodes exactly the premise
    horn (i) needs: a proper part of a substance would itself be a
    substance of the same nature as the whole, and distinct from it.

    Bennett 1984 §21–22 reads Spinoza's rejection of the divisibility
    of substance as resting on precisely this "parts would be rival
    substances" premise — that a genuine part of a substance could
    only be conceived, per Def. III/IV, as itself *in itself* and
    *per se conceived*, i.e. as itself a substance sharing the
    whole's nature. We commit to that premise visibly, as a Section
    III axiom, rather than deriving it from Defs. III/IV (which do
    not by themselves force a *part* of a substance to inherit
    substancehood).

    The `p ≠ s` conjunct encodes properness: Spinoza's "*pars*"
    throughout the demonstratio means *proper* part (a substance is
    not its own part). -/
class MereologyAxioms (Thing : Type u) [MereologyWorld Thing]
    extends Pars1Axioms Thing : Prop where
  /-- A32: a proper part of a substance is itself a substance, shares
      the whole's nature, and is distinct from the whole. -/
  ax_substancePart_sameNatureSubstance :
    ∀ s p : Thing, Substance s → properPart p s →
      Substance p ∧ sameNature p s ∧ p ≠ s

section mereology_theorems

variable {Thing : Type u} [MereologyWorld Thing] [MereologyAxioms Thing]
open EthicaWorld MereologyWorld

/-! ## Propositio XII

  Latin: *Nullum substantiæ attributum potest vere concipi ex quo
         sequatur substantiam posse dividi.*
  Elwes: "No attribute of substance can be conceived from which it
          would follow that substance can be divided."

  Demonstratio: *Partes enim in quas substantia sic concepta
  divideretur, vel naturam substantiæ retinebunt vel non. Si primum,
  tum (per 8 propositionem) unaquæque pars debebit esse infinita et
  (per propositionem 6) causa sui et (per propositionem 5) constare
  debebit ex diverso attributo adeoque ex una substantia plures
  constitui poterunt, quod (per propositionem 6) est absurdum. Adde
  quod partes (per propositionem 2) nihil commune cum suo toto
  haberent et totum (per definitionem 4 et propositionem 10) absque
  suis partibus et esse et concipi posset, quod absurdum esse nemo
  dubitare poterit. Si autem secundum ponatur quod scilicet partes
  naturam substantiæ non retinebunt, ergo cum tota substantia in
  æquales partes esset divisa, naturam substantiæ amitteret et esse
  desineret, quod (per propositionem 7) est absurdum.*

  **What is actually mechanised**: Spinoza states Prop. XII
  *epistemically* — "no attribute can be *truly conceived* from
  which it follows…" — a claim about what can be truly conceived,
  not directly a claim that substance is not divisible. The base
  layer has no "truly conceiving" operator (that machinery belongs
  to Pars II's theory of ideas), so the epistemic wrapper cannot yet
  be mechanised. What both XII and XIII's demonstrationes actually
  turn on, and what is mechanised here, is their shared *ontological
  core*: no substance has a proper part, i.e. no substance is
  divisible. The epistemic reading ("no such attribute is truly
  conceivable") awaits Pars II's idea machinery.

  Mechanisation of the ontological core: suppose `s` is a substance
  with a proper part `p`. A32 gives `Substance p`, `sameNature p s`,
  and `p ≠ s` — this is horn (i) of Spinoza's dilemma, made
  load-bearing directly (see A32's docstring for why horn (ii) is
  not needed). `sameNature p s` unpacks to a shared attribute; A12
  (`ax_substanceIdByAttribute`) then forces `p = s`, contradicting
  `p ≠ s`. -/

/-- Prop. XII (ontological core): no substance is divisible. -/
theorem prop_12_substanceIndivisible
    (s : Thing) (hs : Substance s) : ¬ Divisible s := by
  intro ⟨p, hpart⟩
  obtain ⟨_hsubp, ⟨a, hap, has⟩, hne⟩ :=
    MereologyAxioms.ax_substancePart_sameNatureSubstance s p hs hpart
  exact hne (Pars1Axioms.ax_substanceIdByAttribute p s a hap has)

/-! ## Propositio XIII

  Latin: *Substantia absolute infinita est indivisibilis.*
  Elwes: "Substance absolutely infinite is indivisible."

  Demonstratio: *Si enim divisibilis esset, partes in quas divideretur
  vel naturam substantiæ absolute infinitæ retinebunt vel non. Si
  primum, dabuntur ergo plures substantiæ ejusdem naturæ, quod (per
  propositionem 5) est absurdum. Si secundum ponatur, ergo (ut supra)
  poterit substantia absolute infinita desinere esse, quod (per
  propositionem 11) est etiam absurdum.*

  Mechanisation: `IsGod g` carries `Substance g` as its first
  conjunct (`hgod.1`); Prop. XIII is then a direct specialisation of
  the ontological core of Prop. XII to any absolutely infinite
  substance (paradigmatically God, per Def. VI). -/

/-- Prop. XIII: an absolutely infinite substance (in particular, God)
    is indivisible. -/
theorem prop_13_absolutelyInfiniteSubstanceIndivisible
    (g : Thing) (hgod : IsGod g) : ¬ Divisible g :=
  prop_12_substanceIndivisible g hgod.1

/-! ## Propositio XIII — Corollarium

  Latin: *Ex his sequitur nullam substantiam et consequenter nullam
         substantiam corpoream, quatenus substantia est, esse
         divisibilem.*
  Elwes: "It follows, that no substance, and consequently no extended
          substance, in so far as it is substance, is divisible."

  Mechanisation: this is Prop. XII's ontological core again, restated
  for any substance whatsoever (the corollary's "bodily substance"
  clause needs no separate content at this layer — `Substance` does
  not yet distinguish extended from other substance; that
  distinction awaits the attribute-specific machinery of Pars II). -/

/-- Prop. XIII corollary: no substance, in so far as it is substance,
    is divisible. Identical in content to `prop_12_substanceIndivisible`;
    restated under its own name for citability. -/
theorem prop_13_cor_noSubstanceDivisible :
    ∀ s : Thing, Substance s → ¬ Divisible s :=
  prop_12_substanceIndivisible

end mereology_theorems

end Ethica.Pars1
