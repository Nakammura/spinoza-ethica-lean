/-
  Spinoza, *Ethica* — Attributum: the re-typed attribute axioms.

  `AttrAxioms` below carries the four Pars I axioms whose statements
  mention attributes, re-typed so the attribute argument ranges over
  `Attr` rather than over `Thing`:

    | Pars I | field                        | here | field                          |
    |--------|------------------------------|------|--------------------------------|
    | A10    | `ax_attribute_perSe`         | A10′ | `ax_attributum_perSe`          |
    | A12    | `ax_substanceIdByAttribute`  | A12′ | `ax_substanceIdByAttributum`   |
    | A14    | `ax_substance_has_attribute` | A14′ | `ax_substance_has_attributum`  |
    | A15    | `ax_IsGod_has_attribute_of`  | A15′ | `ax_IsGod_has_attributum_of`   |

  Section classification is inherited unchanged from
  `docs/auxiliary_axioms.md`: A10′ is a Section I definitional
  bridge; A12′, A14′ and A15′ are Section III substantive
  metaphysical commitments. Re-typing changes what the axioms can be
  *combined with*, not how heavy each one is on its own.

  **A8 has no primed counterpart, by design.** In Pars I, A8
  (`ax_inItself_iff_perSeConceived`) is what turned an attribute into
  a substance, via A10. That step is now ungrammatical, so no A8′ is
  declared and none can be: `inItself : Thing → Prop` cannot be
  applied to `a : Attr`. A8 itself survives untouched in
  `Pars1Axioms` and remains available for `Thing`s — it is only its
  *bite on attributes* that this layer withdraws. See `Core.lean`'s
  header and `docs/gaps.md` GAP-25.

  The consequence is the point of the whole exercise: the collapse
  chain has no step 3, so A12′ + A14′ + A15′ can coexist with a God
  having many distinct attributes. `Models/DualAttribute.lean` and
  `Models/InfiniteAttribute.lean` witness this.
-/
import Ethica.Pars1.Definitions
import Ethica.Pars1.Axioms
import Ethica.Attributum.Core

namespace Ethica.Attributum

open Ethica.Pars1
open Ethica.Pars1.EthicaWorld

universe u v

/-- The re-typed attribute axiom register.

    Deliberately **not** an extension of `Pars1Axioms`: that class
    carries A10/A12/A14/A15 in their `Thing`-typed form, and
    inheriting them would reinstate the collapse chain this layer
    exists to break. The attribute-free part of Pars I's register
    (A1, A1ₑ, A2, A7, A8, A9, A11) is orthogonal to attribute typing
    and is available separately via `Ethica.Pars1.StatedAxioms`;
    `Models/DualAttribute.lean` instantiates both classes on one
    carrier to show they are jointly consistent. -/
class AttrAxioms (Thing : Type u) (Attr : Type v) [AttrWorld Thing Attr] : Prop where
  /-- A10′ (Section I — definitional bridge, re-typed): every
      attribute of a substance is per se conceived.

      This is Spinoza's Prop. X (*Unumquodque unius substantiae
      attributum per se concipi debet*) with the conclusion stated in
      the attribute-side vocabulary. Pars I's A10 concluded
      `perSeConceived a` with `a : Thing`; here the conclusion is
      `perSeConceivedAttr a` with `a : Attr`.

      **The substantive difference is what is now missing.** In Pars
      I this conclusion fed A8 and yielded `Substance a`. Here it
      terminates: `perSeConceivedAttr` connects to nothing on the
      `Thing` side. Prop. X is preserved; the inference from Prop. X
      to the substancehood of attributes is not. Bennett 1984 §16. -/
  ax_attributum_perSe :
    ∀ (a : Attr) (s : Thing), Attributum a s → AttrStructure.perSeConceivedAttr a

  /-- A12′ (Section III — substantive metaphysical commitment,
      re-typed): two substances sharing an attribute are identical.

      Verbatim Pars I A12 with `a : Attr`. The commentary is
      unchanged (Bennett 1984 §17, Garrett 1990, Della Rocca 2008
      ch. 2): Spinoza's *demonstratio* of Prop. V is widely judged to
      need this commitment, and it remains the most load-bearing
      axiom of the formalisation.

      Note that re-typing does *not* weaken A12: it still collapses
      any two substances sharing an attribute. What it can no longer
      do is collapse an *attribute* into God, because the attribute
      is not a substance and so is not in A12's range. -/
  ax_substanceIdByAttributum :
    ∀ (s₁ s₂ : Thing) (a : Attr),
      Attributum a s₁ → Attributum a s₂ → s₁ = s₂

  /-- A14′ (Section III — substantive metaphysical commitment,
      re-typed): every substance has at least one attribute.

      Verbatim Pars I A14 with the existential ranging over `Attr`.
      Della Rocca 2008 ch. 2 takes it for granted under PSR; Bennett
      1984 §17 treats it as an independent commitment. In Pars I this
      axiom supplied step 4 of the collapse chain, handing an
      attribute to the substance an attribute had just been shown to
      be. With step 3 gone it has no such role and does only the work
      Spinoza asks of it. -/
  ax_substance_has_attributum :
    ∀ s : Thing, Substance s → ∃ a : Attr, Attributum a s

  /-- A15′ (Section III — substantive metaphysical commitment,
      re-typed): God has every attribute of every substance.

      Verbatim Pars I A15, the universality reading of Def. VI's
      *infinitis attributis* clause (GAP-8b). Bennett 1984 §18 flags
      the universality clause as a substantive commitment in its own
      right; Della Rocca 2008 ch. 2 derives it from PSR plus
      plenitude.

      In Pars I this was step 5, the axiom that finally handed the
      attribute-of-an-attribute to God so A12 could identify the two.
      Here it lands harmlessly: `Attributum a g` for many distinct
      `a : Attr` is exactly what Def. VI wants and what
      `Models/InfiniteAttribute.lean` exhibits. -/
  ax_IsGod_has_attributum_of :
    ∀ (g s : Thing) (a : Attr),
      IsGodAttr (Attr := Attr) g → Substance s → Attributum a s →
      Attributum a g

section attr_theorems

-- The instances are *named* so that `include` can force them into
-- the two Prop. IX statements below, whose signatures mention `Attr`
-- only through a named argument (`(Attr := Attr)`) — a position
-- Lean's automatic section-variable inclusion does not scan.
variable {Thing : Type u} {Attr : Type v}
  [instWorld : AttrWorld Thing Attr] [instAxioms : AttrAxioms Thing Attr]
open AttrWorld AttrStructure

/-! ## Propositio X, re-typed

  Latin: *Unumquodque unius substantiae attributum per se concipi
         debet.*
  Elwes: "Each particular attribute of the one substance must be
          conceived through itself."

  **What is mechanised**: the proposition in full, in the
  attribute-side vocabulary. What is *not* recovered — and is not
  recoverable at this layer by design — is Pars I's further
  inference from this proposition to `Substance a`, which required
  A8's coextension to apply to an attribute. See `Core.lean`'s
  header. -/

/-- Prop. X (re-typed): every attribute of a substance is per se
    conceived. Direct invocation of A10′, exactly as
    `Ethica.Pars1.prop_10_attributePerSe` is a direct invocation of
    A10. -/
theorem prop_10_attributumPerSe (a : Attr) (s : Thing)
    (h : Attributum a s) : perSeConceivedAttr a :=
  AttrAxioms.ax_attributum_perSe a s h

/-! ## Propositio V, re-typed

  Latin: *In rerum natura non possunt dari duae aut plures
         substantiae ejusdem naturae sive attributi.* -/

/-- Prop. V (re-typed): at most one substance per attribute. Direct
    application of A12′, mirroring
    `Ethica.Pars1.prop_5_uniqueSubstancePerAttribute`. -/
theorem prop_5_uniqueSubstancePerAttributum (s₁ s₂ : Thing) (a : Attr)
    (h₁ : Attributum a s₁) (h₂ : Attributum a s₂) : s₁ = s₂ :=
  AttrAxioms.ax_substanceIdByAttributum s₁ s₂ a h₁ h₂

/-! ## Propositio IX, re-typed

  Latin: *Quo plus realitatis aut esse unaquaeque res habet eo plura
         attributa ipsi competunt.* -/

include instWorld in
omit instAxioms in
/-- Prop. IX (re-typed): attribute-dominance transfers attribute
    counts. Verbatim transport of
    `Ethica.Pars1.prop_9_moreRealityMoreAttributes` — the proof is
    the same bookkeeping and uses no axiom at all. -/
theorem prop_9_moreRealityMoreAttrs (x y : Thing)
    (h : hasMoreRealityThanAttr (Attr := Attr) x y)
    (n : Nat) (hy : hasAtLeastNAttrs (Attr := Attr) y n) :
    hasAtLeastNAttrs (Attr := Attr) x n := by
  obtain ⟨f, hattr, hinj⟩ := hy
  exact ⟨f, fun i => h (f i) (hattr i), hinj⟩

include instWorld instAxioms in
/-- Prop. IX corollary (re-typed): God has maximal reality. Direct
    application of A15′, mirroring
    `Ethica.Pars1.prop_9_cor_godMaximalReality`. -/
theorem prop_9_cor_godMaximalRealityAttr (g : Thing)
    (hgod : IsGodAttr (Attr := Attr) g) (s : Thing) (hs : Substance s) :
    hasMoreRealityThanAttr (Attr := Attr) g s := by
  intro a ha
  exact AttrAxioms.ax_IsGod_has_attributum_of g s a hgod hs ha

end attr_theorems

end Ethica.Attributum
