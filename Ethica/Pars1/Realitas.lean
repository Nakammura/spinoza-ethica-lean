/-
  Spinoza, *Ethica* Pars I — Realitas (the reality/attribute-counting
  arc: Propositio IX and GAP-8a).

  This module mechanises Prop. IX under the Della Rocca reading —
  reality is *constituted* by attributes, not measured by some
  further quantity attributes happen to track (Della Rocca 2008
  ch. 2; the reading is licensed by Def. IV, which already identifies
  an attribute with "id quod intellectus de substantia percipit
  tanquam ejusdem essentiam constituens"). Under that reading, "more
  reality" just *is* "attribute-dominance": `x` has at least every
  attribute `y` has. Prop. IX then reduces to a transfer theorem for
  attribute-*counts*, which is exactly the cardinality-free counting
  apparatus GAP-8a asked for (`docs/gaps.md`) — `hasAtLeastNAttributes`
  and `HasInfiniteAttributes` below make Def. VI's "infinitis
  attributis" clause STATEABLE for the first time in this
  formalisation, closing the missing-framework half of GAP-8a.

  The closing section of this file is the intellectual payload: once
  the counting framework exists, it can be pointed at `IsGod`, and
  doing so reveals that the *existing* register (A8, A10, A12, A14,
  A15 — no new axiom) already forces every attribute of every
  substance to equal God. Def. VI's "constantem infinitis
  attributis" is therefore not merely unformalised but
  *unsatisfiable* here. See `/-! ## The attribute-collapse theorem -/`
  below for the full discussion, and `Models/MultiAttribute.lean` for
  the companion model showing the incompatibility is sharp (plurality
  is consistent — but only in a godless world).
-/
import Ethica.Pars1.Definitions
import Ethica.Pars1.Axioms
import Ethica.Pars1.Propositions

namespace Ethica.Pars1

universe u

/-! ### Section 1 — the counting framework (GAP-8a). -/

section definitions
variable {Thing : Type u} [EthicaWorld Thing]
open EthicaWorld

/-- `hasMoreRealityThan x y` : `x` has at least as much reality as
    `y`, read *qualitatively* as attribute-dominance — every
    attribute `y` has, `x` also has. This is the Della Rocca
    constitutive reading of "reality" (reality is *made of*
    attributes; Def. IV grounds it). We deliberately do **not**
    introduce a quantitative "measure of reality" real number or
    order: Spinoza's text supplies no such measure, and the
    qualitative dominance relation is all Prop. IX's demonstration
    ("patet ex definitione 4") actually needs. -/
def hasMoreRealityThan (x y : Thing) : Prop :=
  ∀ a, Attribute a y → Attribute a x

/-- `hasAtLeastNAttributes s n` : `s` has at least `n` *distinct*
    attributes, encoded cardinality-free via an injection from
    `Fin n`. This is GAP-8a's missing counting framework: it lets us
    quantify over "how many attributes" without committing to any
    particular cardinal-arithmetic library (none is imported here —
    `Fin n` and its core lemmas suffice). -/
def hasAtLeastNAttributes (s : Thing) (n : Nat) : Prop :=
  ∃ f : Fin n → Thing, (∀ i, Attribute (f i) s) ∧ (∀ i j, f i = f j → i = j)

/-- `HasInfiniteAttributes s` : `s` has at least `n` distinct
    attributes for *every* `n` — the direct mechanisation of Def.
    VI's "infinitis attributis" clause. Before this file, GAP-8a's
    complaint was that this claim was not even *stateable*; it now
    is, via `hasAtLeastNAttributes`. Whether it is ever *true* of
    God is a separate question — see the collapse theorem below. -/
def HasInfiniteAttributes (s : Thing) : Prop :=
  ∀ n, hasAtLeastNAttributes s n

end definitions

/-! ### Section 2 — Propositio IX. -/

section prop9
variable {Thing : Type u} [EthicaWorld Thing] [Pars1Axioms Thing]
open EthicaWorld

/-! ## Propositio IX

  Latin: *Quo plus realitatis aut esse unaquaeque res habet eo plura
         attributa ipsi competunt.*
  Elwes: "The more reality or being a thing has, the greater the
          number of its attributes (Def. iv.)."

  Spinoza's *demonstratio* is a single line: "*Patet ex definitione
  4*" — it follows directly from Def. IV. Under the constitutive
  reading of reality adopted above (`hasMoreRealityThan`), that is
  literally true: the proposition becomes a transfer theorem for
  attribute-counts, and its proof is genuinely one line of
  bookkeeping. No new axiom is used — `hasMoreRealityThan`'s
  hypothesis directly supplies, for each attribute of `y`, the
  corresponding attribute of `x`. -/

omit [Pars1Axioms Thing] in
/-- Prop. IX: if `x` has more reality than `y` (attribute-dominance)
    and `y` has at least `n` attributes, then `x` has at least `n`
    attributes too. Proof: reuse `y`'s witnessing injection `f`;
    each `Attribute (f i) y` transfers to `Attribute (f i) x`
    pointwise via `h`; injectivity is verbatim (the same `f`, the
    same proof). -/
theorem prop_9_moreRealityMoreAttributes
    (x y : Thing) (h : hasMoreRealityThan x y)
    (n : Nat) (hy : hasAtLeastNAttributes y n) : hasAtLeastNAttributes x n := by
  obtain ⟨f, hattr, hinj⟩ := hy
  exact ⟨f, fun i => h (f i) (hattr i), hinj⟩

/-- Prop. IX corollary: God, as the substance with maximal reality
    (every substance's attribute is also His, A15), has more reality
    than any substance. Direct application of A15
    (`ax_IsGod_has_attribute_of`) — `hasMoreRealityThan g s` unfolds
    to exactly A15's conclusion schema. -/
theorem prop_9_cor_godMaximalReality
    (g : Thing) (hgod : IsGod g) (s : Thing) (hs : Substance s) :
    hasMoreRealityThan g s := by
  intro a ha
  exact Pars1Axioms.ax_IsGod_has_attribute_of g s a hgod hs ha

end prop9

/-! ## The attribute-collapse theorem

  **The discovery.** In any `Pars1Axioms` world containing a God,
  EVERY attribute of EVERY substance is identical to God. Def. VI's
  "constantem infinitis attributis" is therefore not merely
  unformalised (GAP-8a) but **unsatisfiable** in the present
  register: God cannot have even two distinct attributes, let alone
  infinitely many.

  **Anatomy of the collapse.** Five commitments interact, none of
  them new:

  1. Attributes inhabit `Thing` itself, not some separate universe
     of "ways of being" — the Prop. X scholium reading, already
     baked into `Attribute a s`'s type (`a : Thing`).
  2. A10 (`ax_attribute_perSe`) makes any attribute of a substance
     per se conceived.
  3. A8 (`ax_inItself_iff_perSeConceived`) upgrades "per se
     conceived" to "in itself" — so every attribute *is itself a
     substance* (`attribute_is_substance` below).
  4. A14 (`ax_substance_has_attribute`) then gives that
     substance-which-is-an-attribute an attribute of its own.
  5. A15 (`ax_IsGod_has_attribute_of`) hands that further attribute
     to God, and A12 (`ax_substanceIdByAttribute`) identifies the
     original attribute with God, since both now share the same
     further attribute.

  **Scholarly location.** Bennett 1984 §16 declines exactly the A8
  coextension when the subject is an attribute — his worry is that
  attributes are "basic ways of being", not full-blown things that
  could themselves have attributes. The collapse below vindicates
  that caution at kernel level: granting A8 unrestrictedly (as
  Pars1Axioms does) forces every attribute to substance-hood, and
  the rest of the register does the rest. The result also formally
  validates the Ep. 9 (to de Vries) identity reading of substance
  and attribute — "one and the same thing, ... only distinguished in
  respect of the different names by which it is called" — and shows
  the register cannot simultaneously hold that identity reading AND
  attribute plurality once a God exists. Read this way, the
  subjective/objective attribute controversy (Wolfson's attributes as
  intellect-relative appearances vs. Gueroult's attributes as
  objective aspects of substance) becomes, in this register, a forced
  choice rather than a standing interpretive option: whichever side
  one takes, a Spinozistic God with more than one attribute is not a
  model of `Pars1Axioms`.

  **Escape routes**, each naming the commitment it would revise:

  (i) restrict A12 (`ax_substanceIdByAttribute`) to non-attribute
      substances — blocks the final identification step;
  (ii) weaken A10/A8's bite specifically on attributes (Bennett's own
       line) — blocks step 3, the substance-hood of attributes;
  (iii) type attributes off the `Thing` universe entirely, giving
        them their own type distinct from substances/modes — blocks
        step 1 at the ground floor.

  Each is a genuine revision of a Section III / Section I commitment,
  not a bug fix. Tracked as a new GAP (the docs batch assigns the
  number); referenced generically here as "the attribute-typing gap".

  **Cross-reference.** `Models/MultiAttribute.lean` shows attribute
  plurality IS consistent with the *full* register — in GODLESS
  worlds. The incompatibility is not with `Pars1Axioms` as such but
  specifically between a God-existence commitment (A27,
  `Theologia.lean`) and plurality: the moment a witness for `IsGod`
  is admitted anywhere in the model, the collapse theorem below caps
  every substance at exactly one attribute. -/

section collapse
variable {Thing : Type u} [EthicaWorld Thing] [Pars1Axioms Thing]
open EthicaWorld

/-- Every attribute of a substance is itself a substance. Proof: A10
    gives `perSeConceived a`; A8's `.mpr` direction upgrades that to
    `inItself a`; the two conjoin into `Substance a`. -/
theorem attribute_is_substance (a s : Thing) (h : Attribute a s) : Substance a :=
  ⟨(Pars1Axioms.ax_inItself_iff_perSeConceived a).mpr
      (Pars1Axioms.ax_attribute_perSe a s h),
    Pars1Axioms.ax_attribute_perSe a s h⟩

/-- **The attribute-collapse theorem.** If `g` is God, then *every*
    attribute of *every* substance equals `g`. Proof chain: `a` is a
    substance (`attribute_is_substance`); A14 gives `a` its own
    attribute `c`; A15 hands `c` to `g` (since `a` is a substance and
    `g` is God); A12 identifies `a` with `g`, since both now share
    the attribute `c`. -/
theorem attribute_collapse
    (g : Thing) (hgod : IsGod g) (s a : Thing) (h : Attribute a s) : a = g := by
  have hSubA : Substance a := attribute_is_substance a s h
  obtain ⟨c, hc⟩ := Pars1Axioms.ax_substance_has_attribute a hSubA
  have hcg : Attribute c g :=
    Pars1Axioms.ax_IsGod_has_attribute_of g a c hgod hSubA hc
  exact Pars1Axioms.ax_substanceIdByAttribute a g c hc hcg

/-- Specialisation of `attribute_collapse` to God's own attributes:
    the only thing God can perceive as constituting His essence is
    God Himself. -/
theorem god_is_own_only_attribute
    (g : Thing) (hgod : IsGod g) (a : Thing) (h : Attribute a g) : a = g :=
  attribute_collapse g hgod g a h

/-- God cannot have two distinct attributes. Given an alleged
    injection `f : Fin 2 → Thing` witnessing two attributes of `g`,
    `god_is_own_only_attribute` forces both `f 0` and `f 1` to equal
    `g`, so `f 0 = f 1`; injectivity then forces `(0 : Fin 2) = 1`,
    which is false. -/
theorem god_no_two_attributes
    (g : Thing) (hgod : IsGod g) : ¬ hasAtLeastNAttributes g 2 := by
  intro ⟨f, hattr, hinj⟩
  have h0 : f 0 = g := god_is_own_only_attribute g hgod (f 0) (hattr 0)
  have h1 : f 1 = g := god_is_own_only_attribute g hgod (f 1) (hattr 1)
  have hff : f 0 = f 1 := h0.trans h1.symm
  exact absurd (hinj 0 1 hff) (by decide)

/-- Def. VI's "*constantem infinitis attributis*" clause is
    unsatisfiable for any God in this register: `HasInfiniteAttributes
    g` would in particular give `hasAtLeastNAttributes g 2`, which
    `god_no_two_attributes` rules out. -/
theorem def6_infinitis_attributis_unsatisfiable
    (g : Thing) (hgod : IsGod g) : ¬ HasInfiniteAttributes g := by
  intro h
  exact god_no_two_attributes g hgod (h 2)

end collapse

end Ethica.Pars1
