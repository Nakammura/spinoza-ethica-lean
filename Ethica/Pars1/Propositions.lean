/-
  Spinoza, *Ethica* Pars I — Propositiones (I, II, IV, X, …).

  This file walks the propositions of Pars I in order, proving each
  one in Lean from prior definitions, axioms, and earlier propositions.

  -- Strategy --------------------------------------------------------
  Spinoza's demonstrations frequently invoke prior items by their
  standard reference (e.g. "per Def. III"). We mirror this: each
  proof's tactic block cites the same Definition / Axiom / Proposition
  Spinoza cites, then closes the goal in Lean's logic.

  Where a Spinoza demonstration is too informal to mechanise directly,
  we either supply an auxiliary axiom (placed in `Axioms.lean`,
  catalogued in `docs/auxiliary_axioms.md`) or formalise the modern
  reconstruction following Curley / Garrett / Della Rocca. Every
  divergence is tracked in `docs/gaps.md`.

  -- Section structure ----------------------------------------------
  Theorems are split into two sections by what typeclass instance
  they actually need: `pure_definitional` for theorems that follow
  from `EthicaWorld` alone (because `sameNature` is now a derived
  notion — see GAP-2), and `needs_axioms` for theorems that consume
  `Pars1Axioms`. Prop. III lives in `Causation.lean` because it needs
  the causal layer (`CausalAxioms`).
-/
import Ethica.Pars1.Definitions
import Ethica.Pars1.Axioms
import Ethica.Pars1.Causation

namespace Ethica.Pars1

universe u

/-! ### Section 1 — propositions that need only the definitional layer.

  Because GAP-2 was closed by deriving `sameNature` from
  `Attribute`, Prop. II reduces to a one-line analytic move and does
  not need `Pars1Axioms`. -/

section pure_definitional
variable {Thing : Type u} [EthicaWorld Thing]
open EthicaWorld

/-! ## Propositio II

  Latin: *Duae substantiae diversa attributa habentes nihil inter se
         commune habent.*
  Elwes: "Two substances, whose attributes are different, have
          nothing in common."

  Spinoza's demonstration cites Def. III (substances are per se
  conceived; the conception of one does not involve the conception
  of another). With `sameNature x y := ∃ a, Attribute a x ∧ Attribute
  a y` (Della Rocca; closes GAP-2), the proposition reduces to an
  analytic move from the definition of `sameNature`. The classical
  Spinozistic demonstration via Def. III + A5 is recoverable as
  `prop_2_via_def3` in a future module that develops the substantive
  A5 path; the present proof is the Della-Rocca short form, not the
  Spinoza-textual one. -/

/-- Prop. II (Della-Rocca form): if two things share no attribute,
    they share no nature. No substance-side hypotheses are needed,
    since `Attribute a _` already carries `Substance _`. -/
theorem prop_2_distinctSubstancesShareNothing
    (x y : Thing)
    (hdiff : ∀ a, ¬ (Attribute a x ∧ Attribute a y))
    : ¬ sameNature x y := by
  intro ⟨a, hax, hay⟩
  exact hdiff a ⟨hax, hay⟩

end pure_definitional

/-! ### Section 2 — propositions that consume `Pars1Axioms`. -/

section needs_axioms
variable {Thing : Type u} [EthicaWorld Thing] [Pars1Axioms Thing]
open EthicaWorld

/-! ## Propositio I (disjointness fragment)

  Latin: *Substantia prior est natura suis affectionibus.*
  Elwes EN: "Substance is by nature prior to its modifications
            [accidents]."

  Spinoza's demonstration (*Patet ex Definitione III et V.*) appeals
  to the *priority by nature* of substance over modes — a claim of
  asymmetric conceptual dependence (Curley 1988, ch. 1; Bennett 1984
  §16). What we mechanise below is the *disjointness fragment*: no
  thing is both a substance and a mode. The full priority claim
  (asymmetric conceptual dependence: every mode is conceived through
  some substance, but no substance is conceived through any mode)
  is tracked as GAP-6 and awaits a `conceptualDep` relation. The
  theorem name reflects what is actually proved. -/

/-- Prop. I (disjointness fragment): a substance is not a mode.
    Proved via A1 + A1ₑ. -/
theorem prop_1_substanceDisjointFromModes
    (x : Thing) (hsub : Substance x) : ¬ Mode x := by
  intro hmode
  have hself  : inItself  x := hsub.1
  have hother : inAnother x := hmode.1
  exact Pars1Axioms.ax1_exclusive x ⟨hself, hother⟩

/-! ## Propositio III

  See `Ethica/Pars1/Causation.lean` for the substantive proof of
  Prop. III. The causal predicate `Cause` and substantive A4-A5 live
  there to keep this file's import surface minimal. -/

/-! ## Propositio IV

  Latin: *Duae aut plures res distinctae vel inter se distinguuntur ex
         diversitate attributorum substantiarum vel ex diversitate
         earundem affectionum.*
  Elwes: "Two or more distinct things are distinguished from one
          another, either by the difference of the attributes of the
          substances, or by the difference of their modifications."

  Demonstration: *Omnia quae sunt vel in se vel in alio sunt (per
  axioma 1) hoc est (per definitiones 3 et 5) extra intellectum
  nihil datur praeter substantias earumque affectiones.*

  We mechanise the *partition content* Spinoza uses downstream
  (in Props. V, VI): every existent thing is either a substance or
  a mode. Proved from A1 plus the parallelism axioms A8/A9. -/

/-- Prop. IV (partition form): every thing is either a substance or
    a mode. -/
theorem prop_4_partition (x : Thing) : Substance x ∨ Mode x := by
  rcases Pars1Axioms.ax1_inItselfOrInAnother x with hself | hother
  · left
    exact ⟨hself,
      (Pars1Axioms.ax_inItself_iff_perSeConceived x).mp hself⟩
  · right
    exact ⟨hother,
      (Pars1Axioms.ax_inAnother_iff_conceivedThroughAnother x).mp
        hother⟩

/-- Prop. IV (full distinguishability form): any two distinct
    things fall into one of the four cases dictated by the
    substance/mode partition. The "both substances" case carries
    the additional content that they cannot share an attribute
    (Spinoza's "ex diversitate attributorum substantiarum" clause —
    contrapositive of A12).

    The "differ in modifications" clause for the both-modes case is
    not given internal structure here; mode-individuation by
    affection awaits Pars II's body / mode machinery.

    **Note on textual scope**:
    Spinoza's Prop. IV *demonstratio* addresses only same-category
    distinctions — `(substance, substance)` and `(mode, mode)` —
    treating mixed-category distinction as trivial (different
    categories already entail distinctness, so Spinoza does not
    enumerate the cross-category cases). The Lean form here lists
    all four cases for exhaustiveness; the two mixed cases
    (`Substance ∧ Mode` and `Mode ∧ Substance`) **exceed
    Spinoza's textual coverage** but are required by Lean's type
    system to make the conclusion total over distinct pairs. This
    is a cost of mechanisation, not a textual divergence. -/
theorem prop_4_distinguishedByAttributesOrCategory
    (x y : Thing) (hxy : x ≠ y) :
    (Substance x ∧ Substance y ∧
        ∀ a, ¬ (Attribute a x ∧ Attribute a y)) ∨
    (Mode x ∧ Mode y) ∨
    (Substance x ∧ Mode y) ∨
    (Mode x ∧ Substance y) := by
  rcases prop_4_partition x with hsx | hmx
  · rcases prop_4_partition y with hsy | hmy
    · left
      refine ⟨hsx, hsy, ?_⟩
      intro a ⟨ha_x, ha_y⟩
      exact hxy
        (Pars1Axioms.ax_substanceIdByAttribute x y a ha_x ha_y)
    · right; right; left
      exact ⟨hsx, hmy⟩
  · rcases prop_4_partition y with hsy | hmy
    · right; right; right
      exact ⟨hmx, hsy⟩
    · right; left
      exact ⟨hmx, hmy⟩

/-! ## Propositio IX (deferred)

  Latin: *Quo plus realitatis aut esse unaquaeque res habet eo plura
         attributa ipsi competunt.*

  Spinoza's demonstration is *patet ex definitione 4* — a single
  line. Mechanising "more reality → more attributes" requires a
  measure of reality and a counting framework we have not yet
  introduced. Deferred — see `docs/coverage.md`. -/

/-! ## Propositio X

  Latin: *Unumquodque unius substantiae attributum per se concipi
         debet.*
  Elwes: "Each particular attribute of the one substance must be
          conceived through itself."

  Demonstration: *Attributum enim est id quod intellectus de
  substantia percipit tanquam ejus essentiam constituens (per
  definitionem 4) adeoque (per definitionem 3) per se concipi debet.*

  Mechanisation: A10 (post-review form) bridges `Attribute a s` to
  `perSeConceived a` directly. -/

theorem prop_10_attributePerSe (a s : Thing) (h : Attribute a s)
    : perSeConceived a :=
  Pars1Axioms.ax_attribute_perSe a s h

/-! ## Propositio V

  Latin: *In rerum natura non possunt dari duae aut plures
         substantiae ejusdem naturae sive attributi.*
  Elwes: "There cannot exist in the universe two or more substances
          having the same nature or attribute."

  Spinoza's *demonstratio* (per Prop. IV + Prop. I + Def. III + A6)
  is widely judged to require additional commitment to go through
  (Bennett 1984 §17; Garrett 1990; Della Rocca 2008 ch. 2). We
  therefore commit to
  the substantive content of Prop. V via A12
  (`ax_substanceIdByAttribute`), making the load-bearing
  metaphysical commitment visible at the axiom layer rather than
  hidden in a faux-derivation. See `auxiliary_axioms.md` Section III
  for the philosophical record. -/

/-- Prop. V: two substances sharing an attribute are identical.
    Direct application of A12. -/
theorem prop_5_uniqueSubstancePerAttribute
    (s₁ s₂ a : Thing) (h₁ : Attribute a s₁) (h₂ : Attribute a s₂)
    : s₁ = s₂ :=
  Pars1Axioms.ax_substanceIdByAttribute s₁ s₂ a h₁ h₂

/-! ## Propositio VII

  Latin: *Ad naturam substantiae pertinet existere.*
  Elwes: "Existence belongs to the nature of substance."

  Spinoza's *demonstratio* chains Prop. VI corollary with an
  unstated PSR-flavoured commitment (see A13's docstring in
  `Axioms.lean` for the full argument). We commit Prop. VII at the
  axiom layer via A13; the *natureRequiresExistence* form is
  recovered on demand via A11. -/

theorem prop_7_existenceBelongsToSubstance
    (s : Thing) (hs : Substance s) : involvesExistence s :=
  Pars1Axioms.ax_substance_involves_existence s hs

/-- Prop. VII corollary: the *natureRequiresExistence* form. Spinoza's
    Def. I gives the two clauses of *causa sui* as equivalent (A11),
    so once Prop. VII establishes `involvesExistence`, we get the
    other half automatically. This is the first place A11 is
    load-bearing. -/
theorem prop_7_natureRequiresExistence
    (s : Thing) (hs : Substance s) : natureRequiresExistence s :=
  (Pars1Axioms.ax_causaSui_iff s).mp
    (Pars1Axioms.ax_substance_involves_existence s hs)

/-- Prop. VII full form: every substance is *causa sui*. -/
theorem prop_7_substanceIsCausaSui
    (s : Thing) (hs : Substance s) : causaSui s :=
  Pars1Axioms.ax_substance_involves_existence s hs

/-! ## Propositio VIII

  Latin: *Omnis substantia est necessario infinita.*
  Elwes: "Every substance is necessarily infinite."

  Demonstration: *Substantia unius attributi non nisi unica existit
  (per propositionem 5) et ad ipsius naturam pertinet existere (per
  propositionem 7). Erit ergo de ipsius natura vel finita vel
  infinita existere. At non finita. Nam (per definitionem 2) deberet
  terminari ab alia ejusdem naturae quae etiam necessario deberet
  existere (per propositionem 7) adeoque darentur duae substantiae
  ejusdem attributi, quod est absurdum (per propositionem 5).*

  Mechanisation: prove the contrapositive — no substance is
  *finitumInSuoGenere*. Suppose `s` is finite-after-its-kind via
  some `t ≠ s` of same nature. The shared nature gives a shared
  attribute, and A12 forces `s = t`, contradicting `s ≠ t`.

  The "Spinoza vel finita vel infinita" disjunction does not appear
  explicitly in the proof — once we have ¬ finite, the absolute
  infinity claim ("infinitum simpliciter", Def. VI) requires
  Def. VI's substantive content (GAP-8). The current theorem proves
  ¬ finite, which is what Spinoza's argument actually establishes;
  the absolute-infinity reading awaits GAP-8. -/

/-- Note on the unused `_hs : Substance s` hypothesis: kept for
    textual fidelity to Spinoza's "Omnis substantia …" universal
    quantification, even though `sameNature` carries `Substance` via
    `Attribute`. Compare `prop_2_distinctSubstancesShareNothing`,
    which dropped its redundant `Substance` hypotheses (review
    §1.3); the stylistic difference is intentional and noted here
    so the inconsistency is *signed*, not accidental. -/
theorem prop_8_substanceIsNotFinite
    (s : Thing) (_hs : Substance s) : ¬ finitumInSuoGenere s := by
  intro ⟨t, hne, hsame, _hlim⟩
  obtain ⟨a, ha_s, ha_t⟩ := hsame
  exact hne
    (Pars1Axioms.ax_substanceIdByAttribute s t a ha_s ha_t)

/-! ## Propositio XIV

  Latin: *Praeter Deum nulla dari neque concipi potest substantia.*
  Elwes: "Besides God, no substance can be granted or conceived."

  Demonstration: God, being absolutely infinite, has every
  attribute (per Def. VI). Any other substance `s` has some
  attribute `a`. But God also has `a`. Hence by Prop. V (A12),
  `s = God`.

  A14 and A15 are committed at the axiom layer (`Pars1Axioms`
  Section III), so `prop_14` is a short-form theorem, with the two
  Section III axioms doing the load-bearing work transparently.

  Note: encoding A14 / A15 as `private axiom` skeleton premises
  would produce kernel-level inconsistency in conjunction with
  `Models/TwoSubstance.lean`'s counter-witness; committing them as
  `Pars1Axioms` fields avoids this while keeping the Section III
  status explicit. -/

theorem prop_14_onlyGodIsSubstance
    (g : Thing) (hgod : IsGod g)
    (s : Thing) (hs : Substance s)
    : s = g := by
  obtain ⟨a, ha_s⟩ := Pars1Axioms.ax_substance_has_attribute s hs
  have ha_g : Attribute a g :=
    Pars1Axioms.ax_IsGod_has_attribute_of g s a hgod hs ha_s
  exact prop_5_uniqueSubstancePerAttribute s g a ha_s ha_g

end needs_axioms

/-! ### Section 3 — propositions that need the causal layer.

  Prop. VI uses Prop. III's contrapositive (`cause_implies_sameNature`,
  in `Causation.lean`) plus A12. Prop. XIV lives in Section 2 rather
  than here because its (skeletal) proof consumes only `Pars1Axioms`
  + private premise axioms — no causal machinery. -/

section needs_causal_axioms
variable {Thing : Type u} [CausalWorld Thing] [CausalAxioms Thing]
open EthicaWorld CausalWorld

/-! ## Propositio VI

  Latin: *Una substantia non potest produci ab alia substantia.*
  Elwes: "One substance cannot be produced by another substance."

  Demonstration: *In rerum natura non possunt dari duae substantiae
  ejusdem attributi (per propositionem praecedentem [V]) hoc est
  (per propositionem 2) quae aliquid inter se commune habent.
  Adeoque (per propositionem 3) una alterius causa esse nequit sive
  ab alia non potest produci.*

  Mechanisation: contrapose Prop. III via `cause_implies_sameNature`,
  extract the shared attribute, apply A12 to identify the alleged
  two substances. Distinctness contradiction follows. -/

theorem prop_6_substanceNotProducedByAnother
    (s₁ s₂ : Thing) (hs₁ : Substance s₁) (hs₂ : Substance s₂)
    (hdistinct : s₁ ≠ s₂)
    : ¬ Cause s₁ s₂ := by
  intro hcause
  -- From Prop. III contrapositive (Causation.lean):
  --   Cause s₁ s₂ + both Substance ⇒ sameNature s₁ s₂.
  have hsame : sameNature s₁ s₂ :=
    cause_implies_sameNature s₁ s₂ hs₁ hs₂ hcause
  -- sameNature s₁ s₂ unfolds to ∃ a, Attribute a s₁ ∧ Attribute a s₂.
  obtain ⟨a, ha₁, ha₂⟩ := hsame
  -- A12 forces s₁ = s₂.
  exact hdistinct
    (Pars1Axioms.ax_substanceIdByAttribute s₁ s₂ a ha₁ ha₂)

end needs_causal_axioms

end Ethica.Pars1
