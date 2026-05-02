/-
  Spinoza, *Ethica* Pars I — Causation layer.

  This module promotes A4 from its `True` placeholder in
  `Axioms.lean` to substantive form, by introducing the primitive
  relation `Cause : Thing → Thing → Prop` and an "intelligibility
  through" relation `intelligibleThrough`.

  A3 — Spinoza's *ontological-necessitation* axiom — is left as a
  placeholder at this layer (see GAP-7 in `docs/gaps.md`); its proper
  modal form ("∀ world, cause exists → effect exists") awaits the
  modal layer.

  A5 (substantive form) is restricted to *substances* below. Without
  this restriction, the Della Rocca closure of GAP-2 (which makes
  `sameNature` derived from `Attribute`, hence substance-only) would
  collectively force `¬ Cause m₁ m₂` for any pair of modes — wiping
  out the finite-mode causation Pars II–V depend on. Tracked as the
  soundness fix from the review of 2026-05-02 §3.1.

  Latin (recap):
    A3. Ex data causa determinata necessario sequitur effectus, et
        contra, si nulla detur determinata causa, impossibile est ut
        effectus sequatur.
    A4. Effectus cognitio a cognitione causae dependet et eandem
        involvit.
    A5. Quae nihil commune cum se invicem habent, etiam per se
        invicem intelligi non possunt, sive conceptus unius alterius
        conceptum non involvit.

  Reading: Spinoza's epistemology is causal-rationalist. To know an
  effect *just is* to know it through its cause; to be intelligible
  through `y` is to stand in a conceptual dependency on `y`. Prop. III
  ("things with nothing in common cannot be cause of each other")
  drops out of A4 + A5(restricted) once both are stated substantively.
-/
import Ethica.Pars1.Definitions
import Ethica.Pars1.Axioms

namespace Ethica.Pars1

universe u

/-- The causal layer extends `EthicaWorld` with the primitives needed
    to give A4-A5 substantive content. We keep this separate from
    `EthicaWorld` so the bare definitional layer stays minimal. -/
class CausalWorld (Thing : Type u) extends EthicaWorld Thing where
  /-- `Cause c e` reads "c is a (determinate) cause of e". -/
  Cause : Thing → Thing → Prop
  /-- `intelligibleThrough x y` : `x` is conceived / understood
      through `y`. The Latin "per … intelligi" / "conceptus … involvit"
      cluster. A4 and A5 both turn on this relation. -/
  intelligibleThrough : Thing → Thing → Prop

variable {Thing : Type u} [CausalWorld Thing]
open EthicaWorld CausalWorld

/-- Substantive axiomatic backbone for the causal layer.

    `CausalAxioms` extends `Pars1Axioms`: any `EthicaWorld` committed
    to Spinoza's causal-epistemic axioms must also satisfy the
    base-layer axioms. This avoids forcing downstream theorems to
    juggle two typeclass instances.

    The pre-review draft carried `ax3_causeGroundsIntelligibility`
    and `ax4_effectIntelligibleThroughCause` as separate fields with
    *literally identical* signatures; the duplication has been
    removed. A3's ontological-necessitation content (distinct from
    A4's epistemic content) is now tracked as GAP-7 and awaits the
    modal layer. -/
class CausalAxioms (Thing : Type u) [CausalWorld Thing]
    extends Pars1Axioms Thing : Prop where
  /-- A4 (substantive): knowledge of an effect involves knowledge of
      its cause. The mechanised form: if `c` causes `e`, then any
      account of `e` runs through `c` — i.e. `e` is intelligible
      through `c`. -/
  ax4_effectIntelligibleThroughCause :
    ∀ c e : Thing, Cause c e → intelligibleThrough e c

  /-- A5 (substantive, causal form, *substance-restricted*): two
      substances with no shared nature are not intelligible through
      one another.

      The substance-restriction is the soundness fix from the review
      of 2026-05-02 §3.1: with `sameNature` derived as
      `∃ a, Attribute a x ∧ Attribute a y` (GAP-2 path b), the
      substance-implicit nature of `sameNature` would, without this
      restriction, render `¬ Cause m₁ m₂` provable for every pair of
      modes — collapsing the Pars II/III machinery. Restricting A5 to
      substances cleanly preserves Prop. III's substance-side use
      while leaving mode-causation unconstrained at this layer. The
      fully general form awaits the modal layer's `hasAttribute`. -/
  ax5_noCommonNoIntelligibility :
    ∀ x y : Thing, Substance x → Substance y →
      ¬ sameNature x y → ¬ intelligibleThrough x y

/-! ## A small helper: symmetry of `sameNature`. -/

set_option linter.unusedSectionVars false in
/-- `sameNature` is symmetric — immediate from the definition. The
    `[CausalWorld Thing]` instance is unused here (only `EthicaWorld`
    is needed), but moving the lemma out of this section adds churn;
    we suppress the linter locally. -/
theorem sameNature_symm {x y : Thing} (h : sameNature x y)
    : sameNature y x := by
  obtain ⟨a, hax, hay⟩ := h
  exact ⟨a, hay, hax⟩

/-! ## Propositio III — substantive form

  Latin: *Quae res nihil commune inter se habent, earum una alterius
         causa esse non potest.*
  Elwes: "Things which have nothing in common cannot be one the
          cause of the other."

  Demonstration: *Si nihil inter se commune habent, ergo (per Axiom 5)
  nec per se invicem possunt intelligi, adeoque (per Axiom 4) una
  alterius causa esse non potest.*

  Mechanisation: contrapositive. Suppose `x` causes `y`. Then by A4
  `y` is intelligible through `x`. But `¬ sameNature x y` (with both
  substances) blocks any such intelligibility by the substance-form
  of A5. Contradiction.

  The hypotheses now require both `x` and `y` to be substances —
  consistent with Spinoza's actual demonstration path through Prop. II,
  even though his Prop. III statement is in terms of "things"
  generally. The general form is recoverable at the modal layer. -/
theorem prop_3_noCommonNoCause [CausalAxioms Thing]
    (x y : Thing) (hx : Substance x) (hy : Substance y)
    (hno_common : ¬ sameNature x y)
    : ¬ Cause x y := by
  intro hcause
  -- A4: x causes y  →  y intelligible through x
  have hint : intelligibleThrough y x :=
    CausalAxioms.ax4_effectIntelligibleThroughCause x y hcause
  -- A5 (substance-restricted, contrapositive direction):
  --   Substance y, Substance x, ¬ sameNature y x → ¬ intelligibleThrough y x
  exact CausalAxioms.ax5_noCommonNoIntelligibility y x hy hx
    (fun h => hno_common (sameNature_symm h)) hint

/-- Symmetric corollary: same conclusion in the other direction.
    Spinoza states Prop. III without privileging a direction; this
    matches that reading. -/
theorem prop_3_noCommonNoCause_symm [CausalAxioms Thing]
    (x y : Thing) (hx : Substance x) (hy : Substance y)
    (hno_common : ¬ sameNature x y)
    : ¬ Cause y x :=
  prop_3_noCommonNoCause y x hy hx
    (fun h => hno_common (sameNature_symm h))

/-! ## Propositio II — Spinoza-textual form (closes GAP-10)

  Latin: *Duae substantiae diversa attributa habentes nihil inter se
         commune habent.*
  Elwes: "Two substances, whose attributes are different, have
          nothing in common."

  Spinoza's *demonstratio*: *Patet etiam ex Def. III. Unaquaeque
  enim debet in se esse, et per se concipi, sive conceptus unius
  conceptum alterius non involvit.*

  The Della-Rocca form `prop_2_distinctSubstancesShareNothing`
  (in `Propositions.lean`) proves `¬ sameNature x y` from disjoint
  attributes by analytic unfolding of `sameNature`. The
  Spinoza-textual form below proves `¬ intelligibleThrough x y`
  from the same hypothesis, routing through A5ₛ — closer to the
  *demonstratio*'s appeal to Def. III + the conceptual-non-involvement
  language ("conceptus unius conceptum alterius non involvit").

  Both forms hold simultaneously; the equivalence is recorded as a
  small lemma below. Closes GAP-10. -/

/-- Prop. II — Spinoza-textual form.

    **Note on the proof routing** (review of 2026-05-02 §A.3):
    this theorem is named "via Def. III" because A5ₛ — which the
    proof invokes — has a substance-restriction whose body unfolds
    to `inItself ∧ perSeConceived` (Def. III). Def. III is
    therefore *encapsulated* in A5ₛ's typing rather than visibly
    chained through the proof body. The truly Spinoza-textual
    demonstration would expand A5ₛ inline using Def. III's
    "conceptus non involvit" language; in the present project
    that expansion is folded into A5ₛ's substance hypotheses by
    the GAP-2 closure (Della-Rocca `sameNature` derivation). The
    name is kept for continuity with GAP-10's title; the proof
    is honest about what it actually consumes. -/
theorem prop_2_via_def3 [CausalAxioms Thing]
    (x y : Thing) (hx : Substance x) (hy : Substance y)
    (hdiff : ∀ a, ¬ (Attribute a x ∧ Attribute a y))
    : ¬ intelligibleThrough x y := by
  have hno : ¬ sameNature x y := by
    intro ⟨a, ha_x, ha_y⟩
    exact hdiff a ⟨ha_x, ha_y⟩
  exact CausalAxioms.ax5_noCommonNoIntelligibility x y hx hy hno

/-- The bridge between Prop. II's two readings — Della-Rocca form
    (`¬ sameNature`) and Spinoza-textual form
    (`¬ intelligibleThrough`) — *is* A5ₛ. This theorem is a
    **documentation alias** making that fact citable by name; it
    has no proof content beyond invoking
    `CausalAxioms.ax5_noCommonNoIntelligibility` (eta-equivalent
    re-statement). Review of 2026-05-02 §A.4. -/
theorem prop_2_forms_equivalent [CausalAxioms Thing]
    (x y : Thing) (hx : Substance x) (hy : Substance y) :
    ¬ sameNature x y → ¬ intelligibleThrough x y :=
  CausalAxioms.ax5_noCommonNoIntelligibility x y hx hy

/-- Contrapositive of Prop. III: if `x` causes `y`, both substances,
    they must share a nature. Used by Prop. VI to extract the shared
    attribute from a hypothesised substance-causation.

    Uses `Classical.byContradiction` directly to keep the term-mode
    proof short. The `by_contra` tactic in Lean 4 core would also
    work and is preferred in tactic-mode contexts. -/
theorem cause_implies_sameNature [CausalAxioms Thing]
    (x y : Thing) (hx : Substance x) (hy : Substance y)
    (hcause : Cause x y) : sameNature x y :=
  Classical.byContradiction fun hno =>
    prop_3_noCommonNoCause x y hx hy hno hcause

end Ethica.Pars1
