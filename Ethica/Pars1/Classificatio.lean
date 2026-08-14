/-
  Spinoza, *Ethica* Pars I — Classificatio (the consecution
  trichotomy, Prop. XXIII, and the A42 demote experiment).

  `Consecutio.lean`'s A42 (`ax_finiteMode_causedByFiniteMode`)
  documents, in its own docstring, that Spinoza's *demonstratio* of
  Prop. XXVIII silently consumes an exhaustiveness premise: every
  mode follows either absolutely from an attribute of God (Prop.
  XXI's route), or from an eternal-and-infinite mode (Prop. XXII's
  route), or from another finite mode (the route Prop. XXVIII itself
  concludes to, by elimination of the first two). That premise is
  Prop. XXIII's content — never stated by Spinoza as an axiom, but
  load-bearing in his own elimination argument ("*at id quod finitum
  est … ab absoluta natura alicujus Dei attributi produci non
  potuit* … *at ex Deo vel aliquo ejus attributo quatenus affectum
  est modificatione quae aeterna et infinita est, sequi etiam non
  potuit* … *debuit ergo sequi* … *a Deo vel aliquo ejus attributo
  quatenus modificatum est modificatione quae finita est*"). This
  file commits that exhaustiveness premise visibly as **A44**
  (`ClassificatioAxioms.ax_consecution_trichotomy`), mechanises the
  qualitative half of Prop. XXIII from it, and then runs the demote
  experiment A42's docstring leaves open: does the trichotomy (A44),
  together with the transfer axioms A40/A41 and the
  consecution-causation bridge A38, derive A42?

  **Answer: YES** — recorded below as `A42_demote_via_trichotomy`.
  A42 is thereby an *equal-strength decomposition* (the A15 pattern
  in the project's demote taxonomy: see `ModalForm.lean`,
  `prop_A15_demote_via_decomposition`, and README's "Demote
  experiments" section), not an independent commitment, relative to
  A44. The substantive residue of Prop. XXVIII's finite-mode-causal
  chain is exactly Prop. XXIII's classification premise — Spinoza's
  own silent exhaustiveness move, now visible as an axiom rather
  than an unstated inference.
-/
import Ethica.Pars1.Definitions
import Ethica.Pars1.Axioms
import Ethica.Pars1.Causation
import Ethica.Pars1.Propositions
import Ethica.Pars1.Inherence
import Ethica.Pars1.Consecutio

namespace Ethica.Pars1

universe u

variable {Thing : Type u} [ConsecutioWorld Thing]
open EthicaWorld CausalWorld InherenceWorld ConsecutioWorld

/-- The classification layer: `ConsecutioAxioms` plus **A44**, the
    consecution trichotomy Prop. XXVIII's *demonstratio* consumes
    silently. -/
class ClassificatioAxioms (Thing : Type u) [ConsecutioWorld Thing]
    extends ConsecutioAxioms Thing : Prop where
  /-- A44 (Section III — substantive commitment; closes GAP-23's
      premise half): every mode arises in one of exactly three ways —
      absolutely from an attribute of God (the immediate infinite
      modes' route, Prop. XXI); from an eternal-and-infinite mode (the
      mediate route, Prop. XXII); or from another finite mode (the
      common order of nature, Prop. XXVIII).

      Spinoza never states this exhaustiveness as a separate premise,
      but his *demonstratio* of Prop. XXVIII consumes it silently: the
      elimination proceeds "*at id quod finitum est … ab absoluta
      natura alicujus Dei attributi produci non potuit* [rules out the
      first horn, Prop. XXI] … *at ex Deo vel aliquo ejus attributo
      quatenus affectum est modificatione quae aeterna et infinita
      est, sequi etiam non potuit* [rules out the second horn, Prop.
      XXII] … *debuit ergo sequi* … *quatenus modificatum est
      modificatione quae finita est*" [lands on the third] — an
      elimination argument that only closes if the three horns are
      jointly exhaustive, a fact Spinoza nowhere argues for
      independently. Bennett 1984 §25 flags the classification as an
      unargued premise of the infinite-mode doctrine.

      Committed visibly. -/
  ax_consecution_trichotomy :
    ∀ x : Thing, Mode x →
      (∃ g a, IsGod g ∧ Attribute a g ∧ followsAbsolutely x a) ∨
      (∃ m, Mode m ∧ Eternal m ∧ ¬ finitumInSuoGenere m ∧ followsFrom x m) ∨
      (∃ y, Mode y ∧ finitumInSuoGenere y ∧ y ≠ x ∧ followsFrom x y)

section classificatio_theorems
variable {Thing : Type u} [ConsecutioWorld Thing] [ClassificatioAxioms Thing]
open EthicaWorld CausalWorld InherenceWorld ConsecutioWorld

/-! ## Propositio XXIII (partial)

  Latin: *Omnis modus qui et necessario et infinitus existit,
         necessario sequi debuit vel ex absoluta natura alicujus
         attributi Dei vel ex aliquo attributo modificato
         modificatione quae et necessario et infinita existit.*
  Elwes: "Every mode, which exists both necessarily and as infinite,
          must necessarily follow either from the absolute nature of
          some attribute of God, or from an attribute modified by a
          modification which exists necessarily, and as infinite."

  Demonstratio: *Modus enim in alio est per quod concipi debet (per
  definitionem 5) hoc est (per propositionem 15) in solo Deo est et
  per solum Deum concipi potest.* … Spinoza argues from Def. V and
  Prop. XV that a necessarily-and-infinitely-existing mode must be
  perceived through some attribute of God taken absolutely — either
  immediately (Prop. XXI) or mediately through a modification that is
  itself necessary and infinite (Prop. XXII).

  **What is mechanised**: the trichotomy itself (A44), specialised to
  any mode `x` — every mode follows either absolutely from an
  attribute of God, or from an eternal-infinite mode, or from another
  finite mode. This is the *classification* content Prop. XXIII's
  argument turns on, made available generally rather than restricted
  to necessarily-infinite modes.

  **Honest gap**: Spinoza's Prop. XXIII additionally EXCLUDES the
  third branch for modes that are themselves necessary-and-infinite —
  his conclusion is a *disjunction of exactly two* horns (absolute or
  mediate-infinite), not the full trichotomy. That exclusion needs a
  finite-source transfer principle ("what follows from a finite mode
  is itself finite") that Spinoza does not state and this
  formalisation does not commit to; without it, nothing here rules
  out a necessarily-infinite mode following from a finite one. The
  full biconditional classification — trichotomy plus the
  finite-source exclusion — remains open (cross-ref GAP-22/GAP-23
  residue; the documentation batch will update `docs/gaps.md` and
  `docs/coverage.md` accordingly). What is mechanised below is the
  trichotomy A44 already commits to, restated as a theorem — a direct
  📜-pattern invocation, exactly as A40/A41 were for Props. XXI/XXII. -/

/-- Prop. XXIII (partial — the trichotomy clause, not the
    necessarily-infinite exclusion): every mode follows either
    absolutely from an attribute of God, or from an eternal-infinite
    mode, or from another finite mode. -/
theorem prop_23_partial_classification
    (x : Thing) (hx : Mode x) :
    (∃ g a, IsGod g ∧ Attribute a g ∧ followsAbsolutely x a) ∨
    (∃ m, Mode m ∧ Eternal m ∧ ¬ finitumInSuoGenere m ∧ followsFrom x m) ∨
    (∃ y, Mode y ∧ finitumInSuoGenere y ∧ y ≠ x ∧ followsFrom x y) :=
  ClassificatioAxioms.ax_consecution_trichotomy x hx

end classificatio_theorems

/-! ## The A42 demote experiment

  Following the project's demote methodology (README "Demote
  experiments"; `ModalForm.lean`'s A12–A15 precedents), we ask: is
  A42 (`ax_finiteMode_causedByFiniteMode`) derivable from a register
  Σ *strictly excluding* A42 itself?

  Lean classes cannot subtract fields from an ancestor, so — mirroring
  the `StatedAxioms` duplication precedent in `Axioms.lean`
  (`StatedAxioms` duplicates `Pars1Axioms`'s A1–A11 field signatures
  verbatim, omitting A12–A15, precisely so a counter-model can
  instantiate the weaker register without automatically inheriting
  the stronger one) — we duplicate the needed field signatures
  verbatim into a fresh class `TrichotomySigma`, extending
  `InherenceAxioms` (which supplies A33–A36 but nothing of A37–A43).

  Σ = {A38, A40, A41, A44} over the stated-plus-inherence base —
  deliberately EXCLUDING A42 (the demote target), A43, and the
  bridges A37/A39, so the derivation below cannot smuggle the target
  back in through an unrelated field. -/

/-- The demote register Σ for the A42 experiment: `InherenceAxioms`
    (A1–A11, A33–A36) plus duplicated signatures for A38
    (`ax_consecution_causation`), A40
    (`ax_absoluteConsecution_eternalInfinite`), A41
    (`ax_infiniteModeTransfer`), and A44
    (`ax_consecution_trichotomy`) — and nothing else from the
    consecution layer. Field-signature duplication follows the
    `StatedAxioms` precedent (`Axioms.lean`) and documents the
    register boundary: no `TrichotomySigma` instance can smuggle in
    A42, A43, A37, or A39, since none of those fields exist here. -/
class TrichotomySigma (Thing : Type u) [ConsecutioWorld Thing]
    extends InherenceAxioms Thing : Prop where
  /-- Duplicates A38 (`ConsecutioAxioms.ax_consecution_causation`). -/
  sig_consecution_causation :
    ∀ x y : Thing, followsFrom x y → Cause y x
  /-- Duplicates A40 (`ConsecutioAxioms.ax_absoluteConsecution_eternalInfinite`). -/
  sig_absoluteConsecution_eternalInfinite :
    ∀ x a g : Thing, IsGod g → Attribute a g → followsAbsolutely x a →
      Eternal x ∧ ¬ finitumInSuoGenere x
  /-- Duplicates A41 (`ConsecutioAxioms.ax_infiniteModeTransfer`). -/
  sig_infiniteModeTransfer :
    ∀ x m : Thing, Mode m → Eternal m → ¬ finitumInSuoGenere m →
      followsFrom x m → Eternal x ∧ ¬ finitumInSuoGenere x
  /-- Duplicates A44 (`ClassificatioAxioms.ax_consecution_trichotomy`). -/
  sig_consecution_trichotomy :
    ∀ x : Thing, Mode x →
      (∃ g a, IsGod g ∧ Attribute a g ∧ followsAbsolutely x a) ∨
      (∃ m, Mode m ∧ Eternal m ∧ ¬ finitumInSuoGenere m ∧ followsFrom x m) ∨
      (∃ y, Mode y ∧ finitumInSuoGenere y ∧ y ≠ x ∧ followsFrom x y)

section a42_demote
variable {Thing : Type u} [ConsecutioWorld Thing] [TrichotomySigma Thing]
open EthicaWorld CausalWorld InherenceWorld ConsecutioWorld

/-- **Full demote of A42 via the trichotomy**: under Σ =
    `TrichotomySigma` (A38 + A40 + A41 + A44 over the stated+inherence
    base, deliberately excluding A42 itself), every finite mode is
    caused by some other, distinct finite mode.

    Proof: case on the trichotomy (`sig_consecution_trichotomy`)
    applied to `x`. Branch 1 (follows absolutely from an attribute of
    God): `sig_absoluteConsecution_eternalInfinite` concludes
    `¬ finitumInSuoGenere x`, directly contradicting the hypothesis
    `hfin`. Branch 2 (follows from an eternal-infinite mode):
    `sig_infiniteModeTransfer` concludes the same contradiction.
    Branch 3 (follows from another finite mode `y`): this is already
    almost the goal — `sig_consecution_causation` turns the surviving
    `followsFrom x y` into `Cause y x`, and the branch's own witness
    supplies the rest. -/
theorem A42_demote_via_trichotomy :
    ∀ x : Thing, Mode x → finitumInSuoGenere x →
      ∃ y, Mode y ∧ finitumInSuoGenere y ∧ y ≠ x ∧ Cause y x := by
  intro x hx hfin
  rcases TrichotomySigma.sig_consecution_trichotomy x hx with h1 | h2 | h3
  · obtain ⟨g, a, hgod, ha, hfa⟩ := h1
    exact absurd hfin
      (TrichotomySigma.sig_absoluteConsecution_eternalInfinite x a g hgod ha hfa).2
  · obtain ⟨m, hm, he, hinf, hf⟩ := h2
    exact absurd hfin
      (TrichotomySigma.sig_infiniteModeTransfer x m hm he hinf hf).2
  · obtain ⟨y, hy, hyfin, hne, hf⟩ := h3
    exact ⟨y, hy, hyfin, hne, TrichotomySigma.sig_consecution_causation x y hf⟩

end a42_demote

/-- Σ ≤ the full register: every `ClassificatioAxioms` instance
    (hence every `ConsecutioAxioms` instance extended with the
    trichotomy) yields a `TrichotomySigma` instance, by forgetting
    the fields Σ does not need (A37, A39, A42, A43). Shows the demote
    is not vacuous relative to the project's actually-committed
    axioms — Σ is genuinely satisfiable by every model this project
    already trusts. -/
instance (priority := 100) trichotomySigma_of_classificatio
    {Thing : Type u} [ConsecutioWorld Thing] [ClassificatioAxioms Thing] :
    TrichotomySigma Thing :=
  { (inferInstance : InherenceAxioms Thing) with
    sig_consecution_causation := ConsecutioAxioms.ax_consecution_causation
    sig_absoluteConsecution_eternalInfinite :=
      ConsecutioAxioms.ax_absoluteConsecution_eternalInfinite
    sig_infiniteModeTransfer := ConsecutioAxioms.ax_infiniteModeTransfer
    sig_consecution_trichotomy := ClassificatioAxioms.ax_consecution_trichotomy }

/-! ### A42 outcome: equal-strength decomposition

  A42 is derivable from Σ = {A38, A40, A41, A44}
  (`A42_demote_via_trichotomy`); the substantive residue is the
  trichotomy A44 itself — Spinoza's silent exhaustiveness premise,
  now a visible commitment. This parallels the A15 outcome in
  `ModalForm.lean` (decomposition into plenitude + god-uniqueness,
  `prop_A15_demote_via_decomposition`): the finite-mode causal chain
  of Prop. XXVIII is exactly as strong as the classification of
  consecution routes Prop. XXIII supplies — no weaker, no stronger.
  Unlike A15's decomposition (which replaces one axiom with *two*,
  neither weaker), A42's decomposition replaces one axiom with a
  register {A38, A40, A41, A44} already committed elsewhere in the
  project for independent reasons (A38 for Prop. XVI Cor. I, A40/A41
  for Props. XXI/XXII) plus exactly one new commitment (A44) — so the
  net new commitment cost of dropping A42 in favour of A44 is a
  *single* axiom, not two. A42 is thereby redundant with the rest of
  `ConsecutioAxioms` once A44 is granted.

  Contrast with A27/A32/A35 (`Axioms.lean`/`Inherence.lean` demote
  notes), which resist decomposition entirely (counter-witnessed in
  `Models/`) — no combination of already-committed axioms derives
  them. A42 joins A13/A14 (equal-strength) and A15 (decomposition) in
  the "demotable" column of the taxonomy, rather than the
  "irreducible" column A12/A15's non-plenitude-alone case occupies.

  The documentation batch updates README's demote table and
  `docs/auxiliary_axioms.md` accordingly. -/

end Ethica.Pars1
