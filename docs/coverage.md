# Coverage Map — Pars I

Status of every Pars I proposition, definition, and structural
component in the Lean formalisation. Updated alongside any change
that adds, removes, or shifts the status of an item.

Status legend:
- ✅ **mechanised** — proved in Lean with no `sorry`.
- 🟡 **partial** — proved in a restricted form (e.g. substance-only),
  with the gap explicitly tracked.
- ⏳ **deferred** — not yet attempted; blocking dependency is named.
- 🚫 **blocked** — cannot proceed without a structural prerequisite
  (e.g. a counting framework, a modal layer).

---

## Definitions (I–VIII)

| # | Subject                       | Status | Notes |
|---|-------------------------------|--------|-------|
| I   | *Causa sui*                 | ✅     | `causaSui` (single-clause); A11 bridges to Spinoza's *sive*-form. |
| II  | *Finitum in suo genere*     | 🟡     | `finitumInSuoGenere` defined with `x ≠ y` clause (Spinoza's "ab **alia**"); under the GAP-2 closure, only meaningful for substances. The `limitedBy` primitive itself is currently **inert** — declared but no axiom constrains it and no theorem consumes it; load-bearing use awaits Pars II body-mode discussion. Mode-restricted reading awaits modal layer's `hasAttribute`. |
| III | *Substantia*                | ✅     | `Substance`. |
| IV  | *Attributum*                | ✅     | `Attribute`. |
| V   | *Modus*                     | ✅     | `Mode`. |
| VI  | *Deus*                      | 🟡 (Pars I) / ✅ (Attributum) | `IsGod` requires ≥1 attribute (third conjunct, **now redundant under A14** but retained for textual fidelity to Spinoza); (a) *infinitis attributis* cardinality — GAP-8a: **STATEABLE** via `hasAtLeastNAttributes`/`HasInfiniteAttributes` (`Realitas.lean`) but **PROVED UNSATISFIABLE** alongside any God in the Pars I register (`def6_infinitis_attributis_unsatisfiable` — the attribute-collapse discovery); consistent only in godless worlds (`Models/MultiAttribute.lean`). **Resolved in the Attributum layer**: `IsGodAttr` (`Ethica/Attributum/Core.lean`) is the same definition with attributes typed in `Attr`, and `Models/InfiniteAttribute.lean`'s `inf_def6_recovered` satisfies the *infinitis attributis* clause outright — GAP-8a ✅, GAP-25 ✅. The Pars I row stays 🟡 because Pars I is frozen. (b) universality over substance attributes — GAP-8b ✅ (closed by A15 promotion). |
| VII | *Liberum / Coactum*         | 🟡     | `Free`/`Constrained` thin aliases; second clause ("ad agendum determinatur") needs Pars II — GAP-9. |
| VIII| *Aeternitas*                | ✅     | `Eternal` (primitive at this layer; modal reconstruction planned). |

---

## Axioms (I–VII + auxiliaries)

| Axiom | Status | Notes |
|-------|--------|-------|
| A1    | ✅     | `ax1_inItselfOrInAnother`. |
| A1ₑ   | ✅     | `ax1_exclusive` (auxiliary, GAP-1). |
| A2    | ✅     | `ax2_perSeOrThroughAnother` (disjunctive form). |
| A3    | 🚫     | `True : Prop` placeholder; ontological-necessitation form needs modal layer — GAP-7. |
| A4    | 🟡     | `True : Prop` in `Pars1Axioms`; substantive form `ax4_effectIntelligibleThroughCause` in `CausalAxioms`. |
| A5    | 🟡     | `True : Prop` in `Pars1Axioms`; substance-restricted substantive form in `CausalAxioms` (review §3.1 fix). General form awaits modal layer. |
| A6    | 🚫     | `True : Prop` placeholder; needs Pars II idea/ideatum machinery. |
| A7    | ✅     | `ax7_conceivableAsNonExistent`. |
| A8    | ✅     | `ax_inItself_iff_perSeConceived` (auxiliary, GAP-4). PSR-flavoured. |
| A9    | ✅     | `ax_inAnother_iff_conceivedThroughAnother` (auxiliary, GAP-4). |
| A10   | ✅     | `ax_attribute_perSe` (auxiliary, GAP-5; strengthened post-review §3.2). |
| A11   | ✅     | `ax_causaSui_iff` (auxiliary, review §2.4). |
| A12   | ✅     | `ax_substanceIdByAttribute` (auxiliary, **substantive metaphysical commitment** — see auxiliary_axioms.md Section III; GAP-11 tracks possible modal-layer demotion). |
| A13   | ✅     | `ax_substance_involves_existence` (auxiliary, **substantive metaphysical commitment** — Section III; GAP-12 tracks possible modal-layer demotion). |
| A14   | ✅     | `ax_substance_has_attribute` (auxiliary, **substantive metaphysical commitment** — Section III; closes GAP-13). |
| A15   | ✅     | `ax_IsGod_has_attribute_of` (auxiliary, **substantive metaphysical commitment** — Section III; closes GAP-8b. Counter-witnessed by `Models/TwoSubstance.lean` — Bennett-line bench). |

---

## Propositions (I–XXXVI)

Pars I has 36 propositions. Status of each:

| Prop | Statement (abbrev.)                                             | Status | Lean name / location |
|------|-----------------------------------------------------------------|--------|----------------------|
| I    | Substance is by nature prior to its modifications.              | 🟡     | `prop_1_substanceDisjointFromModes` (disjointness only; priority — GAP-6). |
| II   | Two substances of different attributes have nothing in common.  | ✅     | Two readings, both mechanised: `prop_2_distinctSubstancesShareNothing` (Della-Rocca form, in `Propositions.lean`) and `prop_2_via_def3` (Spinoza-textual form via A5ₛ, in `Causation.lean`). `prop_2_forms_equivalent` records the bridge. Closes GAP-10. |
| III  | Things with nothing in common cannot be cause of each other.    | 🟡     | `prop_3_noCommonNoCause` in `Causation.lean` (substance-restricted — review §3.1). |
| IV   | Distinct things differ by attributes or by affections.          | ✅ (with qualifier) | Two theorems: `prop_4_partition` and `prop_4_distinguishedByAttributesOrCategory`. The latter is **information-asymmetric**: the both-substances case carries no-shared-attribute (A12 contrapositive), but the both-modes case is *structurally captured* (`Mode x ∧ Mode y`) without internal mode-individuation content — Spinoza's "ex diversitate earundem affectionum" awaits Pars II. The two mixed-category cases (`Substance ∧ Mode`, `Mode ∧ Substance`) **exceed Spinoza's textual scope** but are required by Lean's exhaustiveness; this is a cost of mechanisation, not a textual divergence. |
| V    | No two substances of same nature/attribute.                     | ✅     | `prop_5_uniqueSubstancePerAttribute` — direct application of A12 (substantive metaphysical commitment, auxiliary_axioms.md §III). |
| VI   | One substance cannot be produced by another.                    | ✅     | `prop_6_substanceNotProducedByAnother` (in `Causation.lean`-section of `Propositions.lean`) via Prop. III contrapositive + A12. |
| VII  | Existence belongs to the nature of substance.                   | ✅     | `prop_7_existenceBelongsToSubstance` — direct application of A13. Corollaries: `prop_7_natureRequiresExistence` (via A11, **first load-bearing use of A11**), `prop_7_substanceIsCausaSui`. |
| VIII | Every substance is necessarily infinite.                        | 🟡     | `prop_8_substanceIsNotFinite` — proves the contrapositive content (no substance is finite-after-its-kind) via A12 + Def. II. The "absolutely infinite" reading (Def. VI) requires GAP-8a (cardinality). |
| IX   | More reality ⇒ more attributes.                                 | ✅ (with qualifier) | `prop_9_moreRealityMoreAttributes` (`Realitas.lean`) — genuine derivation, **no new axiom**: reality-dominance (`hasMoreRealityThan`, the Della Rocca *constitutive* reading — reality *is* attribute-dominance, not a further measured quantity) transfers any attribute count via `hasAtLeastNAttributes`. Corollary `prop_9_cor_godMaximalReality` (direct A15): God has more reality than any substance. **Qualifier**: the quantitative "measure of reality" reading is not introduced — only the qualitative dominance relation Spinoza's one-line *demonstratio* ("*patet ex definitione 4*") actually needs. **Resolved**: the old blocker ("needs reality-measure/counting framework") is dissolved by `hasAtLeastNAttributes`/`HasInfiniteAttributes`, GAP-8a's counting apparatus. |
| X    | Each attribute of a substance is per se conceived.              | ✅     | `prop_10_attributePerSe`. |
| XI   | God necessarily exists.                                         | 📜     | `prop_11_godNecessarilyExists` + corollary `prop_11_godIsCausaSui` (`Theologia.lean`) — direct invocation of A27 (`ax_god_exists`, Section III: "Deus datur"), converted to `involvesExistence`/`natureRequiresExistence` via A13 + A11. **Resolved**: supersedes the earlier "critical path is longer than initially estimated" note — Bennett 1984 §18's four reading paths each needed a commitment beyond A12+A13+GAP-8a; A27 is the minimal direct form of that commitment, adopted visibly rather than derived. **Kernel-level irreducibility**: `Models/NoGod.lean` witnesses A27 (hence Prop. XI) is **not derivable even from the full `Pars1Axioms` register** (A1–A15, all Section III commitments included) — a strictly stronger baseline than the A12/A15 counter-models in `Counterexamples.lean`, which run against `StatedAxioms` only. Extends the project's irreducibility methodology beyond the stated-axioms baseline. |
| XII  | No attribute can be conceived such that substance is divisible. | ✅ (with qualifier) | `prop_12_substanceIndivisible` (`Mereology.lean`) mechanises Props. XII/XIII's shared **ontological core**: no substance has a proper part. Chain: A32 (`ax_substancePart_sameNatureSubstance`, Section III, horn (i) of Spinoza's dilemma) gives a proper part that is itself a substance of the same nature and distinct from the whole; A12 collapses the shared attribute to identity, contradicting distinctness. **Qualifier**: the statement's own epistemic wrapper ("*vere concipi*" — no attribute can be *truly conceived* from which divisibility follows) is not mechanised — no "truly conceiving" operator exists at this layer (GAP-16, Pars II). Horn (ii) of the dilemma is also not formalised — needs destruction/persistence machinery (GAP-20); A32 commits to load-bearing horn (i) only. |
| XIII | Absolutely infinite substance is indivisible.                   | ✅ (with qualifier) | `prop_13_absolutelyInfiniteSubstanceIndivisible` + corollary `prop_13_cor_noSubstanceDivisible` (`Mereology.lean`) — direct specialisation of Prop. XII's ontological core to `IsGod g` (via `hgod.1 : Substance g`). Same qualifier as Prop. XII: epistemic wrapper and horn (ii) not mechanised (GAP-16, GAP-20). |
| XIV  | Besides God, no substance can be given or conceived.            | 📜     | `prop_14_onlyGodIsSubstance` mechanised in short form via A12 + A14 + A15 (Section III commitments) — **closing GAP-8b + GAP-13** in the process. 3-line proof, `sorry`-free. The 📜 marker is retained because the proof rests on three Section III axioms (V, VI, X are still the only theorems mechanised in the substantive sense). `Models/TwoSubstance.lean` **falsifies A15** and is therefore a Bennett-line non-Spinoza bench — it cannot carry a `Pars1Axioms` instance, which is the correct migration outcome. |
| XV   | Whatever is, is in God; nothing without God can be conceived.   | ✅ (with qualifier) | `prop_15_allInGod` (`Inherence.lean`) mechanises the **ontological clause**: every thing is either God or in God. Chain: `prop_4_partition` splits substance/mode; substance case via `prop_14_onlyGodIsSubstance`; mode case via A33 (`ax_mode_inheres_in_substance`, Section II, Def. V promotion) giving a substance `s` with `inheresIn x s`, then `prop_14_onlyGodIsSubstance` forces `s = g`. **Qualifier**: the statement's second, epistemic clause ("*nec concipi potest sine Deo*") is not mechanised — awaits Pars II conception machinery (GAP-17). |
| XVI  | From divine nature, infinite things in infinite ways follow.    | 🟡     | `prop_16_modesFollowFromGod` (`Consecutio.lean`) mechanises the **qualitative clause**: every mode follows from the necessity of the divine nature, via `prop_15_allInGod` + A37 (`ax_inherence_consecution`, Section II, the Della Rocca unified-dependence reading). Corollary I `prop_16_cor1_godEfficientCause` derives God's efficient causation of every mode via A38. **Not mechanised**: the "*infinita infinitis modis*" **cardinality** clause — same counting-framework prerequisite as GAP-8a (cross-referenced there, not duplicated). |
| XVII | God acts from the laws of his own nature alone.                 | 🟡     | `prop_17_godIsFree` (`Theologia.lean`) mechanises Corollary II's **existence-clause** reading only: God is *causa sui* (Prop. VII via `hgod.1`) and unconstrained (A31, `ax_substance_not_constrained`, Section II); A30 (`ax_causaSui_unconstrained_free`, Section I, Def. VII bridge) composes these into `freelyExistent g` (i.e. `Free g`). **Not mechanised**: the action-clause ("*ad agendum a se solo determinatur*") and Prop. XVII's own main clause (acting solely by the laws of its own nature) — same GAP-9 family as `Free`/`Constrained`'s definition (see GAP-18). |
| XVIII| God is the immanent, not transitive, cause of all things.       | ✅ (with qualifier) | `prop_18_godImmanentCause` (`Inherence.lean`): for every mode `x`, `Cause g x ∧ inheresIn x g` — "immanent" captured as the conjunction (a transitive cause's effects would lie outside it). Chain: `prop_15_allInGod` plus `prop_1_substanceDisjointFromModes` rule out `x = g`; the remaining `inheresIn x g` converts via A34 (`ax_inherence_causation`, Section II, the Curley 1969 "in = caused-by" reading) to `Cause g x`. Depends on Prop. XV's mechanised ontological clause, **not** the Prop. XVI consecution relation (now mechanised in `Consecutio.lean` — GAP-19 closed; `prop_16_cor1_godEfficientCause` gives an alternative consecution-routed derivation of the causal conjunct). |
| XIX  | God / all attributes of God are eternal.                        | ✅     | `prop_19_godIsEternal` (God's case) + `prop_19_attributesAreEternal` (attributes' case), `Theologia.lean`. God's case: A13 gives `involvesExistence g`, A11 converts to `natureRequiresExistence g`, A28 (`ax_natureRequiresExistence_eternal`, Section I, Def. VIII bridge) converts to `Eternal g`. Attributes' case: A29 (`ax_attribute_involvesExistence`, Section II) gives `involvesExistence a` from `Attribute a g`, then the same A11 + A28 chain delivers `Eternal a`. |
| XX   | God's existence and essence are one and the same.               | 🟡     | `prop_20_partial_attributesExpressBoth` (`Consecutio.lean`) mechanises the **conjunctive content** the *demonstratio* actually assembles: every attribute of God expresses both His essence (`Attribute`, Def. IV) and His necessary existence (A29). **Not mechanised**: the full "*unum et idem sunt*" **identity claim** — needs essence-as-object machinery (GAP-24). |
| XXI  | All that follows from absolute nature of any attribute is infinite & eternal. | 📜 | `prop_21_absoluteFollowersEternalInfinite` (`Consecutio.lean`) — direct invocation of A40 (📜-pattern, same as A13/A27/A35: Prop. XXI's content adopted directly, since the *demonstratio*'s durational reductio needs machinery this base layer lacks). **Honest caveat**: A40 conflates essence-grounded eternity (Def. VIII) with infinite modes' cause-derived sempiternity — GAP-21. |
| XXII | What follows from a modified attribute is also infinite & eternal. | 📜 | `prop_22_infiniteModeTransfer` (`Consecutio.lean`) — direct invocation of A41 (📜-pattern). Spinoza's statement is genuinely **ternary** ("*ex aliquo Dei attributo quatenus modificatum*"); A41 flattens it to a binary `followsFrom` transfer — GAP-22. |
| XXIII| Every necessarily-existing infinite mode follows from God's attribute. | 📜-partial | `prop_23_partial_classification` (`Classificatio.lean`) — direct invocation of **A44** (`ax_consecution_trichotomy`, Section III): every mode follows absolutely from an attribute of God, from an eternal-infinite mode, or from another finite mode. **Closes the premise half of GAP-23** — the exhaustiveness Prop. XXVIII's *demonstratio* consumed silently (and A42's docstring flagged) is now a visible commitment. **Honest gap**: Spinoza's own conclusion additionally EXCLUDES the finite branch for necessarily-infinite modes (a disjunction of exactly two horns, not the full trichotomy); that exclusion needs a **finite-source transfer principle** ("what follows from a finite mode is itself finite") not committed anywhere in this formalisation. Residual half tracked in GAP-23 (cross-ref GAP-22's ternary-relation prerequisite). |
| XXIV | Essence of things produced by God does not involve existence.   | 📜     | `prop_24_producedEssenceNotInvolveExistence` + corollary fragment `prop_24_cor_modeNotCausaSui` (`Inherence.lean`) — direct invocation of A35 (`ax_mode_not_involvesExistence`, Section III). Honest record: A35 *is* Prop. XXIV's content adopted as an axiom directly, the same 📜-pattern as A13/Prop. VII — Spinoza's one-line *demonstratio* ("*Patet ex definitione 1*") needs a converse link ("produced by another ⇒ not *causa sui*") no prior axiom delivers. The corollary's further claim (God as cause of *perseverance* in existence) needs temporal/durational machinery, not mechanised. |
| XXV  | God is the efficient cause not only of existence but of essence of things. | 🟡 | **Corollary mechanised** as `prop_25_cor_everythingGodOrMode` (`Consecutio.lean`): every particular thing is either God or a mode, via `prop_4_partition` + `prop_14_onlyGodIsSubstance` — Spinoza himself proves the corollary from Prop. XV + Def. V directly, independently of the proposition's harder claim. **Not mechanised**: Prop. XXV proper — God as cause of the **essence** of things — needs essence-as-object machinery (GAP-24, shared with Prop. XX's identity claim). |
| XXVI | Things determined to act are determined by God.                 | 🟡     | `prop_26_modesDeterminedByGod` (`Inherence.lean`, thin/partial form): every mode is `Constrained` (A36, `ax_mode_constrained`, Section II, Def. VII's second-clause existence-side reading) **and** caused by God (via `prop_18_godImmanentCause`'s causal clause). **Not mechanised**: the "*ad aliquid operandum*" self-determination clause (the statement's second half, and the whole of Prop. XXVII) — Pars II action machinery, same GAP-9 family as Prop. XVII (see GAP-18). |
| XXVII| Things determined by God cannot render themselves undetermined. | ⏳     | Depends on Prop. XXVI (now partial, see above); full closure needs Pars II's action machinery. |
| XXVIII| Every singular thing's existence and action is determined by another finite cause, ad infinitum. | 📜 | `prop_28_finiteModeCausedByFiniteMode` (`Consecutio.lean`) — direct invocation of A42 (📜-pattern, single-step form); the "*et sic in infinitum*" iteration is the **derived** corollary `prop_28_cor_noFirstFiniteCause` (no first finite mode — a genuine small proof from A42). **This is the finite-mode-causation backbone Pars II–V consume** — what review §3.1's A5ₛ substance-restriction protected now has its positive counterpart committed. Spinoza's own *demonstratio* routes through Prop. XXIII's trichotomy; that trichotomy is now mechanised as A44 (`Classificatio.lean`), and A42 commits the conclusion directly rather than deriving through it. **Demote update**: `Classificatio.lean`'s `A42_demote_via_trichotomy` shows A42 is in fact an **equal-strength decomposition** over Σ = {A38, A40, A41, A44} — once A44 is granted, A42 is redundant with the rest of `ConsecutioAxioms`. See `auxiliary_axioms.md` A42/A44 entries and README's demote table. |
| XXIX | Nothing in nature is contingent; all is determined by divine necessity. | ✅ (with qualifier) | `prop_29_nothingContingent` (`Inherence.lean`): `causaSui x ∨ Constrained x` for every `x`, via `prop_4_partition` (substance case: A13 directly; mode case: A36). The disjunctive, non-modal reading of "nothing is contingent" that exhausts the alternatives Spinoza's proof trades on. **Qualifier**: the "*ex necessitate divinae naturae*" strengthening (determination specifically *by God*) is available by conjoining `prop_26_modesDeterminedByGod` given an `IsGod` witness, but not folded into the statement so it holds for any `Thing`. |
| XXX  | An actually existing intellect comprehends God's attributes and his affections. | ⏳ | Depends on A6 + Pars II prerequisites. |
| XXXI | The actually existing intellect is a mode of thinking.          | ⏳     | Pars II territory. |
| XXXII| Will is not a free cause but a necessary one.                   | ⏳     | Pars II territory. |
| XXXIII| Things could not have been produced in any other way or order. | ⏳     | Depends on Prop. XVI + XXVI–XXIX; also needs the modal layer's necessity machinery (`ModalForm.lean`). |
| XXXIV | God's power = God's essence.                                   | ⏳     | Depends on Prop. XI (now mechanised) + XX; needs power machinery not yet formalised. |
| XXXV | What we conceive to be in God's power necessarily exists.       | ⏳     | Depends on Prop. XXXIV; needs power machinery not yet formalised. |
| XXXVI| Nothing exists from whose nature an effect does not follow.     | ✅ (with qualifier) | `prop_36_nothingWithoutEffect` (`Consecutio.lean`) — a **genuine (small) derivation**: A43 (`ax_omnia_effectum`, the consecution content) supplies `∃ e, followsFrom e x`, and A38 *derives* the causal form `∃ e, Cause x e` from it. The earlier "candidate for a direct Section III commitment" note is resolved exactly as predicted — but the causal conclusion is derived, not separately committed. **Qualifier**: Spinoza's own route through Prop. XXV cor. + Prop. XXXIV's *potentia* machinery is not mechanised (Props. XXXIV/XXXV deferred); A43 commits the consecution conclusion directly. |

**Tally** (the "fully mechanised" count excludes theorems that are
direct invocations of a Section III commitment axiom; it reflects
the post-GAP-10 closure, the Prop. IV expansion, the
Theologia/Mereology/Inherence extension session — A27–A36 — the
Consecutio extension — A37–A43 — and the Realitas/Classificatio
extension — the counting framework, the attribute-collapse
theorem, and A44):

- ✅ **6 mechanised in the substantive sense, full statement** (with
  one qualifier on Prop. IV — see row note: both-modes case is
  structurally captured but information-free internally;
  mixed-category cases exceed Spinoza's textual scope — and one on
  Prop. XXXVI, whose consecution premise is itself a Section III
  commitment) —
  - **II** (`prop_2_distinctSubstancesShareNothing` Della-Rocca
    form + `prop_2_via_def3` Spinoza-textual form, both 1–3 lines);
  - **IV** (`prop_4_partition` + `prop_4_distinguishedByAttributesOrCategory`,
    proves both the substance/mode partition and the four-case
    distinguishability dichotomy — qualifier above);
  - **VI** (`prop_6_substanceNotProducedByAnother`, 5-line proof
    chaining Prop. III contrapositive + sameNature unfolding +
    A12);
  - **X** (`prop_10_attributePerSe`, one-line invocation of A10, a
    Section I *definitional bridge*);
  - **XIX** (`prop_19_godIsEternal` + `prop_19_attributesAreEternal`,
    both clauses of the statement — God and all his attributes —
    covered via A13/A29 + A11 + A28 chains); and
  - **XXXVI** (`prop_36_nothingWithoutEffect`, a genuine small
    derivation: the causal form is *derived* via A38 from A43's
    consecution content rather than separately committed —
    qualifier above: A43 itself is a 📜-pattern commitment).
- ✅ **6 mechanised with a qualifier, via a real derivation chaining
  multiple items** (statement's full textual scope not entirely
  captured — see each row note for the specific fragment left
  open) —
  - **IX** (`prop_9_moreRealityMoreAttributes` + corollary
    `prop_9_cor_godMaximalReality`, `Realitas.lean`, **no new
    axiom**; qualifier: constitutive/qualitative reading of
    "reality", not a quantitative measure);
  - **XII/XIII** (`prop_12_substanceIndivisible` +
    `prop_13_absolutelyInfiniteSubstanceIndivisible`, via A32 + A12;
    epistemic wrapper and horn (ii) not mechanised);
  - **XV** (`prop_15_allInGod`, via A33 + `prop_14_onlyGodIsSubstance`
    + `prop_4_partition`; epistemic second clause not mechanised);
  - **XVIII** (`prop_18_godImmanentCause`, via `prop_15_allInGod` +
    A34); and
  - **XXIX** (`prop_29_nothingContingent`, via `prop_4_partition` +
    A13 + A36; the "*by God specifically*" strengthening left
    unfolded).
- 📜 **8 mechanised by direct invocation of a single Section III
  commitment axiom** (one — XXIII — only partially, see its own
  entry) —
  - **V** (`prop_5_uniqueSubstancePerAttribute` = direct A12);
  - **VII** (`prop_7_existenceBelongsToSubstance` = direct A13);
  - **XI** (`prop_11_godNecessarilyExists` = direct A27, "Deus
    datur");
  - **XXIV** (`prop_24_producedEssenceNotInvolveExistence` = direct
    A35);
  - **XXI** (`prop_21_absoluteFollowersEternalInfinite` = direct
    A40);
  - **XXII** (`prop_22_infiniteModeTransfer` = direct A41);
  - **XXIII** (`prop_23_partial_classification` = direct A44 —
    📜-**partial**: the trichotomy clause only, not the
    necessarily-infinite exclusion; see row note); and
  - **XXVIII** (`prop_28_finiteModeCausedByFiniteMode` = direct
    A42, plus the *derived* corollary
    `prop_28_cor_noFirstFiniteCause`; A42 itself is now an
    equal-strength decomposition over Σ = {A38, A40, A41, A44} —
    see `Classificatio.lean`'s `A42_demote_via_trichotomy`).
  Honest record: each of A12, A13, A27, A35, A40, A41, A42, A44 *is*
  essentially the corresponding proposition's content adopted as
  an axiom (see `auxiliary_axioms.md` §III). The "proofs" are
  one-liners by design.
- 📜 **+ 1 mechanised by chaining three Section III commitment
  axioms** — **XIV** (`prop_14_onlyGodIsSubstance` consumes
  A12 + A14 + A15; structurally the most Section-III-heavy theorem
  in Pars I, with three commitments threaded through a single
  proof body). Sorry-free; A14 / A15 are now `Pars1Axioms` fields
  (post-§F.α promotion) but remain Section III metaphysical
  commitments per `auxiliary_axioms.md`.
- 🟡 **8 partial** — I (disjointness only — GAP-6 / Prop. I
  priority requires `conceptualDep` at modal layer), III
  (substance-restricted — general form awaits modal layer's
  `hasAttribute`), VIII (not-finite form only; absolutely-infinite
  reading awaits GAP-8a / cardinality), XVII (existence-clause
  reading of Cor. II only; action-clause awaits Pars II — GAP-18),
  XXVI (thin form — determination + causation by God only;
  self-determination clause awaits Pars II — GAP-18), XVI
  (qualitative clause only via A37; "*infinita infinitis modis*"
  cardinality awaits GAP-8a's counting framework), XX (conjunctive
  content only; "*unum et idem*" identity awaits GAP-24), XXV
  (corollary only; essence-causation claim awaits GAP-24).
- ⏳ **7 deferred** — XXVII, XXX–XXXII (Pars II
  territory), XXXIII (modal layer), XXXIV–XXXV (*potentia*
  machinery). (Neither IX nor XXIII remains in this bucket — see
  "Resolved" below.)

**Resolved**: Prop. XI no longer needs GAP-8a closure — see the
row note above. A27 supplies the missing commitment directly,
independent of Def. VI's cardinality clause.

**Resolved**: Prop. IX (🚫 → ✅-with-qualifier) — the "needs
reality-measure/counting framework" blocker is dissolved by
`Realitas.lean`'s `hasAtLeastNAttributes`/`HasInfiniteAttributes`,
which finally give GAP-8a's counting apparatus (the qualitative,
constitutive-reading half; see the Prop. IX row and the
"Attribute-collapse result" subsection below).

**Resolved (partial)**: Prop. XXIII (⏳ → 📜-partial) — the
exhaustiveness/classification premise A42's docstring flagged is
now committed visibly as A44 (`Classificatio.lean`), closing
GAP-23's premise half. The necessarily-infinite exclusion residue
remains open (cross-ref GAP-22).

### Section III axiom utilization

How load-bearing is each Section III commitment across the project?

| Axiom | Used in (theorems / corollaries)                              | Cost-per-axiom note |
|-------|---------------------------------------------------------------|---------------------|
| A12   | `prop_4_distinguishedByAttributesOrCategory` (direct), `prop_5` (direct), `prop_6` (direct, combined with Prop. III contrapositive `cause_implies_sameNature`), `prop_8` (direct), `prop_12`/`prop_13` (direct, combined with A32 — `Mereology.lean`), `prop_14` (direct, combined with A14 + A15) | **Most load-bearing** — used directly in 7 propositions. |
| A13   | `prop_7` + corollaries `prop_7_natureRequiresExistence`, `prop_7_substanceIsCausaSui`; also `prop_11` (direct, `Theologia.lean`), `prop_19_godIsEternal` (God's case, `Theologia.lean`), `prop_29_nothingContingent` (substance case, `Inherence.lean`) | Grew from single-proposition to a cross-cutting existence commitment: 1 proposition + 2 corollaries, plus 3 further propositions in this session's extension classes. |
| A14   | `prop_14` only                                                | **Point-purpose** — committed for one theorem. |
| A15   | `prop_14` only                                                | **Point-purpose** — committed for one theorem. |
| A27   | `prop_11_godNecessarilyExists` (direct, `Theologia.lean`)     | **Point-purpose, but foundational** — single-proposition commitment carrying the entire "Deus datur" instantiation step. **Irreducibility witness**: `Models/NoGod.lean` — falsified while the full `Pars1Axioms` register (A1–A15) holds. |
| A32   | `prop_12_substanceIndivisible`, `prop_13_absolutelyInfiniteSubstanceIndivisible` (direct, combined with A12, `Mereology.lean`) | Single axiom carries two propositions (plus the Prop. XIII corollary) via horn (i) of Prop. XII's dilemma. **Irreducibility witness**: `ModeParts` in `Models/CounterexamplesII.lean` — falsified while `Pars1Axioms` + `CausalAxioms` + `TheologiaAxioms` + `InherenceAxioms` all hold (the parts-as-modes reading, Letter 12 / Curley). |
| A35   | `prop_24_producedEssenceNotInvolveExistence` (direct, `Inherence.lean`) | **Point-purpose** — same 📜-pattern as A13: Prop. XXIV's content adopted directly. **Irreducibility witness**: `NecessaryMode` in `Models/CounterexamplesII.lean` — falsified while `Pars1Axioms` + `CausalAxioms` + `TheologiaAxioms` + the other three `InherenceAxioms` fields (A33/A34/A36, standalone theorems) all hold; the necessarily-existing-mode profile only A35 rules out. |
| A40   | `prop_21_absoluteFollowersEternalInfinite` (direct, `Consecutio.lean`) | **Point-purpose** — 📜-pattern: Prop. XXI's content adopted directly (durational-reductio machinery unavailable at this layer). Eternity/sempiternity conflation tracked as GAP-21. |
| A41   | `prop_22_infiniteModeTransfer` (direct, `Consecutio.lean`)    | **Point-purpose** — 📜-pattern: Prop. XXII's content, ternary statement flattened to binary `followsFrom` (GAP-22). |
| A42   | `prop_28_finiteModeCausedByFiniteMode` (direct) + derived corollary `prop_28_cor_noFirstFiniteCause` (`Consecutio.lean`) | 📜-pattern, but **backbone-grade**: the finite-mode-causation commitment Pars II–V consume throughout; also yields the "*et sic in infinitum*" corollary as a genuine derivation. Bypasses Prop. XXIII's trichotomy (GAP-23). |
| A43   | `prop_36_nothingWithoutEffect` (via A38, `Consecutio.lean`)   | **Point-purpose, with derivational payoff** — commits only the consecution content; the causal form of Prop. XXXVI is *derived* through A38 rather than separately committed. |
| A44   | `prop_23_partial_classification` (direct, `Classificatio.lean`); also consumed by the A42 demote (`A42_demote_via_trichotomy`) | **Dual-purpose** — closes Prop. XXIII's premise half directly, and separately powers A42's equal-strength decomposition (Σ = {A38, A40, A41, A44}). |

Bennett-line reading note: A12 earns its keep across the project
(now 7 propositions, up from 5 after the Mereology extension), but
A14, A15, A27, A35, A40, A41, and A43 are each committed for
essentially one proposition (A27, A35, A40, A41, A43 by design —
see their 📜-pattern above); A42 is nominally single-proposition
but is the backbone Pars II–V will consume, and is now itself
demotable to A44 + already-committed axioms (see A44's row).
Bennett-leaning readers can drop A14 + A15 to recover the partial
state at the cost of losing Prop. XIV; A12 cannot be dropped without
losing Prop. V's mechanisation and everything built on it (VI, VIII,
XII, XIII, XIV). **Irreducibility parity note**: all three Section
III axioms of the Theologia/Mereology/Inherence extension (A27, A32,
A35) now have kernel-level irreducibility witnesses (`NoGod`,
`ModeParts`, `NecessaryMode`), each against a baseline register
**stronger** than the paper's `StatedAxioms` — the previously
flagged parity gap (A32/A35 lacking dedicated counter-models) is
closed. A44 has no dedicated counter-model (its Section III status
rests on demonstratio-gap grounds — Bennett 1984 §25); A12, A14, and
A15 additionally interact with A8 and A10 to produce the
attribute-collapse theorem — see the subsection immediately below.

### Attribute-collapse result

`Ethica/Pars1/Realitas.lean` proves that in any `Pars1Axioms` world
containing a God, **every attribute of every substance equals that
God** (`attribute_collapse`, derived from A8 + A10 + A12 + A14 + A15
jointly — no new axiom). Specialised to God's own attributes
(`god_is_own_only_attribute`), this rules out God having even two
distinct attributes (`god_no_two_attributes`), which in turn makes
Def. VI's *infinitis attributis* clause **unsatisfiable** for any
God in the register (`def6_infinitis_attributis_unsatisfiable`) —
not merely unformalised (the old GAP-8a framing) but actively
inconsistent with the rest of Section III once cardinality is
finally expressible.

`Ethica/Pars1/Models/MultiAttribute.lean` shows the incompatibility
is *sharp*, not an artifact of a weak counting framework: the
**full** `Pars1Axioms` register tolerates a substance with
infinitely many attributes (carrier `Nat`, `multiAttribute_infinitude`)
precisely as long as the model is godless (`multiAttribute_hasNoGod`).
Godless plurality is consistent; godful plurality is impossible.
Escape routes are catalogued in `Realitas.lean`'s header and tracked
as **GAP-25**.

### Resolution: the Attributum layer

**GAP-25 is closed** (Attributum session) by adopting escape route
(iii) — type attributes off the `Thing` universe — as a **parallel
branch**, `Ethica/Attributum/`. Nothing under `Ethica/Pars1/` is
modified, so everything above remains exactly true of the Pars I
register and the published results are untouched.

`AttrWorld Thing Attr` (`Attributum/Core.lean`) extends
`EthicaWorld Thing` — every Pars I primitive is reused verbatim —
and routes attribution through `perceivedAsEssence : Thing → Attr →
Prop`. Since `Attributum a s` has `a : Attr`, `Substance a` does not
typecheck: **step 3 of the collapse chain is inexpressible, not
merely false**. Prop. X survives via the attribute-side predicate
`perSeConceivedAttr` (a field of `AttrStructure Attr`, a class that
does not mention `Thing`); what is withdrawn is only A8's *bite on
attributes*, which is exactly Bennett 1984 §16's position, enforced
by typing rather than by an axiom restriction.

The four attribute axioms are re-typed verbatim as A10′/A12′/A14′/
A15′ (`Attributum/Axioms.lean`), keeping their Section
classifications. Props. V, IX and X are re-derived in the new
vocabulary.

Results, all `sorry`-free and (for the two headline theorems)
dependent on **no axioms whatever**:

| Theorem | File | Content |
|---|---|---|
| `dual_god_with_two_attributes` | `Attributum/Models/DualAttribute.lean` | A God with two distinct attributes (`cogitatio`, `extensio`), in a world carrying `AttrAxioms` **and** `StatedAxioms` |
| `inf_def6_recovered` | `Attributum/Models/InfiniteAttribute.lean` | A God with infinitely many attributes — Def. VI satisfied outright |
| `legacy_god_no_two_attributes` | `Attributum/Bridge.lean` | The same sentence, refuted, once `Attr := Thing` |
| `legacy_collapse` | `Attributum/Bridge.lean` | `attribute_collapse` transported along the legacy embedding |

The last two are the diagnosis. `Bridge.lean`'s `legacyAttrWorld`
instantiates `Attr := Thing`, and under it `Attributum`, `IsGodAttr`,
`hasAtLeastNAttrs` and `HasInfiniteAttrs` are *definitionally* their
Pars I counterparts (four `Iff.rfl` lemmas). So the *same* sentence,
under the *same* axioms, is satisfiable when `Attr` is separate and
refutable when `Attr := Thing`. **The collapse is an artefact of the
Prop. X scholium's identification of attributes with things, not a
consequence of Spinoza's substantive commitments.**

This is also what unblocks Pars II, whose Props. I–II assert that
Thought and Extension are two distinct attributes of God.

---

## Models

| Model | Role | Layer | Status |
|-------|------|-------|--------|
| Single-substance (`Unit`) | Consistency witness; S5 modal collapse | Base + modal | ✅ `Models/SingleSubstance.lean` — full `Pars1Axioms` + `CausalAxioms` + all six modal-layer instances on `Unit` × `Unit`. Bridges A18/A19/A20/A21 discharge trivially; A16/A17 hold vacuously. Prop. XIV applies. |
| Two-substance Bennett-line bench | A15 falsifier (post-promotion) | Base | ✅ `Models/TwoSubstance.lean` — `EthicaWorld` only; **falsifies A15** via `twosubst_falsifies_A15`. |
| Multi-world A18 bridge-bite | A18 non-trivial bite witness | Modal | ✅ `Models/MultiWorld.lean` — `Thing := necessary \| contingent`, `World := w0 \| w1`. A18 fires non-vacuously on the `False ↔ False` branch. Does **not** exercise A19/A20/A21. |
| A12 counter-model | Irreducibility witness (Bennett #1) | StatedAxioms + PSR | ✅ `Models/Counterexamples.lean` `A12CounterModel` — 4-element all-substance world; `StatedAxioms` + `PSRSubstance` satisfied, A12 falsified. Kernel-level hard fact. |
| A15 counter-model | Irreducibility witness (Bennett #2) | StatedAxioms + plenitude | ✅ `Models/Counterexamples.lean` `A15CounterModel` — 3-element all-substance world; `StatedAxioms` + plenitude satisfied, A15 falsified. Kernel-level hard fact. |
| Multi-attribute substance | Delivered — godless plurality/infinitude witness, twinned with the attribute-collapse theorem | Base | ✅ `Models/MultiAttribute.lean` — carrier `Nat`; full `Pars1Axioms` instance. `multiAttribute_hasNoGod`: `absolutelyInfinite` uniformly `False`, so `IsGod` is unsatisfiable — this is load-bearing, not incidental. `multiAttribute_plurality` (≥2 attributes of `0`) and `multiAttribute_infinitude` (`HasInfiniteAttributes 0`) satisfy GAP-8a's cardinality desideratum on the **full** register, but only because no God exists in the model — `Realitas.lean`'s `attribute_collapse` forces exactly one attribute per substance whenever a God is present. Delivered with a twist relative to the v1.0.0 "planned future bench" listing: godless by necessity, not by oversight. |
| Prop. III bite-test | Non-identity `Cause` exercising A4ₛ + A5ₛ contrapositively | Causal | ⏳ Not started; current TwoSubstance uses identity-restricted `Cause` so doesn't exercise A4ₛ+A5ₛ. |
| NoGod (A27 irreducibility witness) | Kernel-level irreducibility witness (Bennett #3) | Full `Pars1Axioms` (A1–A15) | ✅ `Models/NoGod.lean` — one-element `NoGodThing` world satisfying the **full** `Pars1Axioms` register (A1–A15, including all four Section III commitments A12–A15) with `absolutelyInfinite _ := False`, so `IsGod` is unsatisfiable; `noGodWorld_hasNoGod` + `A27_falsified` + `A27_irreducibility_witness`. Strictly stronger baseline than `Counterexamples.lean`'s A12/A15 counter-models, which run against `StatedAxioms` only — the first irreducibility result witnessed against the complete committed register. |
| GodWorld (`TheologiaAxioms` consistency) | Consistency witness for A27–A31 | Base (Theologia) | ✅ `Models/GodWorld.lean` — `TheologiaAxioms Unit` instance layered on `SingleSubstance`'s existing `Pars1Axioms Unit`; `godWorld_god_exists` plus sanity checks that Props. XI, XVII, XIX hold on `Unit`. |
| MereologyWitness (`MereologyAxioms` consistency) | Consistency witness for A32 | Base (Mereology) | ✅ `Models/MereologyWitness.lean` — `Unit` with `properPart _ _ := False`; A32 discharges vacuously (no proper parts to falsify it against); sanity checks that Props. XII/XIII hold on `Unit`. |
| InherenceWitness (`InherenceAxioms` consistency) | Consistency witness for A33–A36 | Base (Inherence) | ✅ `Models/InherenceWitness.lean` — `Unit` with `inheresIn _ _ := False`; A33/A35/A36 discharge vacuously since `Mode ()` is `False` on `Unit` (inherited from `SingleSubstance`'s `inAnother _ := False`), A34 discharges vacuously since `inheresIn` is uniformly `False`; sanity checks that Props. XV/XXIX hold on `Unit`. |
| ModeParts (A32 irreducibility witness) | Kernel-level irreducibility witness (Bennett #4) | Full register minus Mereology | ✅ `Models/CounterexamplesII.lean` — two-element world (`whole`/`part`) embodying the **parts-as-modes** reading (Letter 12 to Meyer; Curley): a substance whose sole proper part is a mode. Satisfies `Pars1Axioms` + `CausalAxioms` + `TheologiaAxioms` + `InherenceAxioms` in full (four instances) while falsifying A32 (`A32_falsified`) — Prop. XII's horn (i) is a genuine interpretive choice, not forced by any other commitment, including causal/inherence machinery A32 was never tested against. |
| NecessaryMode (A35 irreducibility witness) | Kernel-level irreducibility witness (Bennett #5) | Full register minus A35 | ✅ `Models/CounterexamplesII.lean` — two-element world (`g`/`m`) with a **necessarily-existing mode** (the infinite-mode profile with necessity lodged in the mode's own essence). Satisfies `Pars1Axioms` + `CausalAxioms` + `TheologiaAxioms` plus A33/A34/A36 as standalone theorems (`necessaryMode_satisfies_A33/34/36`) while falsifying A35 (`A35_falsified`) — only A35 (= Prop. XXIV) enforces the through-cause vs through-essence necessity distinction. |
| ConsecutioWitness (`ConsecutioAxioms` + full-register consistency) | Joint-consistency witness for A1–A15 + A27–A43 | Base (all non-modal layers) | ✅ `Models/ConsecutioWitness.lean` — fresh one-element carrier `ConsecutioW` with a uniformly *positive* profile (`Cause`, `inheresIn`, `followsFrom`, `followsAbsolutely` all `True`), so A43 and the other consecution fields discharge **non-vacuously** (unlike the `Unit` witnesses' all-`False` relations). Carries instances for `Pars1Axioms` + `CausalAxioms` + `TheologiaAxioms` + `MereologyAxioms` + `InherenceAxioms` + `ConsecutioAxioms` — joint consistency of the entire extended register A1–A15 + A27–A43 on one carrier (modal A16–A26 excluded; separate `World`-indexed layer). **Largest single-model consistency proof in the project.** |
| ClassificatioWitness (`ClassificatioAxioms` consistency) | Consistency witness for A44 (+ the `TrichotomySigma` demote register) | Base (Classificatio) | ✅ `Models/ClassificatioWitness.lean` — extends `ConsecutioWitness`'s carrier `ConsecutioW` with A44, discharging **vacuously** (`Mode x` is `False` on `ConsecutioW`, exactly as A42's own discharge there). Also witnesses `TrichotomySigma ConsecutioW` (via `trichotomySigma_of_classificatio`), i.e. consistency of the A42-demote register Σ = {A38, A40, A41, A44}. |
| DualAttribute (two-attribute God) | **The decisive witness of the Attributum layer** | Attributum (re-typed) | ✅ `Ethica/Attributum/Models/DualAttribute.lean` — fresh carrier `DualThing` (one substance) with `Attr := DualAttr` (`cogitatio`/`extensio`). Carries `AttrAxioms` (A10′/A12′/A14′/A15′) **and** `StatedAxioms` (Spinoza's own A1–A11, the register the published results run against). `dual_god_two_attributes` exhibits exactly what `god_no_two_attributes` forbids in Pars I; `dual_god_with_two_attributes` packages it with `IsGodAttr`. Depends on **no axioms** (`#print axioms`). The legacy `Thing`-typed channel is switched off and *proved* empty (`dual_A14_thingTyped_falsified`), which is why no `Pars1Axioms` instance exists here and the collapse theorem has nothing to apply to. |
| InfiniteAttribute (Def. VI recovered) | GAP-8a's consistency half | Attributum (re-typed) | ✅ `Ethica/Attributum/Models/InfiniteAttribute.lean` — carrier `InfThing` (one substance) with `Attr := Nat`. `inf_def6_recovered : HasInfiniteAttrs deus` satisfies Def. VI's *infinitis attributis* clause with a God present — the exact configuration `def6_infinitis_attributis_unsatisfiable` rules out in Pars I. Contrast `Models/MultiAttribute.lean`, which gets infinitude on the full `Pars1Axioms` register only by being **godless**. Here: plurality *and* God, simultaneously. Depends on **no axioms**. |

---

## Cross-layer formalisations

The methodological note in `Definitions.lean` advertises three
formalisations of Pars I — base FOL, modal S5, categorical / topos.

| Layer       | Status | File (planned)              |
|-------------|--------|------------------------------|
| Base FOL    | 🟡     | `Ethica/Pars1/*` (this work) |
| Modal S5    | 🟡     | `Ethica/Pars1/ModalForm.lean` — fully connected scaffold with all four demote attempts executed. Bridges A18/A19/A20/A21, candidates A16/A17 (Prop. I priority), Section III commitments A22 (PSR-substance), A23 (PSR-self-cause), A24 (PSR-essence-perception), A25/A26 (PSR-plenitude + god-uniqueness). **A18 load-bearing**: `substance_exists_at_every_world` proves `Substance s → ∀ w, existsAt s w` via A13 + A18. **A12 demote (Della Rocca route)**: `prop_5_demote_via_PSR_all_attributes` proves *partial* A12 (all-shared-attributes → identity) from A22; the full any-shared-attribute reading is **NOT** derivable — witnessed at kernel level by `A12CounterModel` and the `A12_falsified` theorem in `Models/Counterexamples.lean`. **A13 demote (modal translation)**: `prop_7_demote_via_PSR` delivers full A13 via A23 + A18 + A3-first-clause; equal-strength translation, not reduction. **A14 demote (essence-perception)**: `prop_A14_demote_via_PSR` delivers full A14 via A24 — trivial redescription modulo `Attribute` unfolding. The genuine universality clause that resists PSR demote is A15, not A14. **A15 demote (decomposition)**: `prop_A15_demote_via_decomposition` delivers A15 via A25 + A26 jointly; plenitude alone fails — witnessed by `A15CounterModel` and the `A15_falsified` theorem. **Demote taxonomy**: A12 (partial-only, irreducible), A13 (modal translation, equal strength), A14 (trivial redescription, equal strength), A15 (decomposition required, irreducible). The engineering separation forced by Lean's diamond inheritance — a typeclass-mechanism layering that treats attribute as a "basic and irreducible way of being" (Bennett 1984 §16, p. 61) — contrasts with the unified PSR-driven structure Della Rocca's reading would require. |
| Categorical | ⏳     | `Ethica/Pars1/CategoryForm.lean` (not started) |
