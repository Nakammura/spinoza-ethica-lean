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
| VI  | *Deus*                      | 🟡     | `IsGod` requires ≥1 attribute (third conjunct, **now redundant under A14** but retained for textual fidelity to Spinoza); (a) full *infinitis attributis* cardinality — GAP-8a; (b) universality over substance attributes — GAP-8b ✅ (closed by A15 promotion). |
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
| IX   | More reality ⇒ more attributes.                                 | 🚫     | Needs reality-measure / counting framework. |
| X    | Each attribute of a substance is per se conceived.              | ✅     | `prop_10_attributePerSe`. |
| XI   | God necessarily exists.                                         | ⏳     | The big payoff. **Critical path is longer than initially estimated.** Bennett 1984 §18 catalogues four reading paths through Spinoza's *demonstrationes* (causa-sui direct; reductio via PSR; power-based; *a posteriori* in the scholium); each requires at least one substantive Section III commitment **beyond** A12 + A13 + GAP-8a. Candidates: a "consistent essence ⇒ instantiation" axiom (Della Rocca / modal ontological-argument flavour), or its PSR-flavoured equivalent. Bennett line holds these commitments are not derivable within Spinoza's stated axioms. Closing **GAP-8a (cardinality)** alone is **not sufficient**; additional Section III commitment(s) are required for at least one of the four reading paths. |
| XII  | No attribute can be conceived such that substance is divisible. | ⏳     | Depends on Prop. X. |
| XIII | Absolutely infinite substance is indivisible.                   | ⏳     | Depends on Prop. XII. |
| XIV  | Besides God, no substance can be given or conceived.            | 📜     | `prop_14_onlyGodIsSubstance` mechanised in short form via A12 + A14 + A15 (Section III commitments) — **closing GAP-8b + GAP-13** in the process. 3-line proof, `sorry`-free. The 📜 marker is retained because the proof rests on three Section III axioms (V, VI, X are still the only theorems mechanised in the substantive sense). `Models/TwoSubstance.lean` **falsifies A15** and is therefore a Bennett-line non-Spinoza bench — it cannot carry a `Pars1Axioms` instance, which is the correct migration outcome (closure-protocol step 6(d)). |
| XV   | Whatever is, is in God; nothing without God can be conceived.   | ⏳     | Depends on Prop. XIV + Defs. III, V. |
| XVI  | From divine nature, infinite things in infinite ways follow.    | ⏳     | Depends on Prop. XI + Def. VI. |
| XVII | God acts from the laws of his own nature alone.                 | ⏳     | Depends on Prop. XI + Def. VII. |
| XVIII| God is the immanent, not transitive, cause of all things.       | ⏳     | Depends on Prop. XV + Prop. XVI. |
| XIX  | God / all attributes of God are eternal.                        | ⏳     | Depends on Def. VIII + Prop. XI. |
| XX   | God's existence and essence are one and the same.               | ⏳     | Depends on Prop. XIX + Def. VI. |
| XXI  | All that follows from absolute nature of any attribute is infinite & eternal. | ⏳ | Depends on Prop. XI + XVI. |
| XXII | What follows from a modified attribute is also infinite & eternal. | ⏳ | Depends on Prop. XXI. |
| XXIII| Every necessarily-existing infinite mode follows from God's attribute. | ⏳ | Depends on Prop. XXI + XXII. |
| XXIV | Essence of things produced by God does not involve existence.   | ⏳     | Depends on Def. I + Prop. XV. |
| XXV  | God is the efficient cause not only of existence but of essence of things. | ⏳ | Depends on Prop. XV + XXIV. |
| XXVI | Things determined to act are determined by God.                 | ⏳     | Depends on Prop. XXV. |
| XXVII| Things determined by God cannot render themselves undetermined. | ⏳     | Depends on Prop. XXVI. |
| XXVIII| Every singular thing's existence and action is determined by another finite cause, ad infinitum. | ⏳ | **Crucial for finite mode causation; this is what review §3.1 protects.** |
| XXIX | Nothing in nature is contingent; all is determined by divine necessity. | ⏳ | Depends on Prop. XXV–XXVIII. |
| XXX  | An actually existing intellect comprehends God's attributes and his affections. | ⏳ | Depends on A6 + Pars II prerequisites. |
| XXXI | The actually existing intellect is a mode of thinking.          | ⏳     | Pars II territory. |
| XXXII| Will is not a free cause but a necessary one.                   | ⏳     | Pars II territory. |
| XXXIII| Things could not have been produced in any other way or order. | ⏳     | Depends on Prop. XVI + XXVI–XXIX. |
| XXXIV | God's power = God's essence.                                   | ⏳     | Depends on Prop. XI + XX. |
| XXXV | What we conceive to be in God's power necessarily exists.       | ⏳     | Depends on Prop. XXXIV. |
| XXXVI| Nothing exists from whose nature an effect does not follow.     | ⏳     | Depends on Prop. XXIX + XXV. |

**Tally** (after the review of 2026-05-02 §B.2 honesty pass — the
prior "fully mechanised" count over-counted theorems that are
direct invocations of a Section III commitment axiom; updated
post-GAP-10 closure and Prop. IV expansion):

- ✅ **4 mechanised in the substantive sense** (with one qualifier
  on Prop. IV — see row note: both-modes case is structurally
  captured but information-free internally; mixed-category cases
  exceed Spinoza's textual scope) —
  - **II** (`prop_2_distinctSubstancesShareNothing` Della-Rocca
    form + `prop_2_via_def3` Spinoza-textual form, both 1–3 lines);
  - **IV** (`prop_4_partition` + `prop_4_distinguishedByAttributesOrCategory`,
    proves both the substance/mode partition and the four-case
    distinguishability dichotomy — qualifier above);
  - **VI** (`prop_6_substanceNotProducedByAnother`, 5-line proof
    chaining Prop. III contrapositive + sameNature unfolding +
    A12); and
  - **X** (`prop_10_attributePerSe`, one-line invocation of A10, a
    Section I *definitional bridge*).
- 📜 **2 mechanised by direct invocation of a Section III
  commitment axiom** —
  - **V** (`prop_5_uniqueSubstancePerAttribute` = direct A12); and
  - **VII** (`prop_7_existenceBelongsToSubstance` = direct A13).
  Honest record: A12 *is* essentially Prop. V's content adopted as
  an axiom, and A13 *is* essentially Prop. VII's content adopted
  as an axiom (see `auxiliary_axioms.md` §III). The "proofs" are
  one-liners by design.
- 📜 **+ 1 mechanised by chaining three Section III commitment
  axioms** — **XIV** (`prop_14_onlyGodIsSubstance` consumes
  A12 + A14 + A15; structurally the most Section-III-heavy theorem
  in Pars I, with three commitments threaded through a single
  proof body). Sorry-free; A14 / A15 are now `Pars1Axioms` fields
  (post-§F.α promotion) but remain Section III metaphysical
  commitments per `auxiliary_axioms.md`.
- 🟡 **3 partial** — I (disjointness only — GAP-6 / Prop. I
  priority requires `conceptualDep` at modal layer), III
  (substance-restricted — general form awaits modal layer's
  `hasAttribute`), VIII (not-finite form only; absolutely-infinite
  reading awaits GAP-8a / cardinality).
- ⏳/🚫 **26 deferred or blocked**.

Prop. XI (announced first big payoff) needs more than GAP-8a
closure: see Prop. XI row note above.

### Section III axiom utilization

How load-bearing is each Section III commitment across the project?

| Axiom | Used in (theorems / corollaries)                              | Cost-per-axiom note |
|-------|---------------------------------------------------------------|---------------------|
| A12   | `prop_4_distinguishedByAttributesOrCategory` (direct), `prop_5` (direct), `prop_6` (direct, combined with Prop. III contrapositive `cause_implies_sameNature`), `prop_8` (direct), `prop_14` (direct, combined with A14 + A15) | **Most load-bearing** — used directly in 5 propositions. |
| A13   | `prop_7` + corollaries `prop_7_natureRequiresExistence`, `prop_7_substanceIsCausaSui` | Single proposition + 2 corollaries. |
| A14   | `prop_14` only                                                | **Point-purpose** — committed for one theorem. |
| A15   | `prop_14` only                                                | **Point-purpose** — committed for one theorem. |

Bennett-line reading note: A12 earns its keep across the project,
but A14 and A15 are committed for a single proposition each.
Bennett-leaning readers can drop A14 + A15 to recover the partial
state at the cost of losing Prop. XIV; A12 cannot be dropped
without losing four propositions including Prop. V's
mechanisation altogether.

---

## Models

| Model | Role | Layer | Status |
|-------|------|-------|--------|
| Single-substance (`Unit`) | Consistency witness; S5 modal collapse | Base + modal | ✅ `Models/SingleSubstance.lean` — full `Pars1Axioms` + `CausalAxioms` + all six modal-layer instances on `Unit` × `Unit`. Bridges A18/A19/A20/A21 discharge trivially; A16/A17 hold vacuously. Prop. XIV applies. |
| Two-substance Bennett-line bench | A15 falsifier (post-promotion) | Base | ✅ `Models/TwoSubstance.lean` — `EthicaWorld` only; **falsifies A15** via `twosubst_falsifies_A15`. |
| Multi-world A18 bridge-bite | A18 non-trivial bite witness | Modal | ✅ `Models/MultiWorld.lean` — `Thing := necessary \| contingent`, `World := w0 \| w1`. A18 fires non-vacuously on the `False ↔ False` branch. Does **not** exercise A19/A20/A21. |
| A12 counter-model | Irreducibility witness (Bennett #1) | Base + PSR | ✅ `Models/Counterexamples.lean` `A12CounterModel` — 4-element world; PSR + base satisfied, A12 falsified. Kernel-level hard fact. |
| A15 counter-model | Irreducibility witness (Bennett #2) | Base + plenitude | ✅ `Models/Counterexamples.lean` `A15CounterModel` — 3-element world; plenitude satisfied, A15 falsified. Kernel-level hard fact. |
| Multi-attribute substance | Planned future bench | Base | ⏳ `MultiAttribute.lean` (not started). |
| Prop. III bite-test | Non-identity `Cause` exercising A4ₛ + A5ₛ contrapositively | Causal | ⏳ Not started; current TwoSubstance uses identity-restricted `Cause` so doesn't exercise A4ₛ+A5ₛ. |

---

## Cross-layer formalisations

The methodological note in `Definitions.lean` advertises three
formalisations of Pars I — base FOL, modal S5, categorical / topos.

| Layer       | Status | File (planned)              |
|-------------|--------|------------------------------|
| Base FOL    | 🟡     | `Ethica/Pars1/*` (this work) |
| Modal S5    | 🟡     | `Ethica/Pars1/ModalForm.lean` — fully connected scaffold with all four demote attempts executed. Bridges A18/A19/A20/A21, candidates A16/A17 (Prop. I priority), Section III commitments A22 (PSR-substance), A23 (PSR-self-cause), A24 (PSR-essence-perception), A25/A26 (PSR-plenitude + god-uniqueness). **A18 load-bearing**: `substance_exists_at_every_world` proves `Substance s → ∀ w, existsAt s w` via A13 + A18. **A12 demote (Della Rocca route)**: `prop_5_demote_via_PSR_all_attributes` proves *partial* A12 (all-shared-attributes → identity) from A22; the full any-shared-attribute reading is **NOT** derivable — witnessed at kernel level by `A12CounterModel` and the `A12_falsified` theorem in `Models/Counterexamples.lean`. **A13 demote (modal translation)**: `prop_7_demote_via_PSR` delivers full A13 via A23 + A18 + A3-first-clause; equal-strength translation, not reduction. **A14 demote (essence-perception)**: `prop_A14_demote_via_PSR` delivers full A14 via A24 — trivial redescription modulo `Attribute` unfolding. The genuine universality clause that resists PSR demote is A15, not A14. **A15 demote (decomposition)**: `prop_A15_demote_via_decomposition` delivers A15 via A25 + A26 jointly; plenitude alone fails — witnessed by `A15CounterModel` and the `A15_falsified` theorem. **Demote taxonomy**: A12 (partial-only, irreducible), A13 (modal translation, equal strength), A14 (trivial redescription, equal strength), A15 (decomposition required, irreducible). The engineering separation forced by Lean's diamond inheritance — a typeclass-mechanism layering that treats attribute as a "basic and irreducible way of being" (Bennett 1984 §16, p. 61) — contrasts with the unified PSR-driven structure Della Rocca's reading would require. |
| Categorical | ⏳     | `Ethica/Pars1/CategoryForm.lean` (not started) |
