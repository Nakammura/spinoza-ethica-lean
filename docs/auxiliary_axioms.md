# Auxiliary Axioms Register — Spinoza's *Ethica* in Lean 4

This document catalogues every auxiliary axiom we have added to the
`Pars1Axioms` and `CausalAxioms` typeclasses *beyond* Spinoza's
seven (A1–A7). Each auxiliary axiom is a commitment we make on
Spinoza's behalf where the source text leaves a step implicit; the
register's purpose is to put those commitments under a spotlight,
not hide them behind a `class`.

The closure protocol in `gaps.md` step 3 requires a corresponding
entry here for any auxiliary axiom introduced to discharge a `GAP`.
This file is the system of record for those entries.

The auxiliary axioms split into three qualitatively distinct
sections. Mixing them in one flat list hides the philosophical
weight differences:

- **Section I — Definitional bridges**. Make explicit the
  definitional or conceptual coextensions Spinoza uses tacitly. The
  commentary literature broadly accepts these are operative in the
  text; we make them machine-checkable. Light commitments.
- **Section II — Substantive promotions of `Pars1Axioms`
  placeholders (A4, A5)**. Promote Spinoza's own A1–A7 from `True`
  placeholders to substantive content within an extended typeclass.
  Currently A4 and A5 are promoted (A1, A2, A7 are already
  substantive in `Pars1Axioms`; A3 / A6 await modal / Pars II
  layers). Medium commitments.
- **Section III — Substantive metaphysical commitments**. Fill
  demonstrably-incomplete steps in Spinoza's *demonstrationes*.
  Commentary literature widely acknowledges these gaps; the axioms
  here are our considered reconstructions. **Heavy** commitments —
  swap a Section III axiom and you change the Spinoza system, not
  just its presentation.

---

# Section I — Definitional bridges

---

## A1ₑ — Exclusivity of *in se* and *in alio*

**Lean signature**:
```lean
ax1_exclusive : ∀ x : Thing, ¬ (inItself x ∧ inAnother x)
```

**Why we add it**: Spinoza's A1 (*Omnia, quae sunt, vel in se, vel
in alio sunt*) uses *vel… vel*, which in classical Latin can be
inclusive or exclusive. The Demonstrationes throughout Pars I
*assume* exclusivity (e.g. Prop. I's disjointness fragment uses it),
but Spinoza never asserts it as a separate axiom.

**Commentary**: We adopt the exclusive reading because the chain
of demonstrations in Pars I (P1, P4, P5) silently requires it.
Bennett 1984 §16 treats this exclusivity as a substantive
metaphysical commitment about ontological categories (substance
vs. mode), not a logical property of *vel*. We make the choice
visible at the axiom layer and document the alternative.

**Used by**: `prop_1_substanceDisjointFromModes`.

**Closes**: GAP-1.

---

## A8 — Ontological–conceptual parallelism (*in se* / *per se*)

**Lean signature**:
```lean
ax_inItself_iff_perSeConceived :
  ∀ x : Thing, inItself x ↔ perSeConceived x
```

**Why we add it**: Def. III ("substance = in se est et per se
concipitur") pairs the ontological clause "in itself" with the
conceptual clause "per se conceived". Spinoza never asserts they
are coextensive; A1 + A2 alone do not force the iff. To prove the
substance/mode partition (Prop. IV), we need the bridge.

**Commentary**: This is a *PSR-flavoured* commitment. Della Rocca
2008 ch. 1–2 makes it constitutive (the Principle of Sufficient
Reason forces ontological dependence to track conceptual
dependence). Curley 1988 ch. 1 treats it as a tacit Spinozistic
principle. **Bennett 1984 §16 explicitly rejects the coextension** —
he argues self-existent items conceived through another are
logically possible and Spinoza simply assumes their absence.
Adopting A8 commits us to the Della Rocca / Curley reading.

**Used by**: `prop_4_partition`.

**Closes**: GAP-4 (in-half).

---

## A9 — Ontological–conceptual parallelism (*in alio* / *per alio*)

**Lean signature**:
```lean
ax_inAnother_iff_conceivedThroughAnother :
  ∀ x : Thing, inAnother x ↔ conceivedThroughAnother x
```

**Why we add it**: The mode-side counterpart of A8.

**Commentary**: Same PSR caveat as A8.

**Used by**: `prop_4_partition`.

**Closes**: GAP-4 (alio-half).

### Quiet payoff of A8 + A9

A consequence not separately axiomatised but worth recording:
`perSeConceived` and `conceivedThroughAnother` are mutually exclusive
without a fresh axiom. The argument is one line —
A1ₑ gives `¬ (inItself x ∧ inAnother x)`; transferring through A8
and A9 gives `¬ (perSeConceived x ∧ conceivedThroughAnother x)`. So
introducing A8/A9 spares us a hypothetical "A2ₑ" exclusivity
counterpart for the conceptual side. Documented here so we do not
accidentally re-axiomatise it later.

---

## A10 — Attribute–substance identity-of-conception

**Lean signature**:
```lean
ax_attribute_perSe :
  ∀ a s : Thing, Attribute a s → perSeConceived a
```

**Why we add it**: Spinoza's Prop. X demonstration is one sentence:
"Attributum enim est id quod intellectus de substantia percipit
tanquam ejus essentiam constituens (per def. 4) adeoque (per def. 3)
per se concipi debet." The leap from "substance is per se
conceived" (Def. III) to "the *attribute* is per se conceived"
presupposes that conceiving substance under attribute `a` is
conceiving `a` itself.

**Commentary**: Della Rocca 2008 ch. 2 reads attributes as the
modes of conception under which substance is grasped, making this
identity definitional. Garrett *Spinoza on the Essence of the Human
Mind* treats it similarly. The hypothesis of A10 is the full
`Attribute a s` (which carries `Substance s`) rather than an
arbitrary `intellectPerceivesAsEssence s a`: the latter would be
over-strong, licensing the conclusion on spurious
essence-attributions.

**Used by**: `prop_10_attributePerSe`.

**Closes**: GAP-5.

---

## A11 — *Causa sui* clause-equivalence

**Lean signature**:
```lean
ax_causaSui_iff :
  ∀ x : Thing, involvesExistence x ↔ natureRequiresExistence x
```

**Why we add it**: Def. I — *Per causam sui intelligo id cujus
essentia involvit existentiam, sive id cujus natura non potest
concipi nisi existens* — joins two clauses with *sive*. Curley
1985 p. 408 reads *sive* here as *id est*: the second clause
re-expresses the first. We define `causaSui` as the first clause
only; A11 lets us recover the second on demand.

**Commentary**: Encoding `causaSui` as the *conjunction* of both
clauses would be a stronger commitment than *sive = id est* warrants.
The single-clause definition + bridging axiom A11 keeps the
definition aligned with the biconditional reading.

**Used by**: `prop_7_natureRequiresExistence` (corollary of Prop. VII;
the first load-bearing use of A11). Will also be used in Prop. XI's
aggregation.

---

# Section II — Substantive promotions of `Pars1Axioms` placeholders (A4, A5)

---

## A4ₛ — Effect intelligible through cause (*substantive form of A4*)

**Lean signature** (in `CausalAxioms`):
```lean
ax4_effectIntelligibleThroughCause :
  ∀ c e : Thing, Cause c e → intelligibleThrough e c
```

**Why we add it**: A4 in `Pars1Axioms` is a `True : Prop`
placeholder; the real epistemic content needs the `Cause` and
`intelligibleThrough` primitives introduced in `CausalWorld`.

**Commentary**: A separate `ax3_causeGroundsIntelligibility` field
would carry literally the same Lean signature, so it is omitted;
A3's distinct *ontological-necessitation* content awaits the modal
layer (tracked as GAP-7).

**Used by**: `prop_3_noCommonNoCause`.

---

## A5ₛ — No common nature, no intelligibility (*substance-restricted*)

**Lean signature** (in `CausalAxioms`):
```lean
ax5_noCommonNoIntelligibility :
  ∀ x y : Thing, Substance x → Substance y →
    ¬ sameNature x y → ¬ intelligibleThrough x y
```

**Why we add it**: Spinoza's A5 ("things sharing nothing in common
cannot be understood through one another") in its general form,
combined with the GAP-2 closure that derives `sameNature` from
`Attribute` (hence implicitly substance-only), would force
`¬ Cause m₁ m₂` for every pair of modes — collapsing the
finite-mode causation Pars II–V depend on. The substance-restricted
form preserves Prop. III's substance-side use while leaving
mode-causation expressible.

**Commentary**: The substance-restriction is a soundness fix. The
fully general A5 will be reinstated at the modal layer, where a
separate `hasAttribute : Thing → Thing → Prop` relation will give
`sameNature` proper coverage over modes as well.

**Used by**: `prop_3_noCommonNoCause`.

**Closes**: the GAP-2 soundness regression (restricting A5ₛ to
substances so that finite-mode causation survives).

---

# Section III — Substantive metaphysical commitments

The Section III register has grown across the project's lifetime
to ~11 commitments. Sub-categorisation by role:

- **§III.A** — Base `Pars1Axioms` Section III commitments (A12,
  A13, A14, A15). The four substantive metaphysical claims that
  fill demonstratio gaps in Spinoza's text.
- **§III.B** — Modal-layer conceptual asymmetry candidates (A16,
  A17). The Prop. I priority asymmetry between substance and
  mode dependence.
- **§III.C** — Modal-layer PSR demote axioms (A22-A26). PSR-
  flavoured commitments introduced for the demote-attempt
  experiments. These have a **recursive role**: they are
  Section III axioms introduced *to derive* §III.A axioms — and
  the demote outcome documents whether the derivation is a
  reduction (Della Rocca line) or a relocation / partial-fail
  (Bennett line).

A note on the structural adjacency of A14 and A15:

A14 (`∀ s, Substance s → ∃ a, Attribute a s`) and A15
(`∀ g s a, IsGod g → Substance s → Attribute a s → Attribute a g`)
are structurally adjacent — both are claims about substances and
attributes — and easy to conflate in prose discussion. The
mechanical separation:

- A14 is **existence over attributes** (`∃ a`): each substance
  has *at least one* attribute. PSR-flavoured existence axioms
  demote it cleanly (see A24).
- A15 is **universality over attributes**: every god has *every*
  realised attribute. PSR-flavoured axioms cannot reach this on
  their own — see A25/A26 and the counter-model in
  `Ethica/Pars1/Models/Counterexamples.lean`.

Whenever Spinoza commentary discusses "Spinoza's commitment to
substance having attributes", clarify which of A14 or A15 is
meant.

---

## §III.A — Base `Pars1Axioms` commitments

---

## A12 — Indiscernibility of substance by attribute

**Lean signature**:
```lean
ax_substanceIdByAttribute :
  ∀ s₁ s₂ a : Thing, Attribute a s₁ → Attribute a s₂ → s₁ = s₂
```

**Why we add it**: This is, in essence, the content of Prop. V
("In nature there cannot be two substances of the same attribute")
adopted as an axiom rather than derived. We do this **because
Spinoza's *demonstratio* of Prop. V is widely held in the commentary
literature to be invalid or incomplete as it stands**, and the
additional commitment required to make it work cannot be hidden
inside a "derivation" without dishonesty.

The hypothesis is the full `Attribute a s` in both arguments
(which carries `Substance s`); the redundant `Substance s₁`,
`Substance s₂` hypotheses are dropped — same hygiene as A10.

**Commentary**:
- *Bennett 1984 §17* identifies "one dubious move and one invalid
  one" in Prop. V's demonstration (p. 67) and shows it can deliver
  at most the all-shared-attribute case (p. 69), not the
  any-shared-attribute case Spinoza announces.
- *Garrett 1990 ("Ethics IP5: Shared Attributes and the Basis of
  Spinoza's Monism")* argues that Prop. V holds under a strong
  reading of Definition III together with ID5 / IA1 / IA2; this
  combination is not entailed by the literal text of Spinoza's
  stated definitions and axioms.
- *Della Rocca 2008 ch. 2* rescues Prop. V via the Principle of
  Sufficient Reason (PSR), but PSR itself must be committed as an
  axiom; the rescue is a **relocation, not an elimination**, of
  the commitment.

We choose to commit visibly at the axiom layer rather than via
PSR-flavoured axioms strewn through a modal-layer derivation. The
Bennett–Della Rocca debate is preserved in the commentary record;
A12 represents Spinoza-as-Della-Rocca-reads-him.

**Caveat — downstream consequences**: A12 dramatically shortens the
proofs of Props. VI and XIV. Specifically:
- Prop. VI ("substance cannot be produced by another") follows in
  a few lines via Prop. III contrapositive + A12.
- Prop. XIV ("besides God, no substance") needs A12 *together with*
  a substantive form of Def. VI's "infinitis attributis" clause
  (currently weakened — GAP-8). Without GAP-8 closed, Prop. XIV
  cannot be proved from A12 alone.

This is not a bug — it reflects Della Rocca's PSR-driven reading
that Pars I propositions V–XIV are consequences of a single deep
commitment (indiscernibility-by-attribute) plus the cardinality
content of Def. VI. Readers preferring Bennett's reading (in which
Prop. V should not hold without further argument) can drop A12 to
recover that alternative.

**Used by**: `prop_5_uniqueSubstancePerAttribute`,
`prop_6_substanceNotProducedByAnother` (transitively),
`prop_8_substanceIsNotFinite`,
`prop_14_onlyGodIsSubstance` (via `private axiom` skeleton premises;
see Propositions.lean and GAP-8 / GAP-13 in `gaps.md`).

**Closes**: Prop. V mechanisation gap.

**Related GAP**: GAP-11 — modal-layer derivation of A12. Tracked
but **not guaranteed to succeed**: the Bennett line of commentary
holds that no such derivation is available within Spinoza's stated
axioms; closing GAP-11 may itself require a further axiom
(PSR or substance plenitude), in which case A12 stays in the
register permanently.

**Counter-model bench**: see
`Ethica/Pars1/Models/TwoSubstance.lean` for a model that exercises
A12 non-trivially (single-substance Unit model satisfies A12
vacuously and so cannot witness the axiom's bite).

---

## A13 — Substance involves existence

**Lean signature**:
```lean
ax_substance_involves_existence :
  ∀ s : Thing, Substance s → involvesExistence s
```

**Why we add it**: This is the content of Prop. VII
("Ad naturam substantiae pertinet existere") committed at the axiom
layer. Spinoza's *demonstratio* of Prop. VII chains Prop. VI
corollary with an unstated PSR-flavoured commitment, and both
links carry gaps:

- Prop. VI corollary's mode-extension. The corollary asserts that
  substance cannot be produced by anything (substances + modes
  exhaust the ontology, by A1 + Defs III/V, hence both cases must
  be ruled out). Spinoza rules out the substance case via Prop. VI
  proper. The mode case is asserted but not actually demonstrated
  in the *corollarium*. The *aliter* (alternative argument) appeals
  to A4 + Def. III, but requires a conceptual-uniqueness bridge
  ("if `x` is intelligible through `y ≠ x`, then `x` is not per se
  conceived") that we have not axiomatised — and adding such a
  bridge is itself a substantive commitment, not a definitional
  one.
- The "no external cause ⇒ self-caused" step. Even granted the
  corollary, deriving `causaSui` requires that *some* explanation
  for substance's existence is mandatory; this is the Principle of
  Sufficient Reason move (Della Rocca 2008 ch. 2).

**Commentary**:
- *Bennett 1984 §18* finds Prop. VII's *demonstratio* relying on
  the same kind of unstated commitments that flaw Prop. V's, with
  the gap closed only by reading Prop. VI corollary in its
  strongest form.
- *Della Rocca 2008 ch. 2* uses PSR to derive Prop. VII; PSR itself
  must then be axiomatised (mirroring the A12 situation).

We adopt A13 as the visible Section-III commitment that
encapsulates these tacit moves. Combined with A11 (causa-sui clause
equivalence), the *natureRequiresExistence* form of Def. I is
recovered on demand, and `causaSui s` follows directly for any
substance.

**Caveat — downstream consequences**: A13 makes Prop. VIII (every
substance is not finite-after-its-kind) provable via A12 + Def. II
+ A13; Prop. XI ("God necessarily exists") will require A13
together with the cardinality content of Def. VI (GAP-8) — Prop. XI
is what *aggregates* A13 into the unique necessarily-existent
absolutely-infinite substance.

**Used by**: `prop_7_existenceBelongsToSubstance`,
`prop_7_natureRequiresExistence` (via A11),
`prop_7_substanceIsCausaSui`, `prop_8_substanceIsNotFinite`
(transitively through A12).

**Closes**: Prop. VII mechanisation gap. First load-bearing use of
A11 (which previously had `Used by: not yet used`).

**Related GAP**: GAP-12 — modal-layer derivation of A13 from a
substantive PSR + the substantive A3/A4 of `Causation.lean`. Same
Bennett-honest scoping as GAP-11: derivation is not guaranteed; if
PSR itself must be axiomatised, A13 stays in Section III
permanently.

---

## A14 — Substance has at least one attribute

**Status**: ✅ **promoted**. Now a `Pars1Axioms` field
(`ax_substance_has_attribute`).

**Lean signature**:
```lean
ax_substance_has_attribute :
  ∀ s : Thing, Substance s → ∃ a, Attribute a s
```

**Why we add it**: Spinoza's Defs. III + IV do not entail that
every substance has an attribute (without A14, an attribute-free
substance was a model of `Pars1Axioms`). But Spinoza's *usage*
throughout Pars I treats the existence of attributes as
constitutive of substance. `prop_14`'s demonstration cannot start
without `∃ a, Attribute a s` for the substance `s`.

**Commentary**: Della Rocca 2008 takes this for granted under PSR;
Bennett 1984 §17 treats it as an independent commitment.

**Used by**: `prop_14_onlyGodIsSubstance`.

**Closes**: GAP-13.

**Bench note**: `Ethica/Pars1/Models/TwoSubstance.lean` *satisfies*
A14 — each element is its own attribute, so `∃ a, Attribute a s`
holds for both substances. **A14 is therefore not the cause of
TwoSubstance's loss of `Pars1Axioms` instance**; that loss is
incurred entirely on A15 (next entry). This matters for the
Bennett-line reading: Bennett rejects the *universality* clause
(A15) but does not necessarily reject the *existence* clause
(A14), so the philosophical geography of the two axioms — and
their migration costs — is distinct.

**Redundancy note**: A14 makes `IsGod`'s third conjunct
(`∃ a, Attribute a g`) **logically redundant** under any
`[Pars1Axioms Thing]` context — `Substance g` (first conjunct of
`IsGod`) plus A14 derive the third conjunct directly. The clause
is retained at the `Definitions.lean` layer for textual fidelity
to Spinoza's *substantia constantem … attributis* and to keep
`IsGod` self-contained at the `[EthicaWorld Thing]` level (no
hidden dependency on `Pars1Axioms`). See `coverage.md` Def. VI
row.

**Related GAP (Bennett-honest scoping)**: As with A12 and A13, the
modal-layer route to demote A14 from axiom to theorem is **not
guaranteed to succeed**. Della Rocca's PSR-driven derivation
(see GAP-13's Resolution path) requires (i) committing PSR and
(ii) bridging `intelligibleVia` to `Attribute` constitutively;
both are themselves substantive commitments. If the Bennett line
is correct, A14 stays in Section III permanently — the commitment
relocates rather than dissolves. We track the attempt; we do not
promise it closes.

---

## A15 — God has every substance's attribute (substantive Def. VI)

**Status**: ✅ **promoted**. Now a `Pars1Axioms` field
(`ax_IsGod_has_attribute_of`). Closes GAP-8b. Cardinality (GAP-8a)
remains separately tracked.

**Lean signature**:
```lean
ax_IsGod_has_attribute_of :
  ∀ g s a : Thing, IsGod g → Substance s → Attribute a s →
    Attribute a g
```

**Why we add it**: Def. VI defines God as a substance *constantem
infinitis attributis* — consisting of *infinitely many*
attributes. The full universal-attribute clause ("God has *every*
attribute") is what Prop. XIV requires, and is not captured by
`IsGod g`'s `∃ a, Attribute a g` clause (that only ensures
non-vacuity).

The cardinality form — "infinitely many" — is a separate concern
(GAP-8a, separately tracked); this axiom captures only the
*universality over substance attributes* (GAP-8b), which is what
`prop_14` actually consumes.

**Commentary**: Standard reading in Curley 1985, Della Rocca 2008.
Bennett 1984 §18 flags the universality clause as a substantive
metaphysical commitment in its own right.

**Used by**: `prop_14_onlyGodIsSubstance`. **Whether
`prop_11_GodNecessarilyExists` will also need A15 depends on
which of Bennett 1984 §18's four reading paths is mechanised** —
the *reductio-via-PSR* path uses A15, while the *causa-sui-direct*
and *power-based* paths do not (they require different additional
commitments; A16-candidate territory). Tracked in `coverage.md`'s
Prop. XI critical-path note.

**Closes**: GAP-8b (universality clause). GAP-8a (cardinality)
remains separately tracked — see `gaps.md`'s split treatment of
GAP-8.

**Related GAP (Bennett-honest scoping)**: The modal-layer route
to demote A15 is **not guaranteed**. Della Rocca's reading derives
universality from PSR + Spinoza's plenitude principle; both are
substantive metaphysical commitments. Bennett 1984 §18 holds that
universality cannot be derived from Spinoza's stated axioms. If
Bennett is correct, A15 stays in Section III permanently. We track
the attempt without promising it closes.

**Counter-bench**: `Ethica/Pars1/Models/TwoSubstance.lean`
provides a Bennett-style multi-substance world where A15 is
**falsified**. Because A15 is a `Pars1Axioms` field, that model
cannot carry a `Pars1Axioms` instance — the failure lives at the
type level. The falsification theorem `twosubst_falsifies_A15`
documents the concrete content of A15's commitment.

---

# Modal-layer auxiliary axioms

The following auxiliary axioms live in
`Ethica/Pars1/ModalForm.lean` and are committed at the modal
layer (not in the base `Pars1Axioms`). Section labelling follows
the same I / II / III geometry as the base layer.

---

## A18 — Essential existence is necessary existence (Section I, modal)

**Lean signature** (in `ModalEthicaAxioms`):
```lean
ax_involvesExistence_iff_necExists :
  ∀ s : Thing, involvesExistence s ↔ ∀ w : World, existsAt s w
```

**Why we add it**: Without this bridge, the modal layer's
`existsAt` primitive floats free of the base layer's
`involvesExistence`. A model could have `involvesExistence s`
true and `existsAt s w` false at every `w`, which contradicts
Spinoza's identification of essential existence with necessary
existence (Della Rocca 2008 ch. 4).

**Commentary**: PSR-flavoured (Della Rocca line). Bennett-line
readers might allow `involvesExistence` to express *modal
de-re* essence without committing to actual existence at every
world; the present design takes the Della-Rocca reading.

**Used by**: prerequisite for any A12 / A13 demote attempt at
the modal layer.

---

## A19 — `perSeConceived` is no external conceptual dependence (Section I, modal)

**Lean signature** (in `ConceptualBridges`):
```lean
ax_perSe_iff_no_external_dep :
  ∀ x : Thing, perSeConceived x ↔
    (∀ y : Thing, conceptualDep x y → y = x)
```

**Why we add it**: Bridges the base layer's `perSeConceived`
predicate to the modal layer's `conceptualDep` relation. Without
this, A16-candidate / A17-candidate (asymmetry) sit beside
`perSeConceived` without telling us they have anything to do with
"per se conceiving".

**Commentary**: Della Rocca 2008 ch. 2 reads `per se concipi`
as exactly "no conceptual dependence on anything else". Bennett
1984 §16 might allow self-referential conceptual loops (`x`
depends on `x`); the present axiom permits self-loops too
(`y = x` is a valid case) so this much is Bennett-compatible.
Strict readings rejecting all loops would tighten further.

**Used by**: prerequisite for using `prop_1_priority` in
combination with base-layer `perSeConceived`-flavoured
arguments.

---

## A20 — `conceivedThroughAnother` is external conceptual dependence (Section I, modal)

**Lean signature** (in `ConceptualBridges`):
```lean
ax_throughAnother_iff_external_dep :
  ∀ x : Thing, conceivedThroughAnother x ↔
    (∃ y : Thing, y ≠ x ∧ conceptualDep x y)
```

**Why we add it**: Mode-side counterpart of A19. Connects
`conceivedThroughAnother` to the existence of an `≠ x` thing on
which `x` conceptually depends.

**Commentary**: Same PSR-flavoured caveat as A19.

**Used by**: same as A19.

---

## A21 — `Cause` is necessary causation (Section I, modal)

**Lean signature** (in `ModalCausalAxioms`):
```lean
ax_cause_iff_necCauseAt :
  ∀ c e : Thing, Cause c e ↔ ∀ w : World, causeAt c e w
```

**Why we add it**: Without this, the world-uniform `Cause`
relation in `Causation.lean` and the world-relative `causeAt` in
the modal layer are unrelated primitives. Spinoza's deterministic
metaphysics treats causation as essential, hence world-invariant.

**Commentary**: Della Rocca 2008 ch. 2's reading. Bennett-line
readers who hold causation can be world-relative would weaken
this to `→` only (giving up the `∀ w` direction). The
biconditional commits the Della Rocca line.

**Used by**: prerequisite for the A4ₛ-from-A3-substantive demote
attempt (deferred).

---

## §III.B — Modal-layer conceptual asymmetry candidates

---

## A16-candidate — Modes depend on substances (Section III, modal)

**Status**: ⏳ **not yet promoted**. Currently a
`ConceptualDepAxioms` field in `Ethica/Pars1/ModalForm.lean`.

**Lean signature**:
```lean
ax_mode_depends_on_substance :
  ∀ m : Thing, Mode m →
    ∃ s : Thing, Substance s ∧ conceptualDep m s
```

**Why we add it**: Spinoza Prop. I priority requires that every
mode depend conceptually on some substance. Defs III/V plus the
parallelism axioms (A8, A9) do not entail this on their own —
nothing in the base layer requires modes to *have* a substance
they depend on.

**Commentary**: Della Rocca 2008 ch. 2 derives this from PSR;
Bennett 1984 §16 treats it as an independent commitment. Same
geography as A14: Della Rocca says "follows from PSR", Bennett
says "independent commitment", we record it visibly.

**Used by**: `prop_1_priority` in `ModalForm.lean`.

**Closes**: GAP-6 (substance side of priority).

**Related GAP (Bennett-honest scoping)**: derivation from PSR
+ base axioms (Della Rocca demote attempt) is **not guaranteed**
to succeed. If Bennett is correct, A16 stays in modal-layer
Section III permanently.

---

## §III.C — Modal-layer PSR demote axioms

These axioms are introduced for the demote-attempt experiments
(§δ through §δ-4 in `ModalForm.lean`). They have a recursive
role: they are Section III commitments introduced *in order to
derive* §III.A axioms (A12-A15). The demote outcomes document
the structural status of the §III.A axioms:

| Target | Demote axioms | Outcome | Pattern |
|--------|--------------|---------|---------|
| A12 | A22 (`PSRSubstance`) | Partial only | Irreducible (Bennett-line evidence #1) |
| A13 | A23 (`PSRSelfCause`) + A18 bridge | Full success | Modal translation, equal strength |
| A14 | A24 (`PSREssencePerception`) | Full success | Trivial redescription, equal strength |
| A15 | A25 + A26 (`PSRPlenitude`) | Decomposition only | Irreducible (Bennett-line evidence #2) |

**Counter-models** (`Ethica/Pars1/Models/Counterexamples.lean`)
provide the kernel-level hard facts for the two irreducibility
results:
- `A12CounterModel`: a `StatedAxioms` + `PSRSubstance` instance
  where two distinct substances share an attribute → A12 not
  derivable from the stated register + PSR.
- `A15CounterModel`: a `StatedAxioms` instance with two
  attribute-distinct gods, plenitude holding, A15 falsified →
  A15 not derivable from the stated register + plenitude.

---

## A22 — PSR for substance distinguishability (Section III, modal)

**Status**: ✅ committed as a `PSRSubstance` field in
`Ethica/Pars1/ModalForm.lean`. The class is independently
optional — proofs that need PSR-flavoured demote attempts
require `[PSRSubstance Thing]`; theorems that don't, don't.

**Lean signature**:
```lean
ax_PSR_substance_distinguishability :
  ∀ s₁ s₂ : Thing, Substance s₁ → Substance s₂ → s₁ ≠ s₂ →
    ∃ a, (Attribute a s₁ ∧ ¬ Attribute a s₂) ∨
         (Attribute a s₂ ∧ ¬ Attribute a s₁)
```

**Why we add it**: Della Rocca 2008 ch. 2's reading of Spinoza's
PSR for substances. Distinct substances must have a sufficient
reason for being distinct; per Prop. IV the only available reason
is an attribute difference (modes are posterior — Prop. I
priority). Hence: distinct → some attribute distinguishes them.

**Used by**: `prop_5_demote_via_PSR_all_attributes` —
demonstrating that the *partial* form of A12 (substances sharing
**all** attributes are identical) demotes via PSR.

**Crucial mechanical finding**: full A12 (substances sharing
**any** attribute are identical — Spinoza's actual Prop. V
content) is **NOT** derivable from `[PSRSubstance Thing]` +
base axioms alone. The kernel-level evidence is **a
counter-model**: see `Ethica/Pars1/Models/Counterexamples.lean`
`A12CounterModel`, a 4-element `StatedAxioms` + `PSRSubstance`
instance (all four elements substances) where two distinct
substances share an attribute, falsifying A12. If A12 were derivable
from the stated register + PSR, the derivation would yield `False`
on this model.

A marker theorem `A12_full_NOT_demotable_from_PSR_alone : True :=
trivial` would be a Lean-as-rhetoric trick (`True` proves nothing
about provability); the counter-model replaces any such marker with
a kernel-level hard fact.
This is the **first mechanical evidence in the project for
Bennett 1984 §17's reading** that Spinoza's Prop. V exceeds what
PSR-alone can deliver.

**Bennett-honest scoping**: this axiom and its consequences are
PSR-flavoured (Della Rocca line). Bennett-line readers might
weaken or drop it; in either case, the demote-attempt result
above stands as evidence for Bennett's Prop. V irreducibility
claim.

---

## A23 — PSR for substance self-causation (Section III, modal)

**Status**: ✅ committed as a `PSRSelfCause` field in
`Ethica/Pars1/ModalForm.lean`. The class is independently
optional — like A22 (PSRSubstance), proofs that need this
flavour of PSR-derivation require `[PSRSelfCause Thing World]`.

**Lean signature**:
```lean
ax_substance_self_caused_at_every_world :
  ∀ s : Thing, ∀ w : World, Substance s →
    ModalCausalWorld.causeAt s s w
```

**Why we add it**: Della Rocca 2008 ch. 2's reading of Spinoza's
Prop. VII via PSR. Every substance has a sufficient reason for
its own existence; per Prop. VI corollary the reason cannot be
external; hence it must be internal — substance is *causa sui*,
which on the modal layer reads as "self-caused at every world".

**Used by**: `prop_7_demote_via_PSR` —
demonstrating that A13 (`Pars1Axioms.ax_substance_involves_existence`)
**fully demotes** via the modal-translation route. Combined with
A18 (existence bridge) and A3-first-clause (cause necessitates
effect), A23 delivers
`∀ s, Substance s → involvesExistence s`, which is A13's content.

**Crucial mechanical finding (asymmetry with A12)**:
- A12 demote attempt was **partial only**: PSR-distinguishability
  delivers the all-shared-attribute case, full A12 is strictly
  stronger (Bennett-line evidence).
- A13 demote attempt **fully succeeds via modal translation**:
  A23 + bridges deliver A13's full content. **But** A23 is not
  weaker than A13 — it is a redescription of "substance has
  necessary existence" in modal-causation vocabulary.

The asymmetry reflects philosophical content: A12's universality
clause has no modal equivalent in our vocabulary, while A13's
existence clause does (via modal causation). A12 is **irreducibly
substantive**; A13 is **modally translatable**. Bennett's
irreducibility survives intact for A12; for A13 both readings
can claim partial victory — Della Rocca that A13 *just is* A23,
Bennett that the commitment hasn't decreased in strength.

**Bennett-honest scoping**: A23 is PSR-flavoured (Della Rocca
line). Bennett-line readers who reject A23 retain A13 in its
original Section III form. Either way, the demote-attempt
documents the *structure* of Spinoza's commitment system as
seen through modal vocabulary.

**Translation cost — A18 dependency**: the equivalence between
A23 and A13 holds **modulo A18** (the bridge
`involvesExistence ↔ ∀ w, existsAt`). The A13 demote thus
replaces one `Pars1Axioms` commitment (A13) with one modal-layer
commitment (A23) **plus reliance on the A18 bridge**. The total
commitment count is unchanged; only the locus shifts. Without
A18, A23 alone does not deliver A13's content.

---

## A24 — PSR for substance-essence perception (Section III, modal)

**Status**: ✅ committed as a `PSREssencePerception` field in
`Ethica/Pars1/ModalForm.lean`. Independently optional like A22,
A23.

**Lean signature**:
```lean
ax_substance_has_essence_perception :
  ∀ s : Thing, Substance s →
    ∃ a, intellectPerceivesAsEssence s a
```

**Why we add it**: Della Rocca 2008 ch. 2's reading: every
substance is intelligible (PSR), and intelligibility is mediated
by attributes (Def. IV); hence every substance has an essence the
intellect perceives.

**Used by**: `prop_A14_demote_via_PSR` —
demonstrating that A14 (`Pars1Axioms.ax_substance_has_attribute`)
**fully demotes** via essence-perception. The proof unwraps
`Attribute a s := Substance s ∧ intellectPerceivesAsEssence s a`
and attaches the substance hypothesis to the perception A24
provides.

**Mechanical finding**: A14 is the **trivially redescribable**
case in the demote taxonomy. A24 has the exact same shape as
A14 (`∀ s, Substance s → ∃ a, …`) with `Attribute a s` replaced
by its only non-trivial component `intellectPerceivesAsEssence s
a`. Logically equivalent modulo unfolding. Equal commitment-
strength.

**Why A14 demotes but A15 does not**: A14
(`∀ s, Substance s → ∃ a, Attribute a s`) is substance-universal
but attribute-*existential*, so PSR-style existence axioms
demote it cleanly. A15 is universal in *both* substance and
attribute (every god has *every* realised substance attribute),
which PSR's existence-explanatory shape cannot reach. The
distinction sharpens the categorisation of which axioms are
PSR-reducible and which are not.

**Demote taxonomy after §δ, §δ-2, §δ-3**:

| Axiom | Demote outcome | Pattern |
|-------|----------------|---------|
| A12 | Partial only — full content irreducible | Bennett-line evidence (universality of attribute-individuation) |
| A13 | Full success via modal translation | Redescription at equal strength (existence ↔ self-causation) |
| A14 | Full success, trivially | Redescription at equal strength (Attribute ↔ essence-perception) |
| A15 | Pending §δ-4 | Predicted: irreducible (true universality clause) |

**Bennett-honest scoping**: A24 is PSR-flavoured. Same caveat as
A22, A23 — the demote tells us about the *structure* of
Spinoza's commitments, not their elimination.

---

## A25, A26 — PSR plenitude + god uniqueness (Section III, modal)

**Status**: ✅ committed as fields of a `PSRPlenitude` class in
`Ethica/Pars1/ModalForm.lean`. Two axioms in one class because
they jointly demote A15 — neither alone suffices.

**Lean signatures**:
```lean
ax_plenitude_attribute :
  ∀ a s, Substance s → Attribute a s →
    ∃ g, IsGod g ∧ Attribute a g

ax_god_unique :
  ∀ g₁ g₂, IsGod g₁ → IsGod g₂ → g₁ = g₂
```

**Why we add them**: Della Rocca 2008 ch. 2's reading of A15
decomposes into (i) plenitude — every realised substance attribute
is realised in some god — and (ii) uniqueness — all gods are
identical.

**Used by**: `prop_A15_demote_via_decomposition` —
demonstrating that A15 fully demotes from A25 + A26 jointly.

**Mechanical finding**: A15 demote requires **both** axioms.
Plenitude alone is genuinely weaker than A15: see
`Ethica/Pars1/Models/Counterexamples.lean` `A15CounterModel`,
where plenitude holds but A15 fails. Hence A15 cannot be reduced
to plenitude alone — it is **irreducible** in the same sense A12
is. This is the **second mechanical evidence in the project for
Bennett 1984 §17 / §18's reading**: PSR's existence-explanatory
power does not reach genuinely universal claims (over attributes).

**A26 is strictly weaker than Prop. XIV**: A26 asserts only that
any two gods are identical — it does not rule out non-god
substances. Prop. XIV (`Praeter Deum nulla dari neque concipi
potest substantia` — *every* substance is god) is strictly
stronger: it requires combining A26 with the universality reach
of A15 to conclude `∀ s, Substance s → s = god`. The previous
self-assessment "A26 is essentially Prop. XIV's content" was too
generous; the corrected reading: **the A15 demote via A25 + A26
trades one universality (over attributes) for two commitments —
an existence (plenitude over attributes) plus a different
universality (over gods) — neither strictly weaker than A15.**

The decomposition into A25 + A26 is **not a reduction**:
universality of attribute-presence in gods (A15) is replaced by
universality of god-identity (A26) plus existence of god-bearers
(A25). The direction of universality shifts, but the
total Section III commitment count goes from 1 to 2.

**Bennett-honest scoping**: A25 + A26 are PSR-flavoured. The
decomposition documents the *structure* of A15's commitment,
showing it splits into existence (plenitude) + identity
(uniqueness) — each at Section III strength.

---

## A17-candidate — Substances do not depend on modes (Section III, modal)

**Status**: ⏳ **not yet promoted**. Currently a
`ConceptualDepAxioms` field.

**Lean signature**:
```lean
ax_substance_not_dep_on_mode :
  ∀ s m : Thing, Substance s → Mode m → ¬ conceptualDep s m
```

**Why we add it**: The asymmetry of Prop. I priority. Defs III/V
+ parallelism do not exclude substance-on-mode dependence; this
is precisely the asymmetric content Curley 1988 ch. 1 reads into
"prior natura".

**Commentary**: Same Bennett-vs-Della-Rocca geography as A16.

**Used by**: `prop_1_priority`.

**Closes**: GAP-6 (asymmetry side).

**Related GAP (Bennett-honest scoping)**: same as A16.
