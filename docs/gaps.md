# Gaps Register — Spinoza's *Ethica* in Lean 4

This document tracks every `sorry` / `GAP-N` marker in the source
tree, the philosophical reason the gap exists, and the planned
resolution path.

The point is to be honest: Spinoza's demonstrations sometimes leap
where modern mechanised proof cannot follow without explicit
auxiliary commitments. Each gap is a *promissory note*, not silence.

For coverage of *which propositions are mechanised at all*, see
`coverage.md`. For the catalogue of auxiliary axioms introduced
when closing a gap, see `auxiliary_axioms.md`.

---

## GAP-1 — *In se* and *in alio* exclusivity

**Location**: `Ethica/Pars1/Propositions.lean`,
`prop_1_substanceDisjointFromModes` (renamed from
`prop_1_substancePriorToModes` after review §2.1).

**Issue**: Spinoza treats Axiom I ("everything is either in itself
or in another") as introducing an *exclusive* disjunction; `inItself
x ∧ inAnother x` should be impossible. He never states this
explicitly, leaving the exclusivity implicit.

**Reading**: The phrase "vel… vel" in Spinoza's Latin is
sometimes inclusive and sometimes exclusive; the chain of
*demonstrationes* in Pars I (especially P1, P4, P5) requires the
A1 disjunction to be read exclusively, even though Spinoza does
not state this explicitly.

**Resolution path**: Add an auxiliary axiom
`ax1_exclusive : ∀ x, ¬ (inItself x ∧ inAnother x)` to the
`Pars1Axioms` typeclass.

**Status**: ✅ closed. `Pars1Axioms.ax1_exclusive`
added; `prop_1_substanceDisjointFromModes` discharges via
`ax1_exclusive x ⟨hself, hother⟩`. Catalogued as A1ₑ in
`auxiliary_axioms.md`. The modal-layer derivation is still open as a
future cross-check.

---

## GAP-2 — *Sameness of nature* via shared attribute

**Location**: `Ethica/Pars1/Propositions.lean`,
`prop_2_distinctSubstancesShareNothing`.

**Issue**: Prop. II says "two substances having different attributes
have nothing in common". The reverse direction — that "having no
common attribute" implies "no shared nature" — requires bridging
the predicates `Attribute` (Def. IV) and `sameNature` (used in
Def. II), which Spinoza never does explicitly.

**Della Rocca reading** (*Spinoza* 2008, ch. 2): Same nature is
*defined* through shared attribute; this is meant to be
constitutive, not a further claim.

**Resolution path**: Either
(a) add the constitutive axiom `sameNature_iff_sharedAttribute`,
(b) replace the primitive `sameNature` with a derived notion
"∃ a, Attribute a x ∧ Attribute a y", which makes the bridge
analytic.

**Status**: ✅ closed via path (b). `sameNature`
removed from the `EthicaWorld` typeclass (no longer primitive) and
redefined in `Definitions.lean` as `∃ a, Attribute a x ∧ Attribute
a y`. Prop. II now closes analytically:
`intro ⟨a, hax, hay⟩; exact hdiff a ⟨hax, hay⟩`.

**Caveat (review §3.1, soundness)**: under the new reading,
`sameNature` implicitly requires both arguments to be substances
(since `Attribute a _` carries `Substance _`). The substantive A5
in `CausalAxioms` was correspondingly restricted to substances —
without that restriction, finite-mode causation in Pars II–V would
collapse. See the **soundness note in GAP-3** below.

For mode-vs-mode "same kind" comparisons (Def. II's bodily
examples), a separate `hasAttribute : Thing → Thing → Prop` will be
added at the modal layer to recover the general form.

---

## GAP-3 — *Causation* predicate

**Location**: `Ethica/Pars1/Causation.lean`, `prop_3_noCommonNoCause`.

**Issue**: Prop. III says "things with nothing in common cannot be
one the cause of the other". This requires a `Cause : Thing → Thing
→ Prop` relation, which the bare `EthicaWorld` lacks.

**Resolution path**: Create `Ethica/Pars1/Causation.lean` introducing
`Cause`, add A3 and A4 in their substantive form, and discharge
Prop. III using A4 ("knowledge of effect involves knowledge of
cause") + A5 ("nothing in common implies no intelligibility through
one another").

**Status**:
  - ✅ initial closure. `CausalWorld` extending
    `EthicaWorld` with `Cause` and `intelligibleThrough`; A4 and A5
    substantive in `CausalAxioms`. `prop_3_noCommonNoCause` proved
    by contraposition via A4 + A5; symmetric corollary provided.
  - 🔧 soundness patch. With `sameNature`
    derived from `Attribute` (GAP-2 path b, hence implicitly
    substance-only), a fully-general A5 would force `¬ Cause m₁ m₂`
    for every pair of modes — wiping out the finite-mode causation
    Pars II–V depend on. Fix:
    - A5 substantive restricted to substances:
      `∀ x y, Substance x → Substance y → ¬ sameNature x y → ¬ intelligibleThrough x y`.
    - `prop_3_noCommonNoCause` and its symmetric corollary now
      require `Substance x` and `Substance y` hypotheses.
    - `CausalAxioms extends Pars1Axioms` so downstream theorems
      consume one typeclass.
    - No `ax3_causeGroundsIntelligibility` field (it would carry
      literally the same Lean signature as A4); A3's distinct
      ontological-necessitation content opened as GAP-7.
    - The general A5 awaits the modal layer's `hasAttribute`.

Catalogued as A4ₛ + A5ₛ in `auxiliary_axioms.md`.

---

## GAP-4 — Ontological–conceptual parallelism

**Location**: `Ethica/Pars1/Propositions.lean`, `prop_4_partition`.

**Issue**: Prop. IV's demonstration uses A1 ("everything is in se or
in alio") together with Defs. III + V to conclude "everything is a
substance or a mode". But Def. III pairs `inItself` with
`perSeConceived` and Def. V pairs `inAnother` with
`conceivedThroughAnother` — the partition only goes through if
each ontological half is *coextensive* with its conceptual half.
Spinoza never states that bridging biconditional explicitly; A1
and A2 together fall short of it.

**Reading**: The parallelism is the load-bearing assumption that
distinguishes Spinoza's monism from mere ontological dualism.
**Della Rocca 2008 ch. 1** and **Curley 1988 ch. 1** both treat it
as a tacit Spinozistic principle (with PSR backing); **Bennett 1984
§16 explicitly rejects the coextension**, treating Spinoza's
parallelism as a substantive metaphysical commitment that should
not be definitional. Adopting A8/A9 commits us to the Della Rocca /
Curley reading; the Bennett alternative is recoverable by deleting
the iffs.

**Resolution path**: Add two auxiliary axioms to `Pars1Axioms`:
- `ax_inItself_iff_perSeConceived`
- `ax_inAnother_iff_conceivedThroughAnother`

**Status**: ✅ closed. Both axioms (A8, A9)
catalogued in `auxiliary_axioms.md`. `prop_4_partition` proves
`Substance x ∨ Mode x` by case-split on A1 and bridging via A8/A9.

---

## GAP-5 — Attribute–substance identity-of-conception

**Location**: `Ethica/Pars1/Propositions.lean`, `prop_10_attributePerSe`.

**Issue**: Prop. X says "every attribute of a substance must be
conceived through itself". Spinoza's demonstration is one sentence —
*Attributum enim est id quod intellectus de substantia percipit
tanquam ejus essentiam constituens (per def. 4) adeoque (per def. 3)
per se concipi debet*. The leap from "substance is per se conceived"
to "the attribute is per se conceived" presupposes that conceiving
a substance under attribute `a` *is* conceiving `a` itself.

**Reading**: Della Rocca, Garrett — attributes are not separable
items glued onto substances; they are the very *modes* under which
substance is conceived.

**Resolution path**: Add `ax_attribute_perSe` to `Pars1Axioms`.

**Status**: ✅ closed (commits `02b435c` for initial form, then
strengthened in the post-review pass). After review §3.2, the
hypothesis was tightened from raw `intellectPerceivesAsEssence s a`
to the full `Attribute a s` (which carries `Substance s`); the
earlier shape would have fired on spurious essence-attributions
beyond what the Della Rocca / Garrett reading licenses. Catalogued
as A10 in `auxiliary_axioms.md`.

---

## GAP-6 — Prop. I priority (asymmetric conceptual dependence)

**Location**: `Ethica/Pars1/Propositions.lean`,
`prop_1_substanceDisjointFromModes`.

**Issue**: Spinoza Prop. I states "Substantia prior est natura suis
affectionibus" — substance is *prior by nature* to its modes. This
is read in the commentary literature (Curley 1988 ch. 1; Bennett
1984 §16) as **asymmetric conceptual dependence**: every mode is
conceived through some substance, but no substance is conceived
through any mode.

What we currently mechanise is the **disjointness fragment** only:
no thing is both a substance and a mode (proved via A1 + A1ₑ). The
priority claim proper is not captured.

**Resolution path**: Introduce a `conceptualDep : Thing → Thing →
Prop` relation at the modal layer, axiomatise its asymmetry between
substance and mode, and prove
```
∀ m, Mode m → ∃ s, Substance s ∧ conceptualDep m s ∧ ¬ conceptualDep s m
```
as `prop_1_priority`.

**Status**: 🟡 partially closed via the modal layer.
`Ethica/Pars1/ModalForm.lean` introduces:

- `ConceptualStructure` (world-invariant `conceptualDep`);
- `ConceptualBridges` (Section I definitional bridges A19, A20:
  `perSeConceived` ↔ no external `conceptualDep`,
  `conceivedThroughAnother` ↔ external `conceptualDep`);
- `ConceptualDepAxioms` (Section III candidate axioms A16, A17:
  the asymmetry of Prop. I priority).

`prop_1_priority` is proved as a 2-line theorem under
`ConceptualDepAxioms`. **The asymmetry itself remains Section III
candidate commitment**, not yet derived from base + PSR; full
closure depends on the Della Rocca demote attempt (deferred).
Bennett-honest scoping: if the demote fails, A16/A17 stay as
modal-layer Section III permanently.

---

## GAP-7 — A3 ontological-necessitation form

**Location**: `Ethica/Pars1/Causation.lean`, `CausalAxioms`.

**Issue**: Spinoza's A3 — *Ex data causa determinata necessario
sequitur effectus, et contra, si nulla detur determinata causa,
impossibile est ut effectus sequatur* — is **ontological-modal**:
given a determinate cause, the effect *necessarily* follows. A4 is
**epistemic**: knowledge of an effect involves knowledge of its
cause. Don Garrett (*A Spinoza Reader* introduction) flags the
independence of these two as a load-bearing interpretive choice.

`CausalAxioms` carries only `ax4_effectIntelligibleThroughCause`:
a separate `ax3_causeGroundsIntelligibility` field would have a
**literally identical** Lean signature, so it is omitted. A3's
distinct ontological content needs a *modal* relation
(e.g. `∀ world, c.exists_in world → e.exists_in world`) that we
have not yet introduced.

**Resolution path**: Introduce a modal world structure and re-state
A3 substantively in `Ethica/Pars1/ModalForm.lean`.

**Status**: 🟡 partially closed via the modal layer; A13 demote
attempt now complete (modal-translation route).
`Ethica/Pars1/ModalForm.lean` introduces:

- `ModalEthicaWorld` (with `existsAt : Thing → World → Prop`);
- `ModalEthicaAxioms` (Section I definitional bridge A18:
  `involvesExistence` ↔ `∀ w, existsAt`);
- `ModalCausalWorld` (with `causeAt : Thing → Thing → World →
  Prop`, extending `ModalEthicaWorld`; **does not** extend
  `CausalWorld` because Lean cannot synthesise the parameter
  `World` from a `CausalWorld Thing` lookup);
- `ModalCausalAxioms` (Section II substantive A3 in two clauses,
  + Section I definitional bridge A21):
  * `ax3_causeNecessitatesEffect` — first clause: cause at `w` →
    effect exists at `w`;
  * `ax3_noCauseNoEffect` — second clause: no cause at `w` → no
    effect at `w`. **This is not the contrapositive** of the
    first clause (which would be automatic in classical logic);
    it is a substantively distinct commitment ruling out
    spontaneously arising effects (Bennett 1984 §15);
  * `ax_cause_iff_necCauseAt` — bridge: `Cause c e` ↔
    `∀ w, causeAt c e w`.

**A13 demote (modal translation, full success)**: under A23
(PSRSelfCause class commitment) + A18 + A3-first-clause,
`prop_7_demote_via_PSR` delivers A13's full content. Mechanical
finding: A13 is **modally translatable** (unlike A12 which is
not), but A23 is not weaker than A13 — the demote is a
redescription, not a reduction. See `auxiliary_axioms.md` A23
for the philosophical analysis.

The placeholder `ax3_causationDeterminate : True` in
`Pars1Axioms` remains as legacy API marker; **do not appeal to it
in proofs**. A4ₛ-from-A3-substantive demote attempt (now
expressible thanks to A21) is deferred.

---

## GAP-8 — IsGod and Def. VI's two substantive clauses

Def. VI contains two **logically independent** content gaps, kept
separate here:

- **GAP-8a**: *cardinality* — God has *infinitely many* attributes.
- **GAP-8b**: *universality over substance attributes* — God has
  *every other substance's* attribute.

These are independent. (Cardinality without universality: God has
infinite attributes, but lacks some attribute owned by another
substance `s`; A12 then forces `s = God`, but the cardinality
question is orthogonal. Universality without cardinality: God has
every attribute any substance has, but the total may be finite —
e.g. a single-substance world has trivial universality but
cardinality 1.)

Different propositions consume different halves: Prop. XIV
(`prop_14_onlyGodIsSubstance`) requires GAP-8b only; Prop. XI's
*ontological* arguments require GAP-8a (the "infinitely many"
clause is what guarantees God is *the* maximal substance).

**Update (Theologia.lean session)**: Prop. XI as actually
mechanised (`prop_11_godNecessarilyExists`, `Theologia.lean`) does
**not** go through GAP-8a at all. It uses the direct Section III
commitment A27 (`TheologiaAxioms.ax_god_exists`, "Deus datur")
instead of aggregating A13 with a cardinality clause — see
`auxiliary_axioms.md` A27 and `coverage.md`'s Prop. XI row. GAP-8a
therefore remains open but is no longer on Prop. XI's critical
path; it would still matter for a *cardinality*-faithful
mechanisation of Def. VI (a substance with *infinitely many*
attributes) should that be pursued independently of A27.

### GAP-8a — Infinite-attribute cardinality

**Location**: `Ethica/Pars1/Definitions.lean`, `IsGod` (the
*infinitis attributis* clause is currently absent from the
predicate; only `∃ a` (existence of some attribute) is required).

**Issue**: Def. VI's *substantia constantem infinitis attributis*
("a substance consisting of *infinitely many* attributes") is a
cardinality claim that is unencoded. Will become load-bearing in
some readings of Prop. XI.

**Resolution path**: At the modal / categorical layer, introduce
either (a) Mathlib's `Set.Infinite` over the attributes of `g`, or
(b) a dedicated cardinality predicate.

**Status**: ✅ **closed** — the framework exists (Realitas session)
*and* is satisfied by an actual God in the Attributum layer
(Attributum session). It remains unsatisfiable-with-a-God in the
Pars I register, which `Bridge.lean` now explains rather than merely
records. See the two updates below, in order.

**Update (Attributum session)**: the consistency half is closed.
`Ethica/Attributum/Models/InfiniteAttribute.lean` exhibits a God
with infinitely many attributes — `inf_def6_recovered :
HasInfiniteAttrs deus`, and `inf_god_with_infinite_attributes`
packaging it with `IsGodAttr deus` — in a world carrying
`AttrAxioms` (A10′/A12′/A14′/A15′, the same axioms re-typed) and
`StatedAxioms` (Spinoza's own A1–A11). The theorem depends on no
axioms at all (`#print axioms`).

Def. VI's "*infinitis attributis*" clause is therefore not merely
stateable but **true of something**. What blocked it was never
Spinoza's commitments: it was the Prop. X scholium reading that puts
attributes in `Thing`. `Ethica/Attributum/Bridge.lean`'s
`legacy_def6_unsatisfiable` re-derives the Pars I impossibility by
instantiating `Attr := Thing`, isolating the typing choice as the
sole difference. See GAP-25's Update for the full module tree.

**Update (Realitas session)**: `Ethica/Pars1/Realitas.lean` closes
the missing-framework half directly: `hasAtLeastNAttributes s n`
(cardinality-free, via a `Fin n` injection) and
`HasInfiniteAttributes s` (`∀ n, hasAtLeastNAttributes s n`) make
Def. VI's "*infinitis attributis*" clause **stateable** for the
first time in this formalisation, with **no new axiom** and no
Mathlib dependency. What remains open is not formalisation but
**consistency**: `def6_infinitis_attributis_unsatisfiable` proves
`HasInfiniteAttributes g` is impossible for any God `g` in the
current `Pars1Axioms` register — a consequence of the
attribute-collapse theorem (`attribute_collapse`, from A8 + A10 +
A12 + A14 + A15, no new axiom), which forces every attribute of
every substance to equal God whenever a God exists
(`god_no_two_attributes` already rules out God having even *two*
distinct attributes). The godless side is witnessed consistent by
`Models/MultiAttribute.lean` (`multiAttribute_infinitude`, carrier
`Nat`) — attribute plurality/infinitude is satisfiable on the
**full** register, but only in the absence of a God-existence
commitment (A27). See `coverage.md`'s "Attribute-collapse result"
subsection and the new **GAP-25** (attribute typing / collapse
escape) for the three named ways this incompatibility could be
revised.

**Update (Consecutio session)**: Prop. XVI's "*infinita infinitis
modis*" clause is a second consumer of the same missing counting
framework — `prop_16_modesFollowFromGod` (`Consecutio.lean`)
mechanises only the **qualitative** content (every mode follows
from God), not the cardinality claim (*how many* things follow,
and in how many ways). No separate GAP is opened for it: the
prerequisite is identical to GAP-8a's, and any counting framework
adopted here should be checked against both Def. VI's "*infinitis
attributis*" and Prop. XVI's "*infinita infinitis modis*" uses.
(The framework `Realitas.lean` supplies for GAP-8a — `Fin n`-based
`hasAtLeastNAttributes`/`HasInfiniteAttributes` — is available for
this use too, unattempted here.)

### GAP-8b — Universality of God's attributes over other substances

**Location**:
- `Ethica/Pars1/Definitions.lean`, `IsGod` (no universal-attribute
  clause).
- `Ethica/Pars1/Propositions.lean`, `prop_14_onlyGodIsSubstance`
  second explicit hypothesis (`god_has_every_substance_attribute`).
  An earlier `private axiom` encoding of this clause has been
  withdrawn in favour of the A15 field.

**Issue**: For Prop. XIV's demonstration to go through, we need
"every attribute of any substance `s` is also an attribute of God".
This is *not* equivalent to GAP-8a's cardinality claim — see the
header note above for the independence argument. Spinoza's
*demonstratio* of Prop. XIV reads this clause off Def. VI implicitly
(if God has *every* attribute and `s` has some attribute `a`, then
God has `a`); Bennett 1984 §18 flags it as a substantive
metaphysical commitment in its own right.

**Resolution path**: Promote `skeleton_IsGod_has_attribute_of` to a
substantive clause of `IsGod`, or as a Section III axiom A15.

**Status**: ✅ closed via A15 promotion.
`ax_IsGod_has_attribute_of` is now a `Pars1Axioms` field;
`prop_14_onlyGodIsSubstance` consumes it directly.
`Models/TwoSubstance.lean` falsifies A15 and sits at
"Bennett-line non-Spinoza bench" status (no `Pars1Axioms`
instance). With A15 as a typeclass field, a kernel inconsistency
of the kind a `private axiom` encoding could introduce is
structurally impossible.

**Demote attempt (§δ-4)**: A15 demote is a **decomposition** into
A25 (plenitude) + A26 (god uniqueness), both Section III strength.
**Plenitude alone fails** to deliver A15. The kernel-level hard
fact is **a counter-model**: see
`Ethica/Pars1/Models/Counterexamples.lean` `A15CounterModel`, a
3-element `StatedAxioms` instance with two attribute-distinct
gods, satisfying plenitude (each god is its own attribute-
bearer) but falsifying A15 (g₁ does not have g₂'s extra
attribute). This is the **second mechanical irreducibility
result** in the project (after A12). Bennett 1984 §17 / §18's
reading that A15 is irreducible to PSR's existence-explanatory
commitments is mechanically confirmed.

A `: True := trivial` marker theorem
(`A15_NOT_demotable_from_plenitude_alone`) would prove nothing
about provability; like the analogous A12 marker, no such marker is
used — the counter-model carries the result instead.

---

## GAP-9 — Def. VII two-clause structure (`Free` / `Constrained`)

**Location**: `Ethica/Pars1/Definitions.lean`, `Free`, `Constrained`.

**Issue**: Def. VII has a two-clause structure: a free thing
(1) exists from the necessity of its own nature alone, and
(2) is determined to act by itself alone. The current `Free`
definition is a thin alias over the `freelyExistent` primitive,
capturing only the existence-clause; the action-clause needs the
agency / *conatus* machinery introduced in Pars II.

**Resolution path**: When Pars II is started, redefine `Free` as the
conjunction
```
Free x ↔ freelyExistent x ∧ selfDeterminedToAct x
```
and similarly for `Constrained` (the contrast term).

**Status**: ⏳ deferred. The current alias is honest about being
incomplete via the doc comment.

**Update (Theologia/Inherence session)**: this gap now also blocks
the action-clause fragments of two new theorems that mechanise only
the existence-clause reading of Def. VII: `prop_17_godIsFree`
(`Theologia.lean`, Prop. XVII) and `prop_26_modesDeterminedByGod`
(`Inherence.lean`, Prop. XXVI, partial). Both are honestly flagged
in their own docstrings and in `coverage.md`. Cross-referenced as
GAP-18 to avoid duplicating this entry.

---

## GAP-13 — Substance has at least one attribute

**Location**: `Ethica/Pars1/Propositions.lean`,
`prop_14_onlyGodIsSubstance` first explicit hypothesis
(`substance_has_attribute`); cross-referenced in
`auxiliary_axioms.md` Section III (A14-candidate). An earlier
`private axiom` encoding of this hypothesis has been withdrawn in
favour of the A14 field.

**Issue**: Spinoza's Defs. III + IV jointly *suggest* that every
substance has at least one attribute (Def. IV defines an attribute
*as* what the intellect perceives in a substance as constituting
its essence; one expects a substance therefore to have *something*
the intellect can so perceive). But the formal definitions
- `Substance s := inItself s ∧ perSeConceived s`
- `Attribute a s := Substance s ∧ intellectPerceivesAsEssence s a`
do not entail `∃ a, intellectPerceivesAsEssence s a`. An
"attribute-less substance" is a model of the current `Pars1Axioms`.

This was surfaced by the `prop_14_onlyGodIsSubstance` skeleton work:
writing the demonstration in the form Spinoza uses revealed the
implicit dependency.

**Reading**: Della Rocca 2008 ch. 2 takes this for granted under
PSR (any substance has *some* essence; intellect can perceive that
essence as an attribute). Bennett 1984 §17 treats it as an
independent commitment of Spinoza's metaphysics.

**Resolution path**: The clean form is to commit
```
ax_substance_has_attribute :
  ∀ s : Thing, Substance s → ∃ a, Attribute a s
```
as A14 in `Pars1Axioms`. Then `prop_14`'s
`skeleton_substance_has_some_attribute` is replaced by A14 directly.

**Alternative (modal layer / PSR)**: under Della Rocca 2008's
reading, every substance is intelligible (by PSR), and
intelligibility runs through attributes (Def. III + Def. IV). The
chain `Substance s → ∃ a, Attribute a s` then unpacks as
`Substance s → intelligible s → ∃ a, intelligibleVia s a → ∃ a,
Attribute a s`. Closing GAP-13 via this route requires (i)
committing PSR as a modal-layer axiom and (ii) bridging
`intelligibleVia` to `Attribute` constitutively. Both steps carry
their own commitment cost; this is a **relocation** of the
commitment, not its elimination.

"PSR + the substantive A6" is *not* a viable modal route: A6 (true
idea agrees with object) does not in fact bear on substance-attribute
existence.

**Status**: ✅ closed via A14 promotion.
`ax_substance_has_attribute` is now a `Pars1Axioms` field;
`prop_14_onlyGodIsSubstance` consumes it directly. No intermediate
explicit-hypothesis encoding remains. Bennett-honest scoping
recorded in `auxiliary_axioms.md` §III.

**Demote attempt (§δ-3)**: under A24 (`PSREssencePerception`
class commitment, `auxiliary_axioms.md` modal-layer Section III),
`prop_A14_demote_via_PSR` in `ModalForm.lean` proves A14's full
content from the essence-perception axiom. **Trivial
redescription**: A24 has identical shape to A14 with
`Attribute a s` unfolded to its non-trivial component
`intellectPerceivesAsEssence s a`. Equal commitment-strength —
demote is a relabelling, not a reduction. The genuine
universality clause that resists PSR is A15, not A14.

---

## GAP-12 — Modal-layer derivation of A13

**Location**: `Ethica/Pars1/Axioms.lean`, `ax_substance_involves_existence`
(A13); cross-referenced in `auxiliary_axioms.md` Section III.

**Issue**: A13 (substance involves existence) is committed as an
axiom in `Pars1Axioms` because Spinoza's *demonstratio* of Prop. VII
chains Prop. VI corollary's mode-extension with an unstated PSR
move. Both links carry gaps the commentary literature flags
(Bennett 1984; Della Rocca 2008; Garrett 1990). The follow-up
question: can A13 be **demoted** from an axiom to a theorem at
the modal layer?

**Resolution path candidates**:
- *Della Rocca / PSR route*: substantive PSR + the substantive A3
  of `Causation.lean` (currently a `True` placeholder, GAP-7) might
  jointly derive A13.
- *Strengthened-corollary route*: prove Prop. VI corollary's
  mode-extension via A4 + a conceptual-uniqueness bridge (itself a
  fresh commitment), then combine with PSR to derive A13.

**Status**: ⏳ deferred, with **Bennett-honest scoping** (same
discipline as GAP-11). The derivation is not guaranteed: the
commentary literature is divided on whether *any* such derivation
succeeds within Spinoza's stated commitments. Closing GAP-12 may
itself require a fresh axiom (PSR), in which case A13 stays in the
auxiliary register permanently — the commitment relocates rather
than dissolves.

---

## GAP-11 — Modal-layer derivation of A12

**Location**: `Ethica/Pars1/Axioms.lean`, `ax_substanceIdByAttribute`
(A12); cross-referenced in `auxiliary_axioms.md` Section III.

**Issue**: A12 (substance indiscernibility by attribute) is committed
as an axiom in `Pars1Axioms` because Spinoza's *demonstratio* of
Prop. V is widely judged to require additional commitment to go
through (Bennett 1984 §17; Garrett 1990; Della Rocca 2008 ch. 2).
The natural follow-up
question is: can A12 be **demoted** from an axiom to a theorem at a
later layer (e.g. modal S5 + PSR), thus eliminating the visible
metaphysical commitment?

**Resolution path candidates**:
- *Della Rocca route*: introduce PSR as a substantive axiom in the
  modal layer and derive A12 from PSR + Spinoza's stated A1–A7.
  This relocates rather than eliminates the commitment, but PSR is
  more general and may earn its keep across many propositions.
- *Substance plenitude route*: introduce a plenitude principle
  ("every consistent attribute belongs to some substance") and
  derive A12 by uniqueness arguments.
- *Garrett route*: strengthen Def. III to make attributes
  *individuating*, and derive A12 from the strengthened definition.

**Status**: 🟡 **partially closed; full closure refused**.

**Partial closure** (Della Rocca PSR route): under
`PSRSubstance` class commitment (A22 in `auxiliary_axioms.md`,
modal-layer Section III), `prop_5_demote_via_PSR_all_attributes`
in `ModalForm.lean` proves a *partial* form of A12 — substances
sharing **all** attributes are identical. PSR-substance-
distinguishability rules out indistinguishable substance pairs,
hence delivers the all-shared case.

**Full closure refused** (Bennett-line evidence): full A12
content (substances sharing **any** attribute are identical) is
**NOT** derivable from the stated register + PSR. The kernel-level
hard fact is **a counter-model**: see
`Ethica/Pars1/Models/Counterexamples.lean` `A12CounterModel`, a
4-element `StatedAxioms` + `PSRSubstance` instance (all four
elements substances) where two distinct substances share the
attribute `a_shared`, falsifying A12. If A12 were derivable from
the stated register + PSR, the derivation would yield `False` on
this model.

A `: True := trivial` marker theorem
(`A12_full_NOT_demotable_from_PSR_alone`) would be a Lean-as-rhetoric
trick proving nothing about provability; no such marker is used. The
counter-model carries the result with kernel-level evidence instead.

This is **the first mechanical evidence in the project for
Bennett's reading** that Spinoza's Prop. V exceeds what is
derivable from PSR + the stated axioms. The remaining content
of A12 stays a Section III commitment irreducible to Della
Rocca's PSR route.

**Test bench**: `Ethica/Pars1/Models/TwoSubstance.lean` exhibits
the model-side counterpart — a two-substance world with disjoint
attributes that satisfies the partial form of A12 (no shared
attribute = no force toward identity) without satisfying full
A12 (since the substances are distinct).

---

## GAP-10 — Spinoza-textual form of Prop. II (`prop_2_via_def3`)

**Location**: `Ethica/Pars1/Propositions.lean`, comment near
`prop_2_distinctSubstancesShareNothing`.

**Issue**: The current `prop_2_distinctSubstancesShareNothing` is
the Della-Rocca short form: with `sameNature` derived from
`Attribute`, the proposition reduces to a one-line analytic move
from the definition. Spinoza's actual demonstration runs through
**Def. III** (substances are *per se concipiur*, so the conception
of one does not involve the conception of another) and **A5**
(things with nothing in common are not intelligible through one
another). Spinoza's text is *not* the Della-Rocca route.

The doc-comment in `Propositions.lean` mentions a future
`prop_2_via_def3` that re-runs Spinoza's textual demonstration, but
no such theorem is registered anywhere — a dangling forward
reference.

**Resolution path**: Once a substantive form of A5 is available at
the Pars I level (currently it lives in `CausalAxioms`,
substance-restricted), prove
```
theorem prop_2_via_def3
    (x y : Thing) (hx : Substance x) (hy : Substance y)
    (hdiff : ∀ a, ¬ (Attribute a x ∧ Attribute a y))
    : ¬ intelligibleThrough x y
```
following Spinoza's actual chain: Def. III + A5 → no shared
intelligibility. This complements the Della-Rocca form; both
should hold simultaneously and the equivalence is itself a small
lemma worth recording.

**Status**: ✅ closed. `prop_2_via_def3` added to
`Ethica/Pars1/Causation.lean`, proving `¬ intelligibleThrough x y`
from disjoint attributes via A5ₛ. The two readings of Prop. II
(Della-Rocca via `sameNature` unfolding, and Spinoza-textual via
A5ₛ) now coexist; `prop_2_forms_equivalent` records the bridge
between them.

---

## GAP-14 — A14 demote attempt (modal layer)

**Location**: `Ethica/Pars1/ModalForm.lean` §δ-3,
`prop_A14_demote_via_PSR`.

**Issue**: A14 is structurally adjacent to A15 (both make
claims about substances and attributes) and easy to misclassify.
A14 is itself an existence claim (`∃ a, Attribute a s`), not a
universality clause. PSR-flavoured existence axioms demote it
cleanly.

**Resolution**: ✅ closed via A24 (`PSREssencePerception`),
trivial redescription. `prop_A14_demote_via_PSR` proves A14's
content from A24 in two lines. **A24 is logically equivalent to
A14** modulo unfolding `Attribute`. Equal commitment-strength —
the demote is a relabelling, not a reduction. The structural
distinction between A14 (existence) and A15 (universality) is
the mechanical reason the two have different demote outcomes
(see `auxiliary_axioms.md` A14 entry's structural-adjacency note).

---

## GAP-15 — A15 demote attempt (modal layer)

**Location**: `Ethica/Pars1/ModalForm.lean` §δ-4,
`prop_A15_demote_via_decomposition`.

**Issue**: A15 (`∀ g s a, IsGod g → Substance s → Attribute a s
→ Attribute a g`) is the universality clause across attributes
and is the genuinely PSR-resistant clause in the demote
taxonomy.

**Resolution**: 🟡 partial — A15 demotes only via decomposition
into A25 (plenitude) + A26 (god uniqueness), neither strictly
weaker than A15. **Plenitude alone fails**: the counter-model
`A15CounterModel` in `Ethica/Pars1/Models/Counterexamples.lean`
exhibits a 3-element `StatedAxioms` instance where plenitude
holds but A15 fails. This is the **second mechanical
irreducibility result** in the project (after A12), confirming
Bennett 1984 §17 / §18's reading.

**A26 strictly weaker than Prop. XIV**: A26 asserts only that any
two gods are identical, not
that every substance is a god. Prop. XIV requires both A26 and
A15's universality reach. Hence the A15 demote replaces one
universality with a different one, not a reduction.

---

## GAP-16 — Prop. XII/XIII epistemic wrapper (*"vere concipi"*)

**Location**: `Ethica/Pars1/Mereology.lean`,
`prop_12_substanceIndivisible`,
`prop_13_absolutelyInfiniteSubstanceIndivisible`.

**Issue**: Spinoza states Prop. XII *epistemically* — "*Nullum
substantiae attributum potest vere concipi ex quo sequatur
substantiam posse dividi*", no attribute can be **truly conceived**
from which it follows that substance can be divided — not directly
as a claim that substance is not divisible. The base layer has no
"truly conceiving" operator (that machinery belongs to Pars II's
theory of ideas), so the epistemic wrapper cannot yet be
mechanised. What is mechanised (`prop_12_substanceIndivisible`,
via A32 + A12) is the shared *ontological core* both XII and XIII's
demonstrationes actually turn on: no substance has a proper part.

**Resolution path**: Pars II's idea/conception machinery — once a
"truly conceived" (`vereConcipi` or similar) predicate exists, the
epistemic wrapper can be added as a further clause and the
ontological core re-used as its consequent.

**Status**: ⏳ open, deferred to Pars II.

---

## GAP-17 — Prop. XV second clause (*"nec concipi potest sine Deo"*)

**Location**: `Ethica/Pars1/Inherence.lean`, `prop_15_allInGod`.

**Issue**: Prop. XV's full statement has two clauses — the
ontological ("*Quicquid est, in Deo est*", whatever is, is in God)
and the epistemic ("*nihil sine Deo esse neque concipi potest*",
nothing can be, or be conceived, without God). Only the ontological
clause is mechanised (`prop_15_allInGod`, via A33 +
`prop_14_onlyGodIsSubstance` + `prop_4_partition`). The epistemic
half needs the same conception machinery GAP-16 is waiting on.

**Resolution path**: Pars II conception machinery — the same
prerequisite as GAP-16; the two gaps may close together once a
"conceived through" chain to God is formalised.

**Status**: ⏳ open, deferred to Pars II.

---

## GAP-18 — Prop. XVII / XXVI action-clause fragments

**Location**: `Ethica/Pars1/Theologia.lean`, `prop_17_godIsFree`;
`Ethica/Pars1/Inherence.lean`, `prop_26_modesDeterminedByGod`.

**Issue**: Both propositions carry an action-clause half that is
not mechanised. Prop. XVII: `prop_17_godIsFree` mechanises Cor.
II's *existence*-clause reading only ("*ex sola suae naturae
necessitate existit*"); the *action*-clause ("*ad agendum a se
solo determinatur*") is not captured. Prop. XXVI:
`prop_26_modesDeterminedByGod` mechanises that the mode is
`Constrained` and caused by God, but the "*ad aliquid operandum*"
self-determination clause (the statement's second half, and the
whole of Prop. XXVII) is not captured. Both fragments are the same
underlying gap as **GAP-9** (Def. VII's two-clause structure for
`Free`/`Constrained`) — this entry cross-references rather than
duplicates it.

**Resolution path**: identical to GAP-9's — Pars II's action /
*conatus* machinery, redefining `Free`/`Constrained` with a
`selfDeterminedToAct` conjunct. Closing GAP-9 closes this gap for
both propositions simultaneously.

**Status**: ⏳ open — see GAP-9 for the shared resolution path.

---

## GAP-19 — Consecution relation (*"ex necessitate divinae naturae sequi"*)

**Location**: blocks Props. XVI, XXI, XXII, XXIII (and
transitively XXVIII, XXXIII) in `docs/coverage.md`.

**Issue**: Spinoza's "follows from the necessity of the divine
nature" (Prop. XVI: "*Ex necessitate divinae naturae infinita
infinitis modis [...] sequi debent*") names a distinct relation —
*following from* an attribute's or God's nature — that nothing in
`Pars1Axioms`, `CausalAxioms`, `TheologiaAxioms`, `MereologyAxioms`,
or `InherenceAxioms` currently formalises. `InherenceAxioms`
mechanises *inherence* (`inheresIn`) and its causal reading (A34),
which is adjacent but not the same relation — Prop. XVIII (God as
immanent cause of what is *in* him) does not need consecution, but
Prop. XVI (what *follows from* his nature) does.

**Resolution path**: a planned `Consecutio.lean` introducing a
`sequiturEx`/consecution primitive (`Thing → Thing → Prop`, "x
follows from y's nature") plus the axioms connecting it to
`Attribute`/`IsGod`, sufficient to state and prove Props.
XVI/XXI/XXII/XXIII.

**Status**: ✅ closed via `Ethica/Pars1/Consecutio.lean`.
`ConsecutioWorld` (extending `InherenceWorld`) introduces two
primitives — `followsFrom` ("*ex necessitate naturae ejus
sequitur*") and `followsAbsolutely` (Prop. XXI's "*ex absoluta
natura*") — and `ConsecutioAxioms` (extending `InherenceAxioms`)
commits A37–A43 (catalogued in `auxiliary_axioms.md`: A39 Section
I; A37/A38 Section II; A40–A43 Section III 📜-pattern). Mechanised
on top: Props. XVI (partial — qualitative clause), XVI Cor. I, XX
(partial), XXI, XXII, XXV cor., XXVIII (+ derived corollary),
XXXVI. Consistency witnessed by `Models/ConsecutioWitness.lean`
(whole extended register A1–A15 + A27–A43 on one carrier).
**Residue split into precise successor gaps**: Prop. XXIII's
exhaustiveness premise (GAP-23), the ternary
attribute-relativisation (GAP-22), the eternity/sempiternity
conflation (GAP-21), and Prop. XVI's cardinality clause (GAP-8a
cross-reference). Prop. XXXIII's consecution dependency is
unblocked on this side but still needs the modal layer.

---

## GAP-20 — Horn (ii) of Prop. XII's dilemma (destruction/persistence)

**Location**: `Ethica/Pars1/Mereology.lean`, `MereologyAxioms`
(A32's docstring).

**Issue**: Spinoza's *demonstratio* of Prop. XII runs a two-horn
dilemma on a hypothesised division of substance: horn (i), the
parts *retain* the substance's nature (rival same-nature substances
— absurd per Prop. V); horn (ii), the parts do *not* retain that
nature, in which case the substance could lose its nature and
*cease to exist* (absurd per Prop. VII). A32 encodes only horn (i)
— the load-bearing horn for the actual contradiction, and the only
one expressible without further machinery. Horn (ii) needs a notion
of a substance ceasing to exist over time or across possibility
(destruction/persistence), which the base layer does not have; this
belongs with a modal / temporal extension, not the current base
layer.

**Resolution path**: at the modal layer, introduce a
persists-at-`w`/ceases-to-exist notion (extending
`ModalEthicaWorld`'s `existsAt`) and formalise horn (ii) as a
second disjunct of A32 (or a sibling axiom), then show the
disjunction is exhaustive and each horn independently yields
`False`.

**Status**: ⏳ open, deferred to the modal layer. A32 is honest
about covering horn (i) only via its own docstring and the
`coverage.md` Prop. XII/XIII row notes.

---

## GAP-21 — Eternity vs sempiternity conflation in A40/A41

**Location**: `Ethica/Pars1/Consecutio.lean`,
`ax_absoluteConsecution_eternalInfinite` (A40) and
`ax_infiniteModeTransfer` (A41).

**Issue**: Def. VIII defines eternity as existence "*quatenus ex
sola rei aeternae definitione necessario sequi concipitur*" —
**essence-grounded** eternity, the kind `prop_19_godIsEternal`
attributes to God via A28. Prop. XXI's "*aeterna*" for the
infinite modes is arguably a different modality: the infinite
modes "*semper … existere debuerunt*" — a **cause-derived
sempiternity** (always existing *through* the attribute they
follow from, "*per idem attributum aeterna*"), not existence
following from their own definition alone. Indeed A35 (Prop.
XXIV) explicitly *denies* that any mode's essence involves
existence — so an infinite mode's "eternity" cannot be Def.
VIII's essence-grounded kind on pain of tension with A35. A40 and
A41 nonetheless conclude with the single `Eternal` primitive Def.
VIII supplies, conflating the two senses — as Spinoza's own text
invites ("*per idem attributum aeterna*" glosses the distinction
over), but a mechanisation should keep the promissory note
visible.

**Reading**: the essence-eternity vs sempiternity distinction is
standard in the commentary on Def. VIII vs Props. XXI–XXIII (the
"duration without beginning or end" versus "atemporal necessity"
debate). The current single-primitive encoding takes no side; it
merely cannot yet *express* the difference.

**Resolution path**: the modal layer's world-relative existence
machinery (`ModalForm.lean`'s `existsAt`) can distinguish (a)
essence-grounded eternity — existence at every world following
from the thing's own nature (A18-style) — from (b) sempiternity
through a cause — existence at every world *inherited via*
`causeAt` from an eternal cause. Once both are expressible, A40/
A41's conclusions should be re-typed to the cause-derived sense
and the tension with A35 dissolved explicitly.

**Status**: ⏳ open, deferred to the modal layer.

---

## GAP-22 — Prop. XXII's ternary attribute-relativisation flattened

**Location**: `Ethica/Pars1/Consecutio.lean`,
`ax_infiniteModeTransfer` (A41), `prop_22_infiniteModeTransfer`.

**Issue**: Spinoza's Prop. XXII is genuinely **ternary**:
"*Quicquid ex aliquo Dei attributo, quatenus modificatum est tali
modificatione quae … sequitur*" — a thing follows from an
**attribute-as-modified-by-a-modification**, not simply from the
modification taken on its own. `ConsecutioWorld` has only the
binary `followsFrom : Thing → Thing → Prop`, so the
attribute-relativisation ("*ex aliquo Dei attributo quatenus
modificatum*") cannot be represented; A41 flattens the statement
to a binary transfer along `followsFrom` from the infinite mode
itself.

**Reading**: the "*quatenus*" construction is load-bearing in
Spinoza's causal metaphysics (it recurs in Prop. XXVIII's
"*quatenus modificatum est modificatione quae finita est*" and
throughout Pars II); flattening it is a genuine loss of logical
form, not just of idiom.

**Resolution path**: introduce a **ternary consecution relation**
— `followsFromQua : Thing → Thing → Thing → Prop` ("x follows
from attribute a insofar as a is modified by m") — when a
consumer needs it, with A39-style bridges projecting the ternary
form onto the binary `followsFrom`. The same ternary relation is
the prerequisite for Prop. XXIII's trichotomy (GAP-23) and for a
form-faithful Prop. XXVIII; introduce it once, for all three.

**Status**: ⏳ open — deferred until a consumer requires the
ternary form.

---

## GAP-23 — Prop. XXIII as classification/exhaustiveness premise

**Location**: `Ethica/Pars1/Consecutio.lean`,
`ax_finiteMode_causedByFiniteMode` (A42's docstring); coverage
row XXIII.

**Issue**: Prop. XXIII ("every mode which exists necessarily and
as infinite must follow either from the absolute nature of an
attribute or from an attribute modified by an infinite
modification") functions in Spinoza's architecture as a
**classification/exhaustiveness premise**: every mode follows
either absolutely, or via an infinite modification, or via a
finite one. Prop. XXVIII's *demonstratio* consumes this
trichotomy **silently** — it rules out the first two horns (via
Props. XXI/XXII) to land finite modes on the third. The
formalisation does not commit the trichotomy: A42 commits Prop.
XXVIII's *conclusion* directly instead (the honest minimal form —
see A42's entry in `auxiliary_axioms.md`), leaving Prop. XXIII
itself unmechanised and the exhaustiveness reasoning unavailable.

**Reading**: the trichotomy is where Spinoza's taxonomy of modes
(immediate infinite / mediate infinite / finite) lives; it is
also, notoriously, where the *Ethica* leans on the letters (Ep.
64's examples of the infinite modes) for content the text itself
underspecifies.

**Resolution path**: (i) the ternary consecution relation of
GAP-22, so "follows from an attribute *quatenus modificatum*"
is expressible at all; (ii) an explicit Section III
**classification commitment** asserting the trichotomy's
exhaustiveness (every mode follows absolutely, via an infinite
modification, or via a finite modification). With both, Prop.
XXIII becomes statable and Prop. XXVIII re-derivable from
XXI + XXII + the trichotomy — at which point A42 could be demoted
to a theorem (the usual demote-experiment discipline applies:
the classification commitment may well be no weaker than A42).

**Status**: 🟡 **premise half CLOSED; residual half open.**

**Update (Classificatio session)**: resolution path (ii) is done —
`Ethica/Pars1/Classificatio.lean` commits the trichotomy's
exhaustiveness directly as **A44** (`ClassificatioAxioms.
ax_consecution_trichotomy`), without needing the ternary relation
of (i): the binary `followsFrom`/`followsAbsolutely` primitives
already available suffice to state the three horns generally
(quantified over *every* mode, not just necessarily-infinite ones).
`prop_23_partial_classification` mechanises this general trichotomy
— the premise Prop. XXVIII's *demonstratio* silently consumed —
closing GAP-23's premise half. As the resolution path predicted,
A42 is now demotable: `A42_demote_via_trichotomy` proves A42's
full content from Σ = {A38, A40, A41, A44}, an **equal-strength
decomposition** (the classification commitment is exactly as
strong as A42, no weaker) — see `auxiliary_axioms.md`'s A42/A44
entries and README's demote table.

**Residual half, unchanged and still open**: A44 (and hence
`prop_23_partial_classification`) commits the trichotomy generally,
for every mode — it does **not** additionally exclude the finite
branch specifically for modes that are themselves
necessarily-and-infinite, which is Prop. XXIII's actual conclusion
(a disjunction of exactly *two* horns for that restricted class of
modes). That exclusion needs a **finite-source transfer principle**
— "what follows from a finite mode is itself finite" — which
nothing in this formalisation commits to; without it, nothing rules
out a necessarily-infinite mode following from a finite one. This
residue is intentionally *not* split into a separate GAP number: it
is exactly GAP-23's original content, now sharpened by A44's
closure of the premise half. Resolution path for the residue is
unchanged from (i) above — the ternary consecution relation of
GAP-22 is likely the natural home for a form-faithful finite-source
transfer principle as well, since Prop. XXVIII's own "*quatenus
modificatum est modificatione quae finita est*" is itself a
ternary construction.

---

## GAP-24 — Essence-as-object machinery (Prop. XX's identity; Prop. XXV proper)

**Location**: `Ethica/Pars1/Consecutio.lean`,
`prop_20_partial_attributesExpressBoth` (Prop. XX partial),
`prop_25_cor_everythingGodOrMode` (corollary only).

**Issue**: two propositions of the consecution arc make claims
*about essences as objects*, which the current layer cannot
express — every essence-flavoured notion in `EthicaWorld` is a
predicate (`involvesExistence`, `expressesEternalEssence`,
`intellectPerceivesAsEssence`), never a *term* denoting an
essence:

- **Prop. XX** ("*Dei existentia ejusque essentia unum et idem
  sunt*") asserts an **identity** — God's essence and God's
  existence are *the same thing*. What is mechanised
  (`prop_20_partial_attributesExpressBoth`) is the conjunctive
  content the *demonstratio* assembles (each attribute expresses
  both essence and existence); the identity conclusion needs
  "God's essence" and "God's existence" as terms that can flank
  `=`.
- **Prop. XXV proper** ("*Deus est causa efficiens rerum
  existentiae sed etiam essentiae*") asserts God **causes the
  essences** of things — `Cause` would need an essence-term as
  its second argument. Only the corollary (provable from Prop. XV
  + Def. V without essence-causation) is mechanised.

**Reading**: essence-as-object is exactly what Pars II's "*ideae
rerum singularium*" machinery trades in (ideas of essences,
formal vs objective essence); it is also adjacent to the
conception machinery GAP-16/GAP-17 await — the "truly conceived"
operator and the essence-term machinery will likely arrive
together with Pars II's theory of ideas.

**Resolution path**: introduce an essence-assignment (e.g.
`essenceOf : Thing → Essence` or a reified `Essence`-sorted
domain) at the Pars II layer; restate Prop. XX as
`essenceOf g = existenceOf g` (or the appropriate identification)
and Prop. XXV proper as `Cause g (essenceOf x)`. Cross-reference:
GAP-16/GAP-17 (Pars II conception machinery — likely the same
delivery vehicle); GAP-21 (the eternity senses also become
disentanglable once essences are objects).

**Status**: ⏳ open, deferred to Pars II.

---

## GAP-25 — Attribute typing / collapse escape

**Location**: `Ethica/Pars1/Realitas.lean`, `/-! ## The
attribute-collapse theorem -/` section (`attribute_collapse`,
`attribute_is_substance`, `god_no_two_attributes`,
`def6_infinitis_attributis_unsatisfiable`); cross-referenced from
GAP-8a and from `coverage.md`'s "Attribute-collapse result"
subsection.

**Issue**: `Realitas.lean` proves, from five already-committed
pieces of the register (attributes typed as `Thing`; A10
`ax_attribute_perSe`; A8 `ax_inItself_iff_perSeConceived`; A14
`ax_substance_has_attribute`; A15 `ax_IsGod_has_attribute_of`), that
**any** `Pars1Axioms` world containing a God collapses every
attribute of every substance onto that God
(`attribute_collapse`). Consequences: God cannot have even two
distinct attributes (`god_no_two_attributes`), and Def. VI's
"*constantem infinitis attributis*" clause is therefore
**unsatisfiable**, not merely unformalised, in any model with a God
(`def6_infinitis_attributis_unsatisfiable`). `Models/
MultiAttribute.lean` confirms the incompatibility is sharp: the
full register tolerates infinite attribute plurality, but only in
GODLESS models (`multiAttribute_hasNoGod`). No current axiom
revision is proposed — this GAP catalogues the escape routes
without endorsing one, since each is a genuine revision of a
Section I/III commitment, not a bug fix.

**Escape routes** (named in `Realitas.lean`'s header; each blocks a
different step of the five-step collapse chain):

1. **Restrict A12** (`ax_substanceIdByAttribute`) to non-attribute
   substances. Blocks the final identification step
   (`attribute_collapse`'s last line, where A12 identifies the
   attribute-of-an-attribute-bearing substance with God). Cost: A12
   currently earns its keep across 7 propositions (`coverage.md`'s
   Section III utilization table); a restricted form would need to
   be re-verified against every one of them, and the restriction
   itself needs principled grounds for distinguishing
   "attribute-typed" substances from ordinary ones within a single
   `Thing` universe.
2. **Weaken A10 and/or A8's bite specifically on attributes**
   (Bennett's own line, Bennett 1984 §16 — declining exactly the A8
   coextension when the subject is an attribute). Blocks step 3 of
   the chain, `attribute_is_substance` (an attribute of a substance
   is itself a substance). Cost: A8/A10 are both load-bearing
   elsewhere (A8 for `prop_4_partition`'s substance/mode partition;
   A10 for `prop_10_attributePerSe`) — any restriction must not
   disturb those uses.
3. **Type attributes off the `Thing` universe entirely**, giving
   them their own type distinct from substances/modes. Blocks step
   1 at the ground floor — `Attribute a s` currently has `a :
   Thing`, the same universe as substances and modes; a genuinely
   separate `Attributum` type would make `attribute_is_substance`
   inexpressible, not merely false. Cost: the largest of the three
   — every axiom and theorem mentioning `Attribute` (A8, A10, A12,
   A14, A15, and every proposition built on them) would need
   re-typing, and the "one universe of things" simplicity the base
   layer currently enjoys would be lost.

**Reading**: the collapse also formally validates (and then
falsifies the joint tenability of) the Ep. 9 (to de Vries) identity
reading of substance and attribute — "one and the same thing, ...
only distinguished in respect of the different names by which it is
called" — showing the register cannot simultaneously hold that
identity reading AND attribute plurality once a God exists. Framed
via the Wolfson (attributes as intellect-relative appearances) vs.
Gueroult (attributes as objective aspects of substance)
subjective/objective controversy, the collapse turns what is
usually treated as a standing interpretive option into a forced
choice: whichever side one takes, a Spinozistic God with more than
one attribute is not a model of `Pars1Axioms`.

**Resolution path**: a future `Attributum.lean` redesign committing
to one of the three escape routes above (most plausibly route 3, a
modal-layer or dedicated-type treatment of attributes, given routes
1–2's collateral cost to already-load-bearing axioms), or an
explicit acceptance of the collapse as correct Spinoza exegesis
(some readings of Ep. 9 might welcome it). No route is adopted in
this formalisation; the escape routes are catalogued, not chosen.

**Update (Attributum session)**: route 3 is now **adopted and
implemented**, as a *parallel branch* rather than as an in-place
edit. New module tree `Ethica/Attributum/`:

- `Core.lean` — `AttrStructure Attr` (the intrinsic structure of the
  attribute universe, parameterised by `Attr` alone) and `AttrWorld
  Thing Attr extends EthicaWorld Thing, AttrStructure Attr`, whose
  attribution relation is `perceivedAsEssence : Thing → Attr → Prop`.
  `Attributum a s` has `a : Attr`, so `Substance a` does not
  typecheck and `attribute_is_substance` — step 3 of the collapse
  chain — is **inexpressible**, not merely false. Prop. X survives
  via the attribute-side predicate `perSeConceivedAttr`; what is
  withdrawn is only A8's *bite on attributes*, exactly Bennett 1984
  §16's position, now enforced by typing rather than by an axiom
  restriction.
- `Axioms.lean` — `AttrAxioms` carrying A10′/A12′/A14′/A15′, the
  four attribute-mentioning axioms re-typed verbatim. Section
  classification unchanged (A10′ Section I; A12′/A14′/A15′ Section
  III). No A8′ exists or can exist. Props. V, IX and X are
  re-derived in the new vocabulary.
- `Models/DualAttribute.lean` — a God with **two** distinct
  attributes (`cogitatio`, `extensio`), satisfying `AttrAxioms` and
  `StatedAxioms` together (`dual_god_with_two_attributes`). Depends
  on no axioms whatever (`#print axioms`).
- `Models/InfiniteAttribute.lean` — a God with **infinitely many**
  attributes (`inf_def6_recovered`), i.e. Def. VI satisfied outright.
- `Bridge.lean` — the diagnosis. `legacyAttrWorld` instantiates
  `Attr := Thing`; under it `Attributum`/`IsGodAttr`/
  `hasAtLeastNAttrs`/`HasInfiniteAttrs` are *definitionally* their
  Pars I counterparts (four `Iff.rfl` lemmas), and
  `legacy_collapse` / `legacy_god_no_two_attributes` /
  `legacy_def6_unsatisfiable` transport Pars I's impossibility
  results into the new vocabulary.

The pair (`dual_god_two_attributes`, `legacy_god_no_two_attributes`)
is the mechanical content of the closure: the *same* sentence, under
the *same* axioms, is satisfiable when `Attr` is separate and
refutable when `Attr := Thing`. The collapse is therefore an
artefact of the Prop. X scholium's identification of attributes with
things, not a consequence of Spinoza's substantive commitments.

**Nothing under `Ethica/Pars1/` is modified.** The v1.0.0 register
and the published irreducibility results (arXiv:2605.02331) are
untouched by construction, per the freeze decision recorded in
`README.md`. The collapse remains true of Pars I — that is now a
statement about Pars I's typing choice, which `Bridge.lean` makes
precise.

**Status**: ✅ closed by parallel branch (Attributum session). The
route is chosen, implemented and witnessed on both sides. Residue,
tracked here rather than in a new gap: the Attributum layer does not
yet re-type the *extension* classes (A29's `Attribute a s → involves
Existence a`, A40's and A44's attribute quantifiers in
`Consecutio.lean` / `Classificatio.lean`); those are re-typed as
Pars II consumes them. Cross-reference: GAP-8a.

---

## GAP-26 — Prop. II.III's *in Deo* localisation

**Location**: `Ethica/Pars2/Idea.lean`, A49
(`ax_god_has_idea_of_all`) and `prop_2_3_ideaOmnium`.

**Issue**: Prop. II.III asserts that in God there necessarily *is*
an idea of his essence and of everything following from it — "*In
**Deo** datur necessario idea*" — and the *demonstratio* closes with
"*et (per propositionem 15 partis I) non nisi in Deo*". What is
mechanised is only the existential clause (`∀ x, ∃ i, ideaOf i x`).
The localisation of ideas *in God* is not stated.

**Resolution path**: strengthen A49 to `∀ x, ∃ i, ideaOf i x ∧
inheresIn i g`, which requires importing the Inherence layer
(`InherenceWorld`/`InherenceAxioms`) into `Pars2World`. Deferred
because that layer is a sibling branch of `CausalWorld` and pulling
it in raises the same synthesization-order question the `outParam`
solves for `CausalWorld` — worth doing once, when batch 1.3
(`Pars2/Corpus.lean`) needs inherence anyway. `prop_15_allInGod`
would then supply the localisation directly.

**Status**: ⏳ open, deferred to batch 1.3.

---

## GAP-27 — Prop. II.VII's identity reading (*idem est*)

**Location**: `Ethica/Pars2/Idea.lean`, `prop_2_7_ordoEtConnexio`.

**Issue**: Prop. VII says the order and connection of ideas *is the
same as* ("*idem est ac*") the order and connection of things. What
is mechanised is the directional transfer — `Cause c e` yields
`Cause ic ie` for the corresponding ideas — which is what the
*demonstratio* ("*Patet ex axiomate 4 partis I*") actually
establishes. Two things are not mechanised:

(a) the **converse** direction (causal order among ideas transfers
    back to things);
(b) the **identity** claim proper. The scholium is emphatic and much
    stronger than parallelism: "*modus extensionis et idea illius
    modi una eademque est res sed duobus modis expressa*" — a mode
    of extension and its idea are *one and the same thing* expressed
    two ways, and "*substantia cogitans et substantia extensa una
    eademque est substantia*".

**Reading**: (b) is the *identity* interpretation of the parallelism
(Della Rocca 1996 ch. 6, against the weaker
correspondence/isomorphism readings). Adopting it commits the
formalisation to cross-attribute identity of modes, which interacts
directly with the *quatenus* machinery: the same mode is "under"
two attributes at once.

**Resolution path**: batch 1.2's `causeUnder : Thing → Thing → Attr
→ Prop` gives the *quatenus* relativisation; the identity claim then
needs a further commitment relating a mode's being-under-cogitatio
to its being-under-extensio. Not attempted in batch 1.1.
Cross-reference: GAP-22 (the same ternary-relativisation
prerequisite, flagged there for Prop. I.XXII).

**Status**: ⏳ open, deferred to batch 1.2.

---

## Closure protocol

Each gap closure must:

1. Replace the `sorry` (or empty stub) with a real proof.
2. Update this register: cross out the gap heading or set the
   status to ✅, append the resolution commit hash.
3. If the resolution required a new auxiliary axiom, add it to
   `docs/auxiliary_axioms.md` with full philosophical justification.
4. Update `docs/coverage.md` if the closure changes the status of
   any proposition or definition.

No silent removals. No `set_option pp.all false` to hide breakage.
**No `axiom` declarations of any kind** (public or `private`) for
forward-reference content — use explicit theorem hypotheses or
typeclass fields. The `private axiom` pattern is avoided because it
produces kernel-level inconsistency in conjunction with
counter-witness models. Public `axiom` is strictly worse (globally
trusted *and* publicly named); the rule covers both.

### 5. Hypothesis-premise discipline

When a `prop_N` proof requires a future Section III commitment
whose content is **not yet committed** in `Pars1Axioms` /
`CausalAxioms`, the missing premise is encoded as an **explicit
hypothesis** of `prop_N`, not as a `private axiom`.

Rationale (kernel-level inconsistency averted): Lean 4's `private`
modifier restricts *name resolution*,
but a `private axiom` is still a polymorphic global axiom that
the kernel trusts for **every** `Thing` instance simultaneously,
*including* counter-witness models (e.g. `TwoSubst`). Combining a
polymorphic skeleton axiom with a counter-witness theorem
(specialising the same proposition to a concrete type and proving
its negation) renders the kernel environment inconsistent. An
explicit theorem hypothesis is supplied at each call site and is
automatically blocked on models that falsify it — exactly the
behaviour Bennett-style multi-substance models require.

**Concrete rule**: never introduce **any** `axiom` declaration
(public or `private`) whose content is a forward reference to an
unproved Section III commitment. Use explicit theorem hypotheses
or wait until the commitment is promoted to a typeclass field.

A plain `axiom` is even worse than `private axiom` — both are
kernel-trusted polymorphic, but `private axiom` is at least
*file-scope-restricted in name*; a plain `axiom` is both
globally trusted *and* publicly named. The rule singles out
`private axiom` because that is the concrete misuse a soundness
incident can exhibit; the underlying rule is broader. Project-wide:
`grep -rE "^axiom|^private axiom" Ethica/` should return empty.

Counter-witness models remain valuable: a model that *falsifies* an
A*-candidate (proved as a theorem in the model file) documents the
philosophical content of the candidate by exhibiting where
Bennett-line readings legitimately diverge.

### 6. Hypothesis-to-axiom promotion

When the explicit hypothesis is finally committed as a `Pars1Axioms`
(or `CausalAxioms`) field — i.e. `A*-candidate` becomes `A*` —
the closure must:

(a) Add the field to the typeclass with full doc-comment
    referencing the gap and Section III status.
(b) Replace each explicit-hypothesis occurrence in `prop_N`'s
    signature with `Pars1Axioms.ax_*` calls in the body, removing
    the corresponding parameters.
(c) Move the candidate entry in `auxiliary_axioms.md` from
    "*-candidate" to its full numbered slot (e.g. `A14-candidate`
    → `A14`) with full Bennett-honest disclaimer.
(d) Add the typeclass field discharge in every existing model
    file. For counter-witness models, promotion of the skeleton
    means the model can no longer instantiate the axiom set —
    flag this explicitly: the model must either be migrated to a
    weaker typeclass (if one exists) or marked as a non-Spinoza
    "Bennett-line" model with the failure documented.
