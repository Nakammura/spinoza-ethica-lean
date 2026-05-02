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

**Status**: ✅ closed (commit `31115fd`). `Pars1Axioms.ax1_exclusive`
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

**Status**: ✅ closed via path (b) (commit `f2b94f8`). `sameNature`
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
  - ✅ initial closure (commit `2ab8039`). `CausalWorld` extending
    `EthicaWorld` with `Cause` and `intelligibleThrough`; A4 and A5
    substantive in `CausalAxioms`. `prop_3_noCommonNoCause` proved
    by contraposition via A4 + A5; symmetric corollary provided.
  - 🔧 soundness patch (commit `935e530`). Triggered by review of
    2026-05-02 §3.1: with `sameNature` derived from `Attribute`
    (GAP-2 path b, hence implicitly substance-only), the original
    fully-general A5 forced `¬ Cause m₁ m₂` for every pair of
    modes — wiping out the finite-mode causation Pars II–V depend
    on. Fix:
    - A5 substantive restricted to substances:
      `∀ x y, Substance x → Substance y → ¬ sameNature x y → ¬ intelligibleThrough x y`.
    - `prop_3_noCommonNoCause` and its symmetric corollary now
      require `Substance x` and `Substance y` hypotheses.
    - `CausalAxioms extends Pars1Axioms` so downstream theorems
      consume one typeclass.
    - Removed the pre-review duplicate
      `ax3_causeGroundsIntelligibility` (literally the same Lean
      signature as A4); A3's distinct ontological-necessitation
      content opened as GAP-7.
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

**Status**: ✅ closed (commit `02b435c`). Both axioms (A8, A9)
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

The pre-review draft of `CausalAxioms` carried two fields,
`ax3_causeGroundsIntelligibility` and
`ax4_effectIntelligibleThroughCause`, with **literally identical**
Lean signatures. They have been collapsed into A4 only; A3's
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

The pre-review of 2026-05-02 §A.1 conflated two **logically
independent** content gaps in Def. VI. They are now split:

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

**Status**: ⏳ deferred.

### GAP-8b — Universality of God's attributes over other substances

**Location**:
- `Ethica/Pars1/Definitions.lean`, `IsGod` (no universal-attribute
  clause).
- `Ethica/Pars1/Propositions.lean`, `prop_14_onlyGodIsSubstance`
  second explicit hypothesis (`god_has_every_substance_attribute`).
  The pre-soundness-fix encoding used a `private axiom`; that has
  been withdrawn — review of 2026-05-02 §A.

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

**Status**: ✅ closed via A15 promotion (post-review of 2026-05-02
§F.α). `ax_IsGod_has_attribute_of` is now a `Pars1Axioms` field;
`prop_14_onlyGodIsSubstance` consumes it directly.
`Models/TwoSubstance.lean` falsifies A15 and was migrated to
"Bennett-line non-Spinoza bench" status (no `Pars1Axioms`
instance) per closure-protocol step 6(d). The kernel-inconsistency
risk that the pre-soundness-fix `private axiom` encoding produced
is now structurally impossible.

**Demote attempt (§δ-4)**: A15 demote is a **decomposition** into
A25 (plenitude) + A26 (god uniqueness), both Section III strength.
**Plenitude alone fails** to deliver A15. The kernel-level hard
fact is **a counter-model**: see
`Ethica/Pars1/Models/Counterexamples.lean` `A15CounterModel`, a
3-element `EthicaWorld` instance with two attribute-distinct
gods, satisfying plenitude (each god is its own attribute-
bearer) but falsifying A15 (g₁ does not have g₂'s extra
attribute). This is the **second mechanical irreducibility
result** in the project (after A12). Bennett 1984 §17 / §18's
reading that A15 is irreducible to PSR's existence-explanatory
commitments is mechanically confirmed.

The previous draft used a `: True := trivial` marker theorem
(`A15_NOT_demotable_from_plenitude_alone`) — retired in the same
review pass that retired the A12 marker (review of 2026-05-03
§A.6).

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

---

## GAP-13 — Substance has at least one attribute

**Location**: `Ethica/Pars1/Propositions.lean`,
`prop_14_onlyGodIsSubstance` first explicit hypothesis
(`substance_has_attribute`); cross-referenced in
`auxiliary_axioms.md` Section III (A14-candidate). The pre-soundness-
fix encoding used a `private axiom`; that has been withdrawn —
review of 2026-05-02 §A.

**Issue**: Spinoza's Defs. III + IV jointly *suggest* that every
substance has at least one attribute (Def. IV defines an attribute
*as* what the intellect perceives in a substance as constituting
its essence; one expects a substance therefore to have *something*
the intellect can so perceive). But the formal definitions
- `Substance s := inItself s ∧ perSeConceived s`
- `Attribute a s := Substance s ∧ intellectPerceivesAsEssence s a`
do not entail `∃ a, intellectPerceivesAsEssence s a`. An
"attribute-less substance" is a model of the current `Pars1Axioms`.

This was surfaced by the `prop_14_onlyGodIsSubstance` skeleton work
(review of 2026-05-02 §A.2): writing the demonstration in the
form Spinoza uses revealed the implicit dependency.

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

The pre-review draft proposed "PSR + the substantive A6" as the
modal route, but A6 (true idea agrees with object) does not in
fact bear on substance-attribute existence — that mistake has
been corrected here.

**Status**: ✅ closed via A14 promotion (post-review of 2026-05-02
§F.α). `ax_substance_has_attribute` is now a `Pars1Axioms` field;
`prop_14_onlyGodIsSubstance` consumes it directly. The intermediate
explicit-hypothesis encoding (post-review §A) is removed. Bennett-
honest scoping recorded in `auxiliary_axioms.md` §III.

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
**NOT** derivable from PSR + base axioms. The kernel-level hard
fact is **a counter-model**: see
`Ethica/Pars1/Models/Counterexamples.lean` `A12CounterModel`, a
4-element `EthicaWorld` + `PSRSubstance` instance where two
distinct substances share the attribute `a_shared`, falsifying
A12. If A12 were derivable from PSR + base, the derivation
would yield `False` on this model.

The previous draft used a `: True := trivial` marker theorem
(`A12_full_NOT_demotable_from_PSR_alone`) — a Lean-as-rhetoric
trick that has been retired (review of 2026-05-03 §A.2). The
counter-model replaces it with kernel-level evidence.

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
exhibits a 3-element `EthicaWorld` instance where plenitude
holds but A15 fails. This is the **second mechanical
irreducibility result** in the project (after A12), confirming
Bennett 1984 §17 / §18's reading.

**A26 strictly weaker than Prop. XIV** (review of 2026-05-03
§A.5): A26 asserts only that any two gods are identical, not
that every substance is a god. Prop. XIV requires both A26 and
A15's universality reach. Hence the A15 demote replaces one
universality with a different one, not a reduction.

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
typeclass fields. Review of 2026-05-02 §A: the `private axiom`
pattern was withdrawn after it produced kernel-level inconsistency
in conjunction with counter-witness models. Public `axiom` is
strictly worse (globally trusted *and* publicly named); the rule
covers both.

### 5. Hypothesis-premise discipline

When a `prop_N` proof requires a future Section III commitment
whose content is **not yet committed** in `Pars1Axioms` /
`CausalAxioms`, the missing premise is encoded as an **explicit
hypothesis** of `prop_N`, not as a `private axiom`.

Rationale (review of 2026-05-02 §A — kernel-level inconsistency
averted): Lean 4's `private` modifier restricts *name resolution*,
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
globally trusted *and* publicly named. The earlier codification
(review of 2026-05-02 §A) singled out `private axiom` because
that was the concrete misuse the soundness incident exhibited;
the underlying rule is broader. Project-wide:
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
