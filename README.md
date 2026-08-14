# Spinoza's *Ethica* in Lean 4

[![arXiv](https://img.shields.io/badge/arXiv-2605.02331-b31b1b.svg)](https://arxiv.org/abs/2605.02331)
[![DOI](https://zenodo.org/badge/1227587615.svg)](https://doi.org/10.5281/zenodo.20111520)

> Pars I (De Deo) is mechanised through the load-bearing
> propositions of the substance / attribute / God arc
> (Propositions II, IV, V, VI, VII, X, XIV) and re-derived in a
> modal-S5 layer. Two kernel-level irreducibility results
> establish that axioms A12 (Proposition V's
> identity-from-shared-attribute clause) and A15 (Proposition
> XIV's universality clause) cannot be derived from stated
> axioms plus a Della-Rocca-flavoured PSR augmentation. Per-
> proposition status is tracked in `docs/coverage.md`.
>
> Project lead: Yuki Nakamura.

## What this is

A formal-verification port of Baruch Spinoza's *Ethica Ordine
Geometrico Demonstrata* (1677) into the Lean 4 theorem prover.

Spinoza wrote the *Ethica* "more geometrico" — in the form of
Euclid's *Elements*, with definitions, axioms, propositions, and
demonstrations. He intended his metaphysics to be checked the way
a geometer checks a construction. This repository executes that
intention against a modern dependent-type-theory kernel.

## Texts

Public-domain sources only:

- *Latin*: Spinoza, *Ethica*, from the cltk public-domain corpus.
- *English*: R. H. M. Elwes 1883 translation, via Project
  Gutenberg / en.wikisource.

The Curley 1985 Princeton translation is consulted as
interpretive cross-check; no Curley text is reproduced in source
or comments.

## Organisation

```
Ethica.lean                                -- Top-level umbrella
Ethica/
└── Pars1/
    ├── Definitions.lean                  -- Defs I–VIII + EthicaWorld class
    ├── Axioms.lean                       -- A1–A7 + auxiliary axioms (Section I/II/III)
    ├── Causation.lean                    -- Cause predicate, A3 / A4 substantive
    ├── Propositions.lean                 -- Props I–XIV with full proofs
    ├── ModalForm.lean                    -- S5 modal re-derivation
    ├── Theologia.lean                    -- Props XI, XVII, XIX; A27–A31 (TheologiaAxioms)
    ├── Mereology.lean                    -- Props XII, XIII; A32 (MereologyAxioms)
    ├── Inherence.lean                    -- Props XV, XVIII, XXIV, XXVI, XXIX; A33–A36 (InherenceAxioms)
    ├── Consecutio.lean                   -- Props XVI, XX (partial), XXI, XXII, XXV cor., XXVIII, XXXVI; A37–A43 (ConsecutioAxioms)
    ├── Realitas.lean                     -- Prop IX; counting framework (GAP-8a); the attribute-collapse theorem
    ├── Classificatio.lean                -- Prop XXIII (partial); A44 (ClassificatioAxioms); A42 demote experiment
    └── Models/
        ├── SingleSubstance.lean          -- Unit-instance consistency witness
        ├── TwoSubstance.lean             -- Bennett-line falsifier bench
        ├── MultiWorld.lean               -- Bridge-axiom witness (modal layer)
        ├── Counterexamples.lean          -- Kernel-level non-derivation witnesses
        ├── NoGod.lean                    -- A27 irreducibility witness (falsifies A27 under full Pars1Axioms)
        ├── CounterexamplesII.lean        -- A32/A35 irreducibility witnesses (ModeParts, NecessaryMode)
        ├── GodWorld.lean                 -- TheologiaAxioms consistency witness
        ├── MereologyWitness.lean         -- MereologyAxioms consistency witness
        ├── InherenceWitness.lean         -- InherenceAxioms consistency witness
        ├── ConsecutioWitness.lean        -- Full-register (A1–A15 + A27–A43) consistency witness
        ├── MultiAttribute.lean           -- Godless infinite-attribute-plurality witness (Nat carrier)
        └── ClassificatioWitness.lean     -- A44 (+ A42-demote register Σ) consistency witness
└── Attributum/                           -- Re-typed attribute layer (GAP-25 / GAP-8a); parallel branch
    ├── Core.lean                         -- AttrStructure, AttrWorld, Attributum, IsGodAttr, counting framework
    ├── Axioms.lean                       -- A10′/A12′/A14′/A15′ (AttrAxioms); Props V, IX, X re-typed
    ├── Bridge.lean                       -- Attr := Thing recovers Pars I; collapse transported
    └── Models/
        ├── DualAttribute.lean            -- A God with TWO attributes (cogitatio, extensio)
        └── InfiniteAttribute.lean        -- A God with infinitely many attributes; Def. VI recovered
└── Pars2/                                -- De natura et origine mentis
    ├── Idea.lean                         -- Props I, II, III, VII; A45–A50 (Pars2Axioms)
    ├── Quatenus.lean                     -- Props V, VI, VII-iff; A51–A55 (QuatenusAxioms)
    ├── Parallelismus.lean                -- Props VII-cor, VIII, IX; A56–A59; ResSingularis; A42-vacuity
    ├── Mens.lean                         -- Props X–XIII; A60–A67; Pars II's own axiomata; Corpus, percipit
    └── Models/
        └── MensWitness.lean              -- Consistency witness; coexistence + real modes + Int-indexed regress + a man
texts/
├── ethica1_la.txt … ethica5_la.txt       -- Latin per Pars
└── en_part1_elwes.txt … en_part5_elwes.txt   -- Elwes EN per Pars
docs/
├── gaps.md                               -- GAP-N catalogue
├── coverage.md                           -- Per-proposition status
├── auxiliary_axioms.md                   -- Section I/II/III register
└── HALLAZGOS.md                          -- Spanish findings digest (maintained separately)
papers/
└── cluster_a_irreducibility/             -- Bennett–Della Rocca paper
```

## Extensions beyond v1.0.0

Since the v1.0.0 release, four further modules extend Pars I's
theological, mereological, inherence, and consecution arcs —
**without touching the v1.0.0 axiom register** (`Pars1Axioms`,
`CausalAxioms`). Each new commitment lives in its own typeclass
extending `Pars1Axioms` (`TheologiaAxioms`, `MereologyAxioms`,
`InherenceAxioms`, `ConsecutioAxioms`), so the original register
and its published irreducibility results are unchanged;
downstream theorems opt in by consuming the extended typeclass.

Propositions XI, XII, XIII, XV, XVII, XVIII, XIX, XXIV, XXVI, and
XXIX were mechanised first (in full or in an honestly-flagged
partial form) via ten new auxiliary axioms, A27–A36. A subsequent
consecution batch (`Consecutio.lean`, axioms A37–A43) adds the
Prop. XVI–XXXVI causal-cascade arc: Props. XXI, XXII, and XXVIII
(📜 direct commitments, the last with a genuinely derived
"no-first-finite-cause" corollary), Prop. XXXVI (derived from
A43 + A38), Prop. XXV corollary, and partial forms of Props. XVI
(qualitative clause; cardinality open) and XX (conjunctive
content; the "unum et idem" identity open). Per-proposition
status and the exact derivation chains are tracked in
`docs/coverage.md`; full philosophical justification for each new
axiom is in `docs/auxiliary_axioms.md`.

Three kernel-level irreducibility witnesses now cover every
Section III axiom of the first extension batch, each against a
baseline **stronger** than the v1.0.0 counter-models for A12 and
A15 (which run against `StatedAxioms`, the register *without* the
Section III commitments):

- `Models/NoGod.lean` — God's existence (A27 / Prop. XI) is not
  derivable even from the full `Pars1Axioms` register (A1–A15).
- `Models/CounterexamplesII.lean` `ModeParts` — A32 (Prop. XII's
  parts-would-be-rival-substances horn) is falsified while
  `Pars1Axioms` + `CausalAxioms` + `TheologiaAxioms` +
  `InherenceAxioms` all hold: the parts-as-modes reading (Letter
  12; Curley) is a live alternative.
- `Models/CounterexamplesII.lean` `NecessaryMode` — A35 (Prop.
  XXIV) is falsified while the register minus A35 holds: only A35
  enforces the through-cause vs through-essence necessity
  distinction.

Joint consistency of the entire extended register — A1–A15 plus
A27–A43, every non-modal layer at once — is witnessed on a single
carrier by `Models/ConsecutioWitness.lean`, the largest
single-model consistency proof in the project.

A further pair of modules — `Realitas.lean` and
`Classificatio.lean` — extends the arc again, **without adding a
single new axiom to `Realitas.lean`'s own content** (Prop. IX is a
genuine derivation) and with exactly one new axiom in
`Classificatio.lean` (A44).

**Prop. IX and the counting framework**: `Realitas.lean` mechanises
Prop. IX (`prop_9_moreRealityMoreAttributes` + corollary
`prop_9_cor_godMaximalReality`) under the Della Rocca *constitutive*
reading of reality — "more reality" just *is* attribute-dominance —
reducing the proposition to a one-line transfer theorem, no new
axiom required. Along the way it introduces `hasAtLeastNAttributes`
and `HasInfiniteAttributes`, a `Fin`-based, Mathlib-free counting
framework that finally makes Def. VI's "*infinitis attributis*"
clause **stateable** — closing the missing-framework half of
GAP-8a.

**The attribute-collapse theorem**: pointing that counting
framework at `IsGod` reveals a sharp result. Five *already-committed*
pieces of the register — attributes typed as `Thing`, plus A8, A10,
A12, A14, A15 — jointly force that in **any** `Pars1Axioms` world
containing a God, every attribute of every substance equals that
God (`attribute_collapse`); God cannot have even two distinct
attributes. Def. VI's "*infinitis attributis*" clause is therefore
not merely unformalised but **unsatisfiable** wherever a God exists
(`def6_infinitis_attributis_unsatisfiable`). `Models/
MultiAttribute.lean` shows the incompatibility is sharp, not an
artifact of a weak framework: the full register tolerates a
substance with *infinitely* many attributes (carrier `Nat`,
`multiAttribute_infinitude`) — but only in a **godless** model
(`multiAttribute_hasNoGod`). Godless attribute plurality is
consistent; godful attribute plurality is impossible. Three escape
routes (restrict A12 to non-attribute substances; weaken A8/A10's
bite on attributes; type attributes off the `Thing` universe
entirely), each with its own cost, are catalogued but not adopted —
tracked as `docs/gaps.md` GAP-25.

## The Attributum layer — GAP-25 resolved

`Ethica/Attributum/` adopts the third escape route — type attributes
off the `Thing` universe — as a **parallel branch**. Nothing under
`Ethica/Pars1/` is modified: v1.0.0's register and the published
irreducibility results stand exactly as they are, and the collapse
remains true of Pars I.

`AttrWorld Thing Attr` extends `EthicaWorld Thing`, so every Pars I
primitive is reused verbatim; only attribution is re-routed, through
`perceivedAsEssence : Thing → Attr → Prop`. Because `Attributum a s`
has `a : Attr`, `Substance a` does not typecheck — the collapse
chain's third step is **inexpressible, not merely false**. Prop. X
survives via `perSeConceivedAttr`, a field of `AttrStructure Attr`,
a class that does not mention `Thing` at all. What the layer
withdraws is only A8's *bite on attributes* — precisely Bennett's
position (1984 §16, attributes as "basic and irreducible ways of
being"), now enforced by typing rather than by restricting an axiom.
The four attribute axioms are re-typed verbatim as A10′/A12′/A14′/
A15′, keeping their Section classifications.

Two witnesses, both depending on **no axioms whatever**:

- `Models/DualAttribute.lean` — a God with **two** distinct
  attributes, `cogitatio` and `extensio`, in a world carrying
  `AttrAxioms` *and* `StatedAxioms` (Spinoza's own A1–A11, the
  register the published results run against).
- `Models/InfiniteAttribute.lean` — a God with **infinitely many**
  attributes (`inf_def6_recovered`). Def. VI is satisfied outright,
  closing GAP-8a. Contrast `Models/MultiAttribute.lean`, which
  achieves infinitude on the full Pars I register only by being
  godless: here plurality and God hold *simultaneously*.

`Bridge.lean` supplies the diagnosis. `legacyAttrWorld` instantiates
`Attr := Thing`; under it `Attributum`, `IsGodAttr`,
`hasAtLeastNAttrs` and `HasInfiniteAttrs` are *definitionally* their
Pars I counterparts (four `Iff.rfl` lemmas), and `legacy_collapse`,
`legacy_god_no_two_attributes` and `legacy_def6_unsatisfiable`
transport Pars I's impossibility results into the new vocabulary.

So the **same sentence, under the same axioms, is satisfiable when
`Attr` is separate and refutable when `Attr := Thing`**. The
attribute collapse is an artefact of the Prop. X scholium's
identification of attributes with things — not a consequence of
Spinoza's substantive commitments. This is also what unblocks
Pars II, whose Props. I–II assert that Thought and Extension are two
distinct attributes of God.

**A44 and Prop. XXIII (partial)**: `Classificatio.lean` commits
**A44** (`ax_consecution_trichotomy`, Section III) — the
exhaustiveness premise Prop. XXVIII's *demonstratio* silently
consumes: every mode follows absolutely from an attribute of God,
from an eternal-infinite mode, or from another finite mode.
`prop_23_partial_classification` mechanises this trichotomy
directly, closing the premise half of GAP-23 (the finite-branch
exclusion for necessarily-infinite modes specifically remains
open). Running the project's demote-experiment discipline on A42
against this new axiom yields `A42_demote_via_trichotomy`: **A42 is
an equal-strength decomposition** over Σ = {A38, A40, A41, A44} —
see the demote-experiments table above.

## Pars II — first batch

`Ethica/Pars2/Idea.lean` opens the second Part with Props. I, II,
III and VII. It is the first module outside Pars I, and it rests on
the Attributum layer: Pars II's opening pair asserts that Thought
and Extension are two **distinct** attributes of God, which
`god_no_two_attributes` refutes in the Pars I register.
`pars2_opening_triple_inconsistent_in_pars1` states that refutation
in Pars I's own vocabulary — the precise sense in which the
Attributum layer was a prerequisite and not a refinement.

Two results are genuine derivations rather than commitments:

- **God has at least two attributes**
  (`prop_2_1_2_deusHabetDuoAttributa`), from A46 + A47 + A48. The
  first theorem in the project that Pars I's register actively
  refutes.
- **The parallelism** (Prop. VII,
  `prop_2_7_ordoEtConnexio`) — *ordo et connexio idearum idem est ac
  ordo et connexio rerum* — derived from A4ₛ plus A50, mirroring
  Spinoza's own one-line *demonstratio* ("*Patet ex axiomate 4
  partis I*"). Only the directional transfer is claimed; the
  scholium's identity reading is tracked as GAP-27.

Props. I, II and III are 📜-pattern commitments (A46, A47, A49), each
because the *demonstratio*'s load-bearing step is unavailable —
Spinoza's existential premise is his own empirical Axiom II (*Homo
cogitat*) for I–II, and Prop. I.35's *potentia* machinery for III.

**A45 retires the oldest placeholder in the project**: Spinoza's A6
(*Idea vera debet cum suo ideato convenire*) has been a `True`
stub since v1.0.0, annotated "idea/ideatum machinery is Pars II".
It is now substantive, on the functionality reading, with the
stronger adequacy content honestly deferred to batch 1.4.

`Models/MensWitness.lean` witnesses consistency of the whole
register on one carrier and proves the **coexistence** result: in
that single world God has two `Attr`-typed attributes *and* no God
has two `Thing`-typed attributes. The two attribution channels live
side by side, the `Thing`-typed one degenerate exactly as the
collapse theorem forces.

## Pars II — the *quatenus* layer (batch 1.2)

`Ethica/Pars2/Quatenus.lean` adds Props. V and VI, Prop. VI's
corollary, and the biconditional form of Prop. VII. It introduces
the project's first **attribute-relativised** primitives —
`modeUnder x a`, `causeUnder c e a`, `involvesConceptOf x a` — which
carry Spinoza's "*quatenus*": God causes a mode *insofar as* he is
considered under one attribute and *not* under another.

**Five new axioms, all Section II, no Section III commitment.** That
is the headline. Every one of A51–A55 is a sentence Spinoza writes
in the relevant *demonstratio*; none is a reconstruction of a
missing step, and no 📜-pattern axiom appears in this batch. The
*quatenus* machinery turns out to be expensive in primitives and
free in metaphysics — a fact worth having, given that the project's
guiding question is how many undeclared commitments the *Ethics*
actually needs.

Both clauses of **Prop. VI are derived**: the positive one from
`prop_16_cor1_godEfficientCause` (already mechanised in Pars I)
refined by A53; the exclusion one from A51's second conjunct
contradicting A52. **Prop. V** is then Prop. VI specialised to
`a := cogitatio` via A54 — Spinoza's own second *demonstratio*.

The batch also closes two gaps by **re-basing** `Pars2World` /
`Pars2Axioms` from `CausalWorld` / `CausalAxioms` onto
`ConsecutioWorld` / `ConsecutioAxioms`:

- **GAP-26** (Prop. III's *in Deo* localisation) — closed with
  **zero new axioms**. `prop_15_allInGod` became available, and
  `prop_2_3_ideaInDeo` derives the localisation from it, which is
  Spinoza's own route ("*per propositionem 15 partis I*"). The gap
  was a missing import, not a missing commitment.
- **GAP-27a** (Prop. VII's converse direction) — closed by A55, on
  the ground that "*idem est ac*" is an identity and identities are
  symmetric. GAP-27b, the scholium's claim that a mode and its idea
  are one and the same *thing*, remains open.

`Models/MensWitness.lean` was rebuilt for this batch on an
**infinite carrier** — `deus | idea : MensThing → MensThing`, God
plus the *idea ideae in infinitum*. This is forced, not decorative:
A45 (an idea has a unique ideatum), A49 (everything has an idea) and
A54 (ideas are modes of thought) are **jointly unsatisfiable on any
finite carrier**. Spinoza's own infinite regress of ideas is what
keeps the register consistent — a structural fact that surfaced from
trying to build the model, not from reading the text. The payoff is
that Props. V and VI now hold of a *real* mode, and their exclusion
clauses refuse `extensio` on a relation that demonstrably holds
under `cogitatio`.

Still deferred: Prop. IV (waits on Prop. I.XXX), GAP-27b and GAP-28
(Prop. V's *hoc est* gloss — ideas are not caused by their own
*ideata*).

## Pars II — the *esse objectivum* layer (batch 1.3)

`Ethica/Pars2/Parallelismus.lean` adds Prop. VII's corollary, Props.
VIII and IX, and their corollaries. Four new axioms, **three of them
Section II**; the one Section III axiom is not new content, for the
reason below.

**The blocker this batch had to clear first.** Pars I's Def. II is

```lean
finitumInSuoGenere x ≝ ∃ y, x ≠ y ∧ sameNature x y ∧ limitedBy x y
```

and `sameNature` is, following GAP-2's resolution path (b),
`∃ a, Attribute a x ∧ Attribute a y` — where `Attribute a s` carries
`Substance s`. So **Pars I's finitude predicate entails
substancehood**, and substances are provably disjoint from modes.
No mode is ever finite-after-its-kind:

```lean
theorem pars1_prop_28_vacuous_for_modes :
    ¬ ∃ x : Thing, Mode x ∧ finitumInSuoGenere x
```

The casualty is **A42**, whose own docstring calls it "the backbone
of finite-mode causation that Pars II–V consume throughout". Its
hypothesis is unsatisfiable in every `Pars1Axioms` world, so Prop.
I.XXVIII is mechanised and never fires — and Prop. II.IX, whose
*demonstratio* cites Prop. I.28 by name, could not have been derived
from it. `Definitions.lean` foresaw the problem in the same breath as
the definition ("*a separate `hasAttribute` relation will be added at
the modal layer*") and GAP-2's caveat recorded the promise.

**The repair costs no primitive.** Batch 1.2's `modeUnder x a`
already says which attribute a mode is a mode *of*, so three
definitions suffice:

```lean
sameNatureUnder x y        ≝ ∃ a : Attr, modeUnder x a ∧ modeUnder y a
finitumInSuoGenereModal x  ≝ ∃ y, x ≠ y ∧ sameNatureUnder x y ∧ limitedBy x y
ResSingularis x            ≝ Mode x ∧ finitumInSuoGenereModal x
```

`ResSingularis` is Pars II Def. VII, and **A59** is A42's content on
it. Nothing under `Ethica/Pars1/` is edited — v1.0.0 stays frozen and
the vacuity theorem sits beside A42 rather than replacing it, exactly
as GAP-25's repair went in a parallel branch.

With that in place, **Prop. IX is a full derivation following
Spinoza's *demonstratio* step for step**: A59 gives the object
another singular cause, A49 gives that cause an idea, A58 keeps the
idea singular, Prop. VII transfers the causal fact, and A45 forces
the two ideas apart. **Prop. VII's corollary** costs nothing at all —
A38, A49 and Prop. VII suffice. This is also A45's **first
consumer**: batches 1.1 and 1.2 carried it unused, and the README
said so.

`Models/MensWitness.lean` gained a third constructor,
`res : Int → MensThing`. The index type is forced, and by two
requirements pulling in opposite directions: A59 wants every singular
thing to have a singular *cause*, A43 wants every thing to have an
*effect*, so the causal order needs **neither a first nor a last
element**. `Nat` fails; `Int` works. Prop. IX's "*et sic in
infinitum*" is thus a two-sided requirement rather than a
one-directional regress — the second time in this Part that a
Spinozist thesis has turned up as a satisfiability condition.

Splitting `res` off from `idea` also gives the witness modes of
*extension*, so Prop. VI's exclusion clause is now non-vacuous in
**both** directions (`mens_prop_6_extensio`, `mens_prop_6_cor_res`),
and a `durat` predicate that genuinely splits the carrier, so Prop.
VIII is tested on both sides rather than waved through.

New gap: **GAP-29** — the *quatenus … affectus* locution relativises
God to an *individual mode*, where `causeUnder` relativises only to
an attribute. Same shape as GAP-22's outstanding target; the two
should be closed together.

## Pars II — the human-mind layer (batch 1.4)

`Ethica/Pars2/Mens.lean` adds Props. X–XIII and three corollaries —
where Pars II stops being about God's idea in general and starts
being about us. **Every proposition in the batch is a derivation**,
and the eight new axioms are seven Section II and one Section I; none
is Section III.

**Five of the eight are Spinoza's own axiomata of Pars II**, entered
here for the first time. Pars I's seven were in the register from the
start; Pars II's five had never been entered at all, which is why
Props. X–XIII could not be attempted before now.

| | Latin | Field |
|---|---|---|
| Ax. I | *Hominis essentia non involvit necessariam existentiam* | A60 |
| Ax. II | *Homo cogitat* | A61 |
| Ax. III | *Modi cogitandi … idea natura prior est* | A63 |
| Ax. IV | *Nos corpus quoddam multis modis affici sentimus* | A64 |
| Ax. V | *Nullas res singulares præter corpora et cogitandi modos sentimus* | **not entered** |

**Axioma V is redundant, and there is a theorem for it.** Its only
job in Pars II is the "*et nihil aliud*" of Prop. XIII, which Spinoza
reaches through Prop. I.XXXVI, Prop. XII and an empirical premise: a
second object of the mind would have some effect, we would have an
idea of that effect, and "*atqui per axioma 5 nulla ejus idea
datur*". On our reading of his **Axioma VI** — A45, an idea has at
most one object — the clause is analytic, because the mind is one
idea. `prop_2_13_objectumUnicum` is two lines. That is a small result
about the *Ethica*'s own economy rather than a formalisation
shortcut: the redundancy is exhibited, not asserted.

**Three notions that looked like primitives are definitions**, each
built from machinery an earlier batch already paid for:

```lean
Corpus b                ≝ modeUnder b extensio            -- Def. I,  from batch 1.2
pertinetAdEssentiam m x ≝ (durat m ↔ durat x)             -- Def. II, from batch 1.3
percipit m a            ≝ ∃ i, ideaOf i a ∧ comprehensaIn i m
```

The third is Spinoza's own gloss on Prop. XII — "*id ab humana mente
debet percipi **sive ejus rei dabitur in mente necessario idea***".
Only `Homo`, `mensHominis` and `affectio` are new primitives. Note
that `mensHominis` is deliberately *not* defined as "the idea of the
body": that identification is Prop. XIII's **content**, and defining
it away would turn the proposition into a tautology. Spinoza proves
it; so do we.

The derivations follow Spinoza's citations rather than working
around them. Prop. XI's actual-existence clause comes from **A57**,
which *is* Prop. VIII's corollary — exactly what he cites at that
step, and the second job batch 1.3's `durat` was built for. Prop.
XIII's *corpus* clause is his reductio run forwards.

Two things the batch could not get. **GAP-30**: Prop. XI's corollary
says the mind is a *part* of God's infinite intellect, and although
`Ethica/Pars1/Mereology.lean` has `properPart`, importing
`MereologyWorld` would drag A32 — a Section III commitment about the
indivisibility of substance — into Pars II for one corollary. And
GAP-29 now has a price tag: **A65** exists *only* because that gap is
open. It is the first axiom in the project whose existence is
entirely attributable to an unclosed gap, and it is flagged as such
so that closing GAP-29 shrinks the register rather than leaving a
fossil behind.

## Build

Lean 4.13.0 is pinned in `lean-toolchain`. No Mathlib dependency.

```bash
brew install elan-init
cd spinoza-ethica-lean
lake build
```

## Methodology summary

### Three layers

The base layer is classical first-order with primitive predicates
over a `Thing` universe. The modal layer adds S5 with `□` for
"necessary by virtue of essence" and re-derives the same
propositions through Kripke-frame machinery. A categorical layer
(topos / monoidal-closed-category formulation) is planned.

### Section sub-categorisation of auxiliary axioms

Beyond Spinoza's stated A1–A7, the Pars I formalisation requires
auxiliary axioms grouped into three sections:

- **Section I** — definitional bridges making explicit the
  ontological/conceptual co-extensions Spinoza uses without
  comment.
- **Section II** — substantive promotions of stated content into
  forms the kernel can use (e.g. excluded middle on `inItself`,
  bridges between `Cause` and `intelligibleThrough`).
- **Section III** — metaphysical commitments needed to fill gaps
  in Spinoza's *demonstrationes*, partitioned further into base
  axioms (§III.A), demote candidates (§III.B), and modal-layer
  promotions (§III.C).

The sub-categorisation makes commitment cost visible to readers
and supports the demote-experiment methodology described next.

### Demote experiments

For each Section III axiom A, the formalisation can be queried:
*does some weaker commitment Σ derive A from the base layer?*
The procedure declares Σ as a typeclass extending `EthicaWorld`,
attempts a direct proof of A from Σ-augmented base, and on
failure constructs a counter-model in `Models/Counterexamples.lean`
falsifying A while satisfying all of `EthicaWorld + Σ`. The
non-derivation argument runs at kernel level: any Lean derivation
of A from Σ would specialise to the model, contradicting the
constructed falsification.

Outcome patterns observed across Pars I's four demotable Section
III axioms of v1.0.0 (A12, A13, A14, A15), plus the post-v1.0.0
A42 demote (a different mechanism — a base-layer classification
commitment rather than modal-layer PSR, see below):

| Axiom | Demote Σ | Outcome |
|-------|----------|---------|
| A12 | `PSRSubstance` | Partial reduction; full irreducible |
| A13 | `PSRSelfCause` modulo bridge A18 | Equal-strength translation |
| A14 | `PSREssencePerception` | Trivial redescription |
| A15 | `PSRPlenitude` (plenitude + uniqueness) | Decomposition only |
| A42 | `TrichotomySigma` (A38+A40+A41+A44) | Equal-strength decomposition |

Universality clauses (A12, A15) resist Della-Rocca-flavoured
PSR-driven reduction; existence clauses (A13, A14) translate at
equal strength. The structural distinction is not made explicit
by the prose commentary on Spinoza and is the subject of the
companion paper. A42's demote runs a structurally similar
experiment one layer down — a base-layer register Σ (no modal
layer, no PSR) built from already-committed consecution axioms
plus one new commitment (A44, the trichotomy Prop. XXVIII's own
*demonstratio* consumes silently) — and lands on the same
"equal-strength decomposition" outcome A15 does: A42 is derivable,
but the destination register is no weaker than A42 itself. See
`Ethica/Pars1/Classificatio.lean` and `docs/auxiliary_axioms.md`'s
A42/A44 entries.

### Gap policy

Each `sorry` carries a `-- GAP-N` comment and an entry in
[`docs/gaps.md`](docs/gaps.md) recording the philosophical reason
and resolution path. Discharge happens in a dedicated commit that
updates `gaps.md` in the same change. Silent `sorry` is forbidden.

## Companion paper

The `papers/cluster_a_irreducibility/` directory contains a
research paper situating the formalisation in the
Bennett–Della-Rocca debate over Spinoza's Proposition V. The
paper provides the first machine-checked evidence in the debate,
encoding Bennett's reading of Spinoza's stated axioms as a
typeclass and Della-Rocca's substantive PSR as an extension class,
and establishing kernel-level non-derivability through
counter-models for A12 and A15.

## License

Code: MIT. Public-domain texts retain their PD status.

## Citation

**Paper** (arXiv:2605.02331):

```
Nakamura, Y. (2026). Bennett's Conjecture in Lean 4:
Counter-Models for the PSR-Reducibility of Spinoza's
Propositions V and XIV. arXiv:2605.02331.
https://arxiv.org/abs/2605.02331
```

**Software** (Zenodo, this repository):

```
Nakamura, Y. (2026). spinoza-ethica-lean (v1.0.0) [Software].
Zenodo. https://doi.org/10.5281/zenodo.20111521
```

**ORCID**: [0009-0001-7174-6737](https://orcid.org/0009-0001-7174-6737)
