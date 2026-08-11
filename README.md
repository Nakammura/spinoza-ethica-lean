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
    └── Models/
        └── MensWitness.lean              -- Consistency witness; the coexistence result
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
register — A1–A15, A4ₛ/A5ₛ, A10′–A15′, A45–A50 on one carrier — and
proves the **coexistence** result: in that single world God has two
`Attr`-typed attributes *and* no God has two `Thing`-typed
attributes. The two attribution channels live side by side, the
`Thing`-typed one degenerate exactly as the collapse theorem forces.

Deferred to batch 1.2: Props. V and VI, which need *quatenus* —
attribute-relativised causation (`causeUnder : Thing → Thing → Attr
→ Prop`), the same ternary-relativisation prerequisite GAP-22 tracks
for Prop. I.XXII. Prop. IV waits on Prop. I.XXX.

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
