# §3 The Spinoza *Ethica* Pars I formalisation in Lean 4

## §3.1 Why Lean 4

We chose Lean 4 (de Moura and Ullrich 2021) for three reasons.
First, its dependent type theory and typeclass mechanism let us
encode Spinoza's "axioms over an abstract universe of things" as
a typeclass parameterised by a `Type`, deferring commitments
about which things exist until concrete models or theorems
require them. Second, Lean's small trusted core (the kernel
type-checker) lets us state non-derivability results
model-theoretically without trusting any tactic library: a
counter-model that type-checks at kernel level establishes a
hard fact, not a metaphor. Third, Lean's inheritance for
typeclasses lets us layer commitments — base axioms, modal
extensions, PSR augmentations — without rewriting earlier
material, so the demote experiments of §4 can be run against a
single canonical formalisation.

The Lean source is open at
\url{https://github.com/Nakammura/spinoza-ethica-lean}; all
claims in this paper correspond to specific theorems in that
repository, verifiable via `lake build`.

## §3.2 The base typeclass `EthicaWorld`

We work in an abstract universe `Thing : Type u`. Spinoza's *id*,
*ea res*, *quod*, and similar referring expressions all denote
elements of this universe; we do not commit to any cardinality
of `Thing` (that there is exactly one substance is to be proved
as Proposition XIV, not assumed).

The base typeclass `EthicaWorld Thing` declares the primitive
predicates Spinoza uses through Pars I: ontological predicates
(`inItself`, `inAnother`, `limitedBy`), conceptual predicates
(`perSeConceived`, `conceivedThroughAnother`,
`intellectPerceivesAsEssence`), existence predicates
(`involvesExistence`, `natureRequiresExistence`), and modal /
ethical predicates (`absolutelyInfinite`, `expressesEternalEssence`,
`freelyExistent`, `constrained`, `eternal`).

All Spinoza's Definitions I–VIII are then *derived* notions, not
further primitives. Definition III's `Substance` becomes
`inItself x ∧ perSeConceived x`; Definition IV's `Attribute`
becomes `Substance s ∧ intellectPerceivesAsEssence s a`;
Definition V's `Mode` becomes `inAnother x ∧ conceivedThroughAnother x`;
Definition VI's `IsGod` becomes the conjunction of `Substance g`,
`absolutelyInfinite g`, the existence of an attribute, and the
universal essence-expression clause. Spinoza's Definitions are
thus type-theoretic *definitions* in our sense: each is a `def`
in Lean, expanding to a Boolean combination of `EthicaWorld`
primitives.

Two interpretive decisions in the Definitions deserve note. The
first concerns *sameNature* — Spinoza's "ejusdem naturae" — which
he uses adjectivally without explicit definition. We adopt the
Della Rocca / Curley reading on which "same nature" is
constitutively shared attribute: `sameNature x y :=
∃ a, Attribute a x ∧ Attribute a y`. The Bennett-line alternative
(treat *sameNature* as a separate primitive related to attributes
by axiom) would make our counter-models slightly stricter; we
note this as one of the "fidelity caveats" of §8.

The second decision concerns Spinoza's *sive* in Proposition V's
formulation *ejusdem naturae sive attributi* ("of the same nature
or attribute"). Latin *sive* admits two readings: identifying
("that is to say") and disjunctive ("or alternatively"). Curley's
1985 translation (and Della Rocca's reading on which we have
already settled for *sameNature*) take *sive* identifyingly,
making "same nature" and "same attribute" equivalent. Bennett
1984 §17 considers a disjunctive reading on which "nature" and
"attribute" can come apart. The identifying reading is implicit
in our `sameNature` definition; the disjunctive reading would
require an additional primitive `sameKind` distinct from shared
attribute. This is the second fidelity caveat: our counter-models
operate under the identifying *sive*; a disjunctive *sive* would
require a different formal apparatus and possibly different
counter-models. We discuss this further in §8.4.

## §3.3 The base axiomatic typeclass `Pars1Axioms`

`Pars1Axioms Thing` extends `EthicaWorld Thing` with Spinoza's
Axioms I–VII plus auxiliaries we have made explicit. The
sub-categorisation is:

- **Section I** — definitional bridges. Axioms that make explicit
  the ontological/conceptual co-extensions Spinoza uses
  throughout Pars I but does not state separately:
  - A1ₑ — exclusivity of *in se* and *in alio*: `¬ (inItself x ∧
    inAnother x)`. Spinoza's text states the disjunction without
    qualifying its mood, but the chain of *demonstrationes* in
    Pars I (especially P1, P4, P5) requires the disjunction to
    be exclusive: an inclusive reading would leave open cases
    (some `x` both *in itself* and *in another*) that the proofs
    silently exclude. We adopt this exclusive reading as a
    Section I auxiliary axiom rather than impute it to Spinoza's
    text.
  - A8 / A9 — parallelism between ontological and conceptual
    halves of Definitions III and V: `inItself x ↔ perSeConceived x`
    and `inAnother x ↔ conceivedThroughAnother x`.
  - A10 — attribute–substance identity-of-conception: every
    attribute of a substance is itself per se conceived.
  - A11 — *causa-sui* clause-equivalence: `involvesExistence x
    ↔ natureRequiresExistence x` (Definition I's *sive* read
    identifyingly).

- **Section II** — substantive promotions of Spinoza's stated
  axioms whose content needs the modal and causal layer to be
  expressible. A4 and A5 in this register: their substantive
  forms live in `CausalAxioms` (introduced in §3.5 below) where
  the cause-relation and intelligibility-relation are available.

- **Section III** — substantive metaphysical commitments that
  fill gaps in Spinoza's *demonstrationes*. The four base-layer
  Section III axioms are:
  - **A12** (`ax_substanceIdByAttribute`): two substances sharing
    an attribute are identical. *This is Proposition V's content
    adopted as an axiom.*
  - A13: every substance involves existence. (Proposition VII.)
  - A14: every substance has at least one attribute. (A
    structural prerequisite for Proposition XIV.)
  - **A15** (`ax_IsGod_has_attribute_of`): every realised
    substance attribute is also a god's attribute. (A load-bearing
    universality clause for Proposition XIV.)

The classification of A12 and A15 as Section III commitments is
itself a position in the Bennett–Della Rocca debate. Bennett
holds that these axioms encode metaphysical commitments Spinoza's
text does not establish; Della Rocca holds that they fall out of
PSR. Both readings are consistent with our placing the axioms in
Section III: the Section III register is precisely where
commitments live whose status as Spinozistic is contested.

In Lean syntax, A12 reads:

```lean
ax_substanceIdByAttribute :
  ∀ s₁ s₂ a : Thing,
    Attribute a s₁ → Attribute a s₂ → s₁ = s₂
```

The translation from Spinoza's Latin *In rerum natura non possunt
dari duae aut plures substantiae ejusdem naturae sive attributi*
to this formal statement involves three steps: (a) the
universally-negated existential ("there cannot be given two or
more substances …") becomes `∀ s₁ s₂, ¬ (s₁ ≠ s₂ ∧ …)`, which
classical logic rewrites to the conditional form above; (b) the
"of the same nature or attribute" clause becomes the
"sharing-an-attribute" hypothesis under the identifying *sive*
reading; (c) the implicit substance-status of the things ranged
over is supplied by the `Attribute a s` clause itself, since
`Attribute a s` carries `Substance s` constitutively (Definition
IV). The translation is the regimentation common to Bennett 1984
§17, Garrett 1990, and Della Rocca 2008 ch. 2; we adopt it
without modification.

## §3.4 The modal-layer extension

For some demote experiments — particularly the A13 attempt of
§7 — we need world-relative existence and causation predicates
that Pars I's text does not directly require. We extend
`EthicaWorld` with a parallel modal layer:

- `ModalEthicaWorld Thing World` adds `existsAt : Thing →
  World → Prop`. The `World` parameter is abstract; we adopt
  S5 / universal accessibility for "necessary" claims, as is
  standard in modal reconstructions of Spinoza's necessitarianism
  (Della Rocca 2008 ch. 2 develops the necessitarian reading
  without fixing a specific modal logic).
- `ModalEthicaAxioms` provides A18, the bridge
  `involvesExistence ↔ ∀ w, existsAt`. This is a PSR-flavoured
  commitment that essential existence and necessary existence
  coincide; it is itself a modal-layer Section I axiom in our
  classification.
- `ConceptualStructure` adds a world-invariant `conceptualDep`
  binary relation (Della Rocca's reading of conceptual
  dependence as essential, not contingent), with bridges A19 /
  A20 to `perSeConceived` and `conceivedThroughAnother`.
- `ModalCausalWorld` adds world-relative `causeAt`, plus bridge
  axioms for Spinoza's A3 (the "from cause necessarily follows
  effect" content; see Bennett 1984 §8, p. 32, where 1a3 is read
  as "conjoining causal rationalism with a version of explanatory
  rationalism: causes necessitate, and nothing happens without a
  cause") and A21 connecting world-uniform `Cause` to
  `∀ w, causeAt c e w`.

The modal extension is what allows us to formulate the demote
candidate axioms — `PSRSubstance`, `PSRSelfCause`,
`PSREssencePerception`, `PSRPlenitude` — that the §4 methodology
runs against the Section III commitments. Each demote axiom
class extends or coexists with `Pars1Axioms` and provides one
or more PSR-flavoured commitments matching Della Rocca 2008's
reconstruction of the relevant Spinozistic principle.

The `PSRSubstance` class declares an axiom A22 — committing that
distinct substances differ in at least one attribute — that we
shall use in §5 to attempt the A12 demote. The axiom corresponds
to Della Rocca 2008 ch. 2's substance-distinguishability
argument; its full Lean signature, and the precise correspondence
to Della Rocca's prose, are given in §5.2.

## §3.5 Layered inheritance — a brief note

Lean 4's structure-inheritance mechanism does not automatically
resolve diamond inheritance: when multiple classes share
`EthicaWorld` as a common parent, they must be wired together
explicitly (typically via `toEthicaWorld := inferInstance`)
rather than via automatic merging. The modal extension hits
this concretely; the multiple bridge structures must be declared
as separate requirements rather than collapsed into a single
unified class. This engineering pattern is a mechanical feature
of typeclass systems generally (Coq, Isabelle, and Agda exhibit
related patterns under their own elaboration disciplines) and we
draw no philosophical conclusion from it. We note only that the
analytic-style design we adopted — keeping ontological,
conceptual, causal, and modal structures as separate typeclass
commitments rather than collapsing them into a single unified
class — is *consonant* with Bennett's treatment of attribute as
a "basic and irreducible way of being" (Bennett 1984 §16,
especially p. 61, on attributes as logically irreducible to one
another), while a unified PSR-driven structure (Della Rocca
2008) would correspond to a more aggressively merged design. The
choice is the formaliser's, not Spinoza's; the trace is
suggestive rather than evidential, and we leave the
methodological question of whether design choices carry
interpretive weight in mechanised philosophy projects to a
separate paper in preparation.

## §3.6 What the formalisation establishes for our purposes

For the Bennett–Della Rocca debate, the formalisation has three
properties that matter:

1. *Precision of the Bennett-line "stated resources"*. The
   Section I + II + Spinoza's A1–A7 + Definitions axiom set is
   a candidate regimentation of "what Spinoza explicitly gives
   himself". Bennett's diagnosis, in our formalisation, becomes
   the meta-claim that Section III commitments cannot be derived
   from Section I + II + A1–A7.

2. *Precision of the Della Rocca PSR augmentations*. Each PSR
   class — `PSRSubstance`, `PSRSelfCause`, `PSREssencePerception`,
   `PSRPlenitude` — names a specific Della-Rocca-flavoured
   addition to Spinoza's stated axioms, allowing Bennett's
   conjecture and Della Rocca's reconstruction to be tested
   against each other in mechanically distinct experiments.

3. *Counter-model construction discipline*. Models with explicit
   `EthicaWorld` instances and concrete `Thing` types let us
   establish non-derivability claims at kernel level: a
   witnessing
   counter-model is a finite, type-checked artifact, not a
   prose argument about absence-of-proof.

The formalisation as currently committed has 10 modules and
~2950 lines of Lean (including documentation), with zero `sorry`
(incomplete proof) markers and zero raw `axiom` declarations
outside the typeclass register. The source's `gaps.md`,
`coverage.md`, and `auxiliary_axioms.md` document every Section
III commitment with full Bennett-honest scoping notes — these
are non-essential for the paper's claims but support reader
verification of the project's epistemic discipline.

We turn now to the methodology of the demote experiments
themselves.
