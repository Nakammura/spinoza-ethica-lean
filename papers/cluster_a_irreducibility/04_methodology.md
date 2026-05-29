# §4 The demote-experiment methodology

## §4.1 The general schema

A demote experiment is an attempt to derive a Section III axiom A
from a strictly weaker commitment family Σ. The aim is to locate A in
the topology of Spinozistic commitments: is A *reducible* to weaker
principles (in which case Spinoza's deeper commitment lies in Σ), or
is A *irreducible* (in which case A itself names a substantive
commitment Spinoza must introduce as a primitive)?

The schema admits five distinct outcomes:

1. *Full reduction*: A derives from Σ + base axioms, and Σ is
   strictly weaker than A. Bennett's critique fails for A; the
   commitment relocates to Σ.

2. *Equal-strength translation*: A derives from Σ + base, but the
   elements of Σ are not strictly weaker than A; they are
   redescriptions of A in different vocabulary. The reformulation is
   informative but not a reduction.

3. *Partial reduction*: A in some restricted form derives from Σ +
   base, but A in its full form does not. Σ captures part of A's
   content but not all.

4. *Decomposition-only*: A derives from Σ + base where Σ is a
   conjunction of components, neither of which is strictly weaker
   than A. The reformulation distributes A's commitment across
   multiple axioms but does not reduce its strength.

5. *Full irreducibility*: A does not derive from the specific Σ
   candidates tested. Stronger commitment families might still derive
   A; the claim is bounded to the augmentations actually formalised.
   The Bennett-line scope distinction is developed in §8.1.

Pars I yields four of these patterns concretely (1 not yet observed):
A12 partial-only with full-form irreducibility (§5), A13
equal-strength translation via modal-causal vocabulary (§7), A14
trivial redescription via essence-perception vocabulary (§7), A15
decomposition-only with one component non-trivially weaker than A15
(§6). The four-pattern typology itself is the subject of §7.

## §4.2 The Σ candidates

The candidate commitment families Σ for a Pars I demote experiment
are constrained by Spinoza scholarship. We choose each Σ to match a
specific reconstruction proposed by Della Rocca 2008 or close
cognates. For A12, the candidate is `PSRSubstance`, a typeclass
declaring an axiom A22 that captures Della Rocca's "distinct
substances must differ in some attribute" intuition. For A13, the
candidate is `PSRSelfCause`, declaring A23 that every substance is
self-causal at every world. For A14, the candidate is
`PSREssencePerception`, declaring A24 that every substance has an
intellect-perceived essence. For A15, the candidate is
`PSRPlenitude`, declaring two axioms A25 (every realised substance
attribute is also some god's attribute) and A26 (any two gods are
identical).

Each candidate is a *modal-layer Section III commitment* in our
register: it is added to the commitment system, not derived from the
base. The demote experiment then asks whether, with this specific
Della-Rocca-flavoured commitment in scope, the Section III target
axiom (A12, A13, A14, or A15) becomes a theorem. The question is
decidable by Lean's elaborator: either the proof type-checks at the
kernel, or a counter-model shows it cannot.

## §4.3 The kernel-level discipline

Independence results, claims of the form "A is not provable from Σ,"
are meta-logical and cannot be stated internally in Lean; this
constraint is shared with all type-theoretical proof assistants. The
disciplined alternative is *model-theoretic*: construct a concrete
model in which Σ holds while A fails. An assumed derivation of A from
Σ would specialise to the model and produce A's conclusion there, but
the model proves the negation, so the assumed derivation would derive
`False`, which Lean's kernel disallows. The argument appeals to
kernel consistency and type-theoretic specialisation, reducing the
non-existence claim to two ordinary Lean theorems: the model
satisfies Σ, and the model falsifies A. We assume Lean 4's kernel is
consistent. Under standard metamathematical assumptions, Lean 4's
underlying type theory (Carneiro 2019's extension of the Calculus of
Inductive Constructions with quotient types, propositional
extensionality, and primitive projections) is consistent relative to
ZFC augmented with countably many inaccessible cardinals (one per
universe level), paralleling Werner 1997's earlier relative-consistency
result for pure CIC. The assumption is widely accepted within the
proof-assistant community.

## §4.4 Counter-model construction

A counter-model for the Σ → A demote attempt has three components:

1. A finite inductive `Type` (typically 3-5 elements) capturing the
   model's universe.
2. Explicit `EthicaWorld`, `StatedAxioms`, and Σ-class instances on
   that type, discharging every typeclass field with concrete proof
   terms or tactic blocks.
3. A theorem exhibiting the falsification of A on this model:
   specific elements with the relevant predicates such that A's
   conclusion fails for them.

The construction is direct rather than abstract. We do not invoke a
general framework for Kripke-style Spinoza models; we hand-craft each
counter-model for the specific demote attempt. The trade-off is
engineering economy versus generality: a general framework would let
us re-use machinery across demote attempts, but would require
theorising about what "Spinoza model" means in general, itself a
contested question. Hand-craft is conservative.

One design choice is forced by `IsGod`'s definitional structure: its
fourth conjunct asks that every attribute of g express eternal
essence, and the most compact discharge sets `expressesEternalEssence
_ := True` uniformly, over-shooting Spinoza's restriction (which
limits the predicate to attributes proper). This is a *Spinoza
fidelity caveat* — no effect on the meta-logical claim, but bearing on
the counter-model's appropriateness as Spinozistic ontology. We
discuss it in §8.3 (F1).

A second feature is forced by the stated register itself. A10 (every
attribute is per se conceived, Spinoza Ip10) and A8 (in-itself ↔
per-se-conceived) together entail that any attribute-thing is in
itself and per se conceived — hence a substance, by Definition III.
The counter-models therefore interpret every element as a substance.
(An earlier draft instead treated attribute-things as modes, which
left A10 unsatisfiable and confined the models to the bare
`EthicaWorld` predicate signature; §8.3 records the retirement of
that choice.) The cost is that the models contain no modes, and a
substance may be its own or another's attribute — milder fidelity
caveats (§8.3 F3) appropriate to a Bennett-line multi-substance world.

The caveats are both *logically harmless* — the counter-models are
valid instances of `StatedAxioms` + Σ and the falsification theorems
hold — and *philosophically informative*, since a more
Spinoza-faithful counter-model would constrain predicate values more
carefully. We accept them for the present paper's purpose,
establishing irreducibility against specific Della Rocca
reconstructions, and note them as opportunities for refinement in
§8.3.

## §4.5 The retired marker-theorem trick

A previous draft of this work used a different presentation of the
irreducibility claim: a Lean theorem named, for example,
`A12_full_NOT_demotable_from_PSR_alone`, whose statement was `True`
and whose proof was `trivial`. The intent was to provide a citable
artifact in the Lean source documenting the irreducibility. In
retrospect this was Lean-as-rhetoric: the theorem proves nothing
about provability; it merely names an empty content with suggestive
prose surroundings. A reader inspecting the source file might mistake
the marker for a machine-checked irreducibility result. That
impression would be wrong.

The discipline we now follow, counter-models rather than marker
theorems, is what makes the irreducibility claim mechanical rather
than rhetorical. The methodological lesson is general beyond Spinoza:
in a mechanised philosophy project, non-derivability claims should be
backed by counter-models or left as plain prose claims; they should
not be encoded as trivial-content Lean theorems with claim-laden
names.

The full development of this discipline, alongside other
methodological points the project's history surfaced, belongs in a
separate paper on *mechanised philosophy methodology* (in
preparation). Here we record the marker-theorem retirement as it
bears on the irreducibility claims of §5–§7.

## §4.6 The methodology applied

With the schema, the Σ candidates, the kernel-level discipline, and
the counter-model construction in place, we can run the experiments.
§5 presents the A12 demote attempt: the partial success of
`PSRSubstance` and the full irreducibility witness via the
four-element `A12CounterModel`. §6 presents the A15 analogue:
plenitude alone fails, decomposition with god uniqueness succeeds,
and a three-element `A15CounterModel` witnesses the alone-failure. §7
abstracts the four-axiom typology from these and the two
redescription cases (A13, A14) that we treat more briefly.
