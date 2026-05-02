# §8 Scope, limitations, and what the counter-models do not establish

## §8.1 The strict claim and the Bennett-line scope

The mechanical evidence the paper provides is bounded. The
strict claims established are two:

(S-A12) A12 is not provable from `[EthicaWorld T] +
[PSRSubstance T]` alone, witnessed by the four-element
`A12CounterModel`.

(S-A15) A15 is not provable from `[EthicaWorld T]` plus the
plenitude clause of `[PSRPlenitude T]` alone (without the god
uniqueness clause), witnessed by the three-element
`A15CounterModel`.

The strict claims are narrower than the narrative reading of the
paper might suggest in two respects, and we record both
explicitly.

*First, the typeclasses the counter-models instantiate are
`[EthicaWorld T] + [PSRSubstance T]` and `[EthicaWorld T] +`
*plenitude*, not the full `[Pars1Axioms T]` register of Section
I + II + Spinoza's stated A1–A7.* The counter-models do not — and
under the F2 fidelity choice of §8.3 cannot — instance the full
`Pars1Axioms` register: F2's three-category collapse forces
`inAnother` to track `¬ isSubstance` exactly, so non-substance
attribute-things like `a_shared` cannot simultaneously satisfy
A8 (`inItself ↔ perSeConceived`) and A10 (every attribute is per
se conceived) without forcing `inItself a_shared = true`, which
would contradict the substance/non-substance split. The F2
caveat is therefore not only a Spinoza-faithfulness issue (as
§8.3 frames it) but also a *logical-scope issue*: the strict
non-derivability claims hold over the typeclasses witnessed
above, not over the full Section I + II + A1–A7 + PSR
augmentation.

How this affects the narrative claim. The Section I auxiliary
axioms (A8–A11) are bridges between predicates — parallelism of
ontological and conceptual halves, attribute-conception, *causa-
sui* clause-equivalence; they shape the predicate-graph structure
but do not deliver substance-individuation principles or
attribute-universality clauses. The plausible expectation is that
expanding the type universe to track attributes separately from
modes (the §8.3 F2 refinement) would preserve the falsifying
witnesses while letting the counter-model satisfy A8–A11 jointly,
and that the strict claim would transfer to the broader
typeclass. We have not carried out this construction; we
therefore treat the broader claim as a conjecture *supported by
but not formally entailed by* the strict claim. The strict claim
is what the kernel verifies; the narrative claim is the
philosophical reading we believe the strict claim licenses.

*Second, the strict claims rule out specific PSR-augmentations
rather than every candidate.* Bennett's full doubt — that no
valid argument for Proposition V can be constructed from the
resources Spinoza explicitly gives himself, *under any reasonable
charitable reconstruction* — quantifies over a much broader space
than the two augmentations above cover. Bennett's doubt would be
vindicated only by ruling out *every* candidate augmentation a
Della-Rocca-flavoured reconstruction might propose. We do not
establish the broader claim. The counter-models are *first-step
mechanical evidence* for the Bennett-line position; they are not
closing argument. What they do is move the dispute past prose:
any further PSR-augmentation a Della-Rocca-leaning interpreter
wishes to propose can now be tested mechanically, against the
same counter-models or against new ones.

## §8.2 Thoroughgoing PSR — formal candidates

The most ambitious Della Rocca position invokes Spinoza's
"thoroughgoing commitment to the PSR" (Della Rocca 2008, p. 1)
— that every fact whatsoever has a sufficient reason. The
formalisation question is whether this thoroughgoing form can
be stated non-trivially in our framework and whether, so
stated, it derives A12 and A15.

A naive formalisation reads:

```
ax_thoroughgoing_PSR :
  ∀ x y : Thing, x ≠ y → ∃ φ : Thing → Prop, φ x ∧ ¬ φ y
```

But this is provable in Lean — take `φ := fun z => z = x`. The
trivial property "being identical to x" distinguishes any
distinct pair. So this naive formulation is empty: it commits
nothing.

A non-trivial formalisation must restrict the predicates. One
candidate restricts to *Spinozistically-significant* properties
— attributes, modes, ontological status — but specifying that
restriction itself requires further metaphysical commitments.
Another candidate restricts to predicates definable from the
`EthicaWorld` primitives, which would make the axiom non-trivial
but also drastically narrows what "every fact" means in
Spinoza's intent. A third candidate restricts to predicates
expressible in some logic of essence or modality, which adds
substantial machinery to the formalisation.

Each of these three non-trivial candidates is a project in
itself. We do not develop them
here. The point is methodological: thoroughgoing PSR is
unrefuted by our counter-models, *and* its non-refutation is
substantively correlated with the difficulty of stating it
non-trivially. Della Rocca's prose appeals to thoroughgoing PSR
without constraining it to any particular formal shape; a
charitable formalisation must do that constraining itself, and
each constraint choice is a further interpretive position. We
treat thoroughgoing-PSR formalisation as open future work and
invite readers to attempt their own candidates against the
project's counter-models.

## §8.3 Counter-model fidelity caveats

Two design choices in the counter-model construction (§§5–6) are
deliberately Spinoza-unfaithful in service of compact
construction.

(F1) `expressesEternalEssence _ := True` is set uniformly across
the counter-model universe. Spinoza's text restricts the
predicate to attributes proper (Definition VI explanation; Pars
II Proposition VIII). Setting it `True` for non-substance
elements like `a_shared` or `attr_g₂` flatly contradicts the
restriction. The choice is convenient — it discharges `IsGod`'s
fourth conjunct vacuously — but is not the choice a fully
Spinoza-faithful counter-model would make.

(F2) `inAnother x := ¬ isSubstance x` (and the conceptual
counterpart) collapses Spinoza's three-category ontology
(substances, attributes, modes) into a two-category split
(substance vs non-substance). Attribute-things in our
counter-models are treated as modes, even though Spinoza's
attributes are essence-aspects of substance rather than
independent objects.

Neither caveat affects the *strict* meta-logical claim — the
counter-models do satisfy `[EthicaWorld T] + [PSRSubstance T]`
(respectively `[EthicaWorld T] +` plenitude) and falsify A12
(respectively A15). The falsification of A12 depends only on the
`intellectPerceivesAsEssence` graph (which the caveats leave
untouched), and similarly for A15. The caveats are *logically
harmless against the strict claim*. They do, however, bear on
two further issues. First, on philosophical appropriateness: a
Spinoza-faithful counter-model would constrain
`expressesEternalEssence` to attributes proper and expand the
type universe to track attributes separately from modes. Second,
on the *logical scope* of the broader narrative claim — F2's
three-category collapse prevents the counter-models from
instancing the full Section I + II + A1–A7 + PSR augmentation,
as §8.1 records. We accept the caveats for the present paper's
purpose — establishing irreducibility against specific Della
Rocca reconstructions — and treat them as opportunities for
refinement in future work.

## §8.4 Sensitivity to the *sive* translation

§3.2 records our adoption of the identifying reading of Latin
*sive* in *ejusdem naturae sive attributi*, following Curley
1985 and the reading implicit in Della Rocca 2008. Bennett 1984
§17 considers a disjunctive reading on which "nature" and
"attribute" come apart — Spinoza's *sive* listing two distinct
features substances might share, rather than glossing one as the
other. Our central claims are sensitive to this choice, and we
record the sensitivity here.

Under the identifying reading, A12 reads (as in §3.3)
`∀ s₁ s₂ a, Attribute a s₁ → Attribute a s₂ → s₁ = s₂` — sharing
an attribute suffices for identity. Under a disjunctive reading,
A12 would split into two clauses: a *sameNature* clause (two
substances of the same nature are identical) and a
*sameAttribute* clause (two substances sharing an attribute are
identical), with *sameNature* requiring a new primitive
`sameKind` distinct from shared attribute. Whether the
counter-models of §5–§6 falsify both clauses depends on how
`sameKind` is interpreted: a `sameKind` defined as shared
attribute collapses the readings (A12 reduces to its identifying
form); a `sameKind` independent of attribute would let the
counter-models falsify the *sameAttribute* clause while leaving
the *sameNature* clause's status open.

Two consequences. First, the strict claim S-A12 of §8.1 carries
over to the *sameAttribute* clause of a disjunctive-*sive*
formulation — the same four-element counter-model witnesses
irreducibility against `[EthicaWorld T] + [PSRSubstance T]`.
Second, the *sameNature* clause under disjunctive *sive* would
need its own demote experiment, with a new PSR-flavoured
candidate matching the nature-sharing predicate; we have not
carried out this construction. The translation choice therefore
affects scope (which formal regimentation of Proposition V the
strict claim addresses) but not the specific irreducibility
result we establish for the regimentation we adopt. Readers
inclined to a disjunctive-*sive* reading should treat our result
as bearing on the *sameAttribute* fragment of the disjunction;
the *sameNature* fragment is open.

## §8.5 The Garrett-route demote attempt

Garrett 1990's reconstruction (§2.3) is a distinct demote
candidate from Della Rocca's PSR. The Garrett route would
replace `PSRSubstance` with a typeclass committing that
Spinoza's "in and conceived through" relation (ID3 / ID5,
together with IA1 / IA2) is strict and total — strong enough
that any difference of modes resolves into a difference of
attributes. Whether such a commitment, formally stated, derives
A12 is an open mechanical question our formalisation supports
but does not develop.

The construction would proceed as the §5 demote did: declare
the strong-Definition-III axiom in a typeclass, attempt the A12
proof, and if it fails, exhibit a counter-model. We expect the
attempt to succeed for some formulations of the axiom (a
sufficiently strong axiom would derive A12 by definition) and
to fail for weaker formulations. The interesting question —
which is the *minimal* Garrett-route axiom that delivers A12 —
is itself a research project we leave to follow-up work.

## §8.6 Other open questions

*Counter-model generality.* The counter-models we construct are
ad hoc — small inductive types built for specific
non-derivability targets. A general framework for Spinoza-
flavoured Kripke models would let demote attempts share
machinery, but presupposes a settled formal account of "Spinoza
model" that the demote experiments are themselves attempting to
clarify. We leave the framework question to a methodology
companion paper in preparation.

*Finite vs intended cardinality.* Our counter-models have 3 or
4 elements; Spinoza's intended ontology is infinite. The
non-derivation argument does not depend on cardinality (a Lean
universal statement that fails for a finite witness fails *as
a universal statement*), but the philosophical question of
whether finite counter-models are appropriate witnesses for
Spinoza's infinite-substance metaphysics deserves attention. We
note the question and defer detailed treatment.

*Pars II and Pars III.* The formalisation extends only through
Pars I. The mind-body parallelism of Pars II Proposition VII
and the *conatus* doctrine of Pars III may yield further
demote experiments and irreducibility results. Whether the
typology we identify generalises beyond Pars I is an empirical
question the formalisation is positioned to answer through
extension.
