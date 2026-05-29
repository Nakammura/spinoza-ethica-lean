# §8 Scope, limitations, and what the counter-models do not establish

## §8.1 The strict claim and the Bennett-line scope

The mechanical evidence the paper provides is bounded. The strict
claims established are two:

(S-A12) A12 is not provable from `[StatedAxioms T] + [PSRSubstance
T]`, witnessed by the four-element `A12CounterModel`.

(S-A15) A15 is not provable from `[StatedAxioms T]` plus the plenitude
clause of `[PSRPlenitude T]` (without the god uniqueness clause),
witnessed by the three-element `A15CounterModel`.

Here `StatedAxioms` is Spinoza's stated-axiom register: his seven
axioms A1–A7 together with the Section I definitional bridges (A1ₑ,
A8–A11) and the Section II placeholders, but without the Section III
substantive commitments (A12–A15). The counter-models instance this
full register at kernel level. An earlier draft instanced only the
bare `EthicaWorld` predicate signature, because the
"attributes-as-modes" interpretation (the retired F2 caveat of §8.3)
left A10 — every attribute is per se conceived, Spinoza Ip10 —
unsatisfiable for the attribute-things; the all-substance
interpretation now used (§§5.4, 6.4) discharges A10 and the rest of
the stated register honestly. The strict claims therefore bear on
Spinoza's stated resources, not merely on a predicate signature.

Two remarks on scope follow. The first is not a limitation but a
structural necessity: the counter-models do not, and cannot, instance
the *full* `Pars1Axioms` class, because `Pars1Axioms` contains A12
(and A15) as Section III *fields* — any instance satisfies A12 by
construction, so none could falsify it. Carving out `StatedAxioms` as
a separate class is what makes the question well-posed: non-derivability
of a Section III axiom can only be witnessed against a register that
omits it, and `StatedAxioms` is the largest fragment of Spinoza's
stated resources against which the question is even statable. The
counter-models satisfy all of it.

The second remark is a genuine narrowing: the strict claims rule out
specific PSR-augmentations rather than every candidate. Bennett's full
doubt, that no valid argument
for Proposition V can be constructed from the resources Spinoza
explicitly gives himself *under any reasonable charitable
reconstruction*, quantifies over a much broader space than the two
augmentations above cover. Bennett's doubt would be vindicated only
by ruling out *every* candidate augmentation a Della-Rocca-flavoured
reconstruction might propose. We do not establish the broader claim.
The counter-models are *first-step mechanical evidence* for the
Bennett-line position; they are not closing argument. What they do is
move the dispute past prose: any further PSR-augmentation a
Della-Rocca-leaning interpreter wishes to propose can now be tested
mechanically, against the same counter-models or against new ones.

## §8.2 Thoroughgoing PSR: formal candidates

The most ambitious Della Rocca position invokes Spinoza's
"thoroughgoing commitment to the PSR" (Della Rocca 2008, p. 42), the
claim that every fact whatsoever has a sufficient reason. The
formalisation question is whether this thoroughgoing form can be
stated non-trivially in our framework and whether, so stated, it
derives A12 and A15.

A naive formalisation reads:

```
ax_thoroughgoing_PSR :
  ∀ x y : Thing, x ≠ y → ∃ φ : Thing → Prop, φ x ∧ ¬ φ y
```

But this is provable in Lean: take `φ := fun z => z = x`. The trivial
property "being identical to x" distinguishes any distinct pair. So
this naive formulation is empty: it commits nothing.

A non-trivial formalisation must restrict the predicates. One
candidate restricts to *Spinozistically-significant* properties
(attributes, modes, ontological status), but specifying that
restriction itself requires further metaphysical commitments. Another
candidate restricts to predicates definable from the `EthicaWorld`
primitives, which would make the axiom non-trivial but also
drastically narrows what "every fact" means in Spinoza's intent. A
third candidate restricts to predicates expressible in some logic of
essence or modality, which adds substantial machinery to the
formalisation.

Each of these three non-trivial candidates is a project in itself. We
do not develop them here. The point is methodological: thoroughgoing
PSR is unrefuted by our counter-models, *and* its non-refutation is
substantively correlated with the difficulty of stating it
non-trivially. Della Rocca's prose appeals to thoroughgoing PSR
without constraining it to any particular formal shape; a charitable
formalisation must do that constraining itself, and each constraint
choice is a further interpretive position. We treat thoroughgoing-PSR
formalisation as open future work and invite readers to attempt their
own candidates against the project's counter-models.

## §8.3 Counter-model fidelity caveats

An earlier construction used a design choice, since retired, that
bears recording because it shaped the scope of the strict claim.

(F2, retired) The earlier counter-models set `inAnother x := ¬
isSubstance x`, collapsing Spinoza's three-category ontology
(substances, attributes, modes) into a two-category split and
treating attribute-things as modes. This made A10 — every attribute
is per se conceived, Spinoza Ip10 — unsatisfiable, so those models
could instance only the bare `EthicaWorld` predicate signature, not
the stated-axiom register `StatedAxioms`. The current construction
(§§5.4, 6.4) interprets every element as a substance: A10 together
with A8 (in-itself ↔ per-se-conceived) forces an attribute-thing to
be in itself and per se conceived, hence a substance by Definition
III, so the faithful move is to accept attributes as substances
rather than demote them to modes. With F2 retired the counter-models
satisfy the full `StatedAxioms` register, and the strict claims of
§8.1 hold over Spinoza's stated resources rather than a predicate
signature alone.

Two milder caveats remain.

(F1) `expressesEternalEssence _ := True` is set uniformly. Spinoza's
text restricts the predicate to attributes proper (Definition VI
explanation; Pars II Proposition VIII). The uniform setting
discharges `IsGod`'s fourth conjunct vacuously; it is not the choice
a fully Spinoza-faithful counter-model would make.

(F3) The counter-models contain *no modes* — every element is a
substance — and a substance may be its own attribute or an attribute
of another. Spinoza's intended ontology has modes, and his attributes
are essence-aspects of substance rather than free-standing
substances. The models are therefore "Bennett-line multi-substance
worlds" rather than Spinoza-faithful universes, which is appropriate:
they exist to exhibit configurations Proposition V and Proposition
XIV would forbid.

Neither remaining caveat affects the strict meta-logical claim: the
counter-models satisfy `[StatedAxioms T] + [PSRSubstance T]`
(respectively `[StatedAxioms T] +` plenitude) and falsify A12
(respectively A15). The falsification depends only on the
`intellectPerceivesAsEssence` graph being non-uniform, which the
caveats leave untouched. They bear only on philosophical
appropriateness: a fully Spinoza-faithful counter-model would
restrict `expressesEternalEssence` to attributes proper and populate
the universe with genuine modes. We treat these as opportunities for
refinement in future work.

## §8.4 Sensitivity to the *sive* translation

§3.2 records our adoption of the identifying reading of Latin *sive*
in *ejusdem naturae sive attributi*, following Curley 1985 and the
reading implicit in Della Rocca 2008. Bennett 1984 §17 considers a
disjunctive reading on which "nature" and "attribute" come apart,
Spinoza's *sive* listing two distinct features substances might share
rather than glossing one as the other. Our central claims are
sensitive to this choice, and we record the sensitivity here.

Under the identifying reading, A12 reads (as in §3.3) `∀ s₁ s₂ a,
Attribute a s₁ → Attribute a s₂ → s₁ = s₂`: sharing an attribute
suffices for identity. Under a disjunctive reading, A12 would split
into two clauses: a *sameNature* clause (two substances of the same
nature are identical) and a *sameAttribute* clause (two substances
sharing an attribute are identical), with *sameNature* requiring a
new primitive `sameKind` distinct from shared attribute. Whether the
counter-models of §5–§6 falsify both clauses depends on how `sameKind`
is interpreted: a `sameKind` defined as shared attribute collapses the
readings (A12 reduces to its identifying form); a `sameKind`
independent of attribute would let the counter-models falsify the
*sameAttribute* clause while leaving the *sameNature* clause's status
open.

Two consequences. First, the strict claim S-A12 of §8.1 carries over
to the *sameAttribute* clause of a disjunctive-*sive* formulation:
the same four-element counter-model witnesses irreducibility against
`[StatedAxioms T] + [PSRSubstance T]`. Second, the *sameNature* clause
under disjunctive *sive* would need its own demote experiment, with a
new PSR-flavoured candidate matching the nature-sharing predicate; we
have not carried out this construction. The translation choice
therefore affects scope (which formal regimentation of Proposition V
the strict claim addresses) but not the specific irreducibility
result we establish for the regimentation we adopt. Readers inclined
to a disjunctive-*sive* reading should treat our result as bearing on
the *sameAttribute* fragment of the disjunction; the *sameNature*
fragment is open.

## §8.5 The Garrett-route demote attempt

Garrett 1990's reconstruction (§2.3) is a distinct demote candidate
from Della Rocca's PSR. The Garrett route would replace `PSRSubstance`
with a typeclass committing that Spinoza's "in and conceived through"
relation (ID3 / ID5, together with IA1 / IA2) is strict and total,
strong enough that any difference of modes resolves into a difference
of attributes. Whether such a commitment, formally stated, derives
A12 is an open mechanical question our formalisation supports but
does not develop.

The construction would proceed as the §5 demote did: declare the
strong-Definition-III axiom in a typeclass, attempt the A12 proof,
and if it fails, exhibit a counter-model. We expect the attempt to
succeed for some formulations of the axiom (a sufficiently strong
axiom would derive A12 by definition) and to fail for weaker
formulations. The interesting question, which is the *minimal*
Garrett-route axiom that delivers A12, is itself a research project
we leave to follow-up work.

## §8.6 Other open questions

*Counter-model generality.* The counter-models we construct are ad
hoc, small inductive types built for specific non-derivability
targets. A general framework for Spinoza-flavoured Kripke models
would let demote attempts share machinery, but presupposes a settled
formal account of "Spinoza model" that the demote experiments are
themselves attempting to clarify. We leave the framework question to
future work.

*Finite vs intended cardinality.* Our counter-models have 3 or 4
elements; Spinoza's intended ontology is infinite. The non-derivation
argument does not depend on cardinality (a Lean universal statement
that fails for a finite witness fails *as a universal statement*),
but the philosophical question of whether finite counter-models are
appropriate witnesses for Spinoza's infinite-substance metaphysics
deserves attention. We note the question and defer detailed
treatment.

*Pars II and Pars III.* The formalisation extends only through Pars
I. The mind-body parallelism of Pars II Proposition VII and the
*conatus* doctrine of Pars III may yield further demote experiments
and irreducibility results. Whether the typology we identify
generalises beyond Pars I is an empirical question the formalisation
is positioned to answer through extension.
