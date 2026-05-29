# §1 Introduction

## §1.1 The problem

Forty years after Jonathan Bennett's *A Study of Spinoza's Ethics*
(Bennett 1984), the validity of Spinoza's Proposition V of *Ethica*
Pars I remains contested. The proposition reads *In rerum natura non
possunt dari duae aut plures substantiae ejusdem naturae sive
attributi* ("in nature there cannot be two or more substances of the
same nature or attribute"). Bennett's verdict in §17 of his study is
unequivocal: Spinoza's *demonstratio* of Proposition V "involves one
dubious move and one invalid one" (Bennett 1984, p. 67), and the gap
between what is established and what Spinoza claims is one Bennett
"wonders how [Spinoza] could overlook" (p. 69). Even granting the
dubious and invalid moves, Bennett shows, the demonstration "cannot
yield more than the conclusion that two substances could not have
all their attributes in common" (p. 69), while Spinoza's text
concludes that they cannot share *any* attribute. §17 closes by
passing to Proposition XIV: "Spinoza's chief use of p5 is in an
argument which has plenty of other things wrong with it" (p. 70).
§18 opens the analysis of that further argument by characterising
the official monism case as "a poor thing" (p. 70). Bennett stops
short of asserting that no valid reconstruction is possible, but
each candidate reconstruction he considers requires importing
commitments Spinoza has not explicitly made in the Definitions, the
seven Axioms of Pars I, or the propositions established earlier
(Props. I–IV).

The doubt has been disputed. Don Garrett's "Ethics IP5: Shared
Attributes and the Basis of Spinoza's Monism" (Garrett 1990,
reprinted as Garrett 2018, ch. 3, with a Postscript at pp. 91–97
engaging Della Rocca's 2002 article "Spinoza's Substance Monism")
argues that Proposition V can be made to go through by reading
Spinoza's "in and conceived through" relation strongly enough to
collapse mode-individuation into attribute-individuation. Michael
Della Rocca, in his *Spinoza* (Della Rocca 2008, ch. 2), proposes a
more systematic reconstruction: Spinoza's structurally operative use
of the Principle of Sufficient Reason (PSR) is sufficient to derive
Proposition V. On Della Rocca's reading, every fact about Spinozistic
substance has a sufficient reason; if two substances were distinct,
the distinction would itself need a reason; the only available
reason in Spinoza's system is an attribute difference; hence distinct
substances must differ in attributes, which is Proposition V's
content. PSR, on Della Rocca's view, is not tacit but structurally
inseparable from the rationalist principles already operative in
Spinoza's text.

The debate has remained at the level of prose argument. Bennett
holds that making PSR explicit would be a substantive metaphysical
move beyond what Spinoza accepts (Bennett 1984 §18); Della Rocca
holds that PSR is already operative in the text. There has been no
mechanism for adjudication, no way to fix a precise formal reading
of "Spinoza's stated axioms" or "Spinoza plus PSR" and then check
whether Proposition V is or is not derivable.

## §1.2 The mechanical question

This paper introduces a new instrument. We formalise Spinoza's
*Ethica* Pars I in Lean 4, fixing the axiom set in a way that makes
the question *what is derivable from which axioms?* decidable by
Lean's type checker. The formalisation respects the structure of
Bennett's critique: we distinguish between (i) Spinoza's stated
axioms (A1–A7) plus auxiliary bridges that Spinoza demonstrably uses
(A1ₑ for the exclusivity of "in se" / "in alio"; A8–A11 for
parallelism between ontological and conceptual predicates), and (ii)
substantive metaphysical commitments, grouped as a Section III
register, that fill in steps Spinoza's *demonstrationes* leave open.
Della Rocca's PSR enters this register as additional Section III
commitments, declared without separate axiomatic statement in
Spinoza's text but made explicit by us so the derivation question
becomes mechanically posable.

We then attempt to derive Proposition V's content. Encoded as the
Lean axiom A12, the formalisation reads "two substances sharing an
attribute are identical." (The translation of Spinoza's *non possunt
dari duae aut plures … ejusdem naturae sive attributi* into this
shared-attribute form follows the reading common to Bennett, Garrett,
and Della Rocca; we discuss the translation step, including Spinoza's
*sive*, in §3.) The Della Rocca route commits a PSR-flavoured axiom
we label A22, requiring that any two distinct substances differ in
at least one attribute. The formal statements of A12 and A22 are
given in §3.

The result, both *what derives* and *what does not*, is the substance
of this paper.

## §1.3 The result

The derivation succeeds only partially. From A22 plus the base
axioms, we prove the *all-shared-attribute* form of Proposition V:
substances sharing every attribute are identical. The proof runs in
six lines of tactic script. This is itself a non-trivial positive
finding for the Della Rocca route, confirming that PSR delivers a
substantial fragment of Proposition V's content and qualifying
Bennett's verdict that the demonstration fails to establish
Proposition V's full content (Bennett 1984, p. 69).

The full content of Proposition V, that substances sharing *any* one
attribute are identical, does not derive. We establish the
non-derivation through a four-element counter-model in which the base
axioms and A22 hold simultaneously, but where two distinct substances
share an attribute. If A12 in its full form were derivable from these
axioms, the derivation would yield a proof of `s₁ = s₂` on this
model, contradicting the model's explicitly proven `s₁ ≠ s₂`. The
counter-model itself is *kernel-level*: a finite, type-checked
artefact whose `StatedAxioms T` (Spinoza's A1–A7 with the Section I
bridges) and `PSRSubstance T` instances and whose falsifying theorem
are all verified by Lean's trusted core, the minimal type-checker to
which all of Lean's correctness ultimately reduces. The non-derivability claim that follows is *meta-logical*:
granting that Lean's kernel is consistent (§4.3), no derivation of
A12 from these axioms can exist. The non-derivation is therefore
established not by absence-of-proof rhetoric but by a kernel-checked
counter-model plus a one-line meta-argument about kernel consistency.

The result is the first machine-checked evidence in the forty-year
Bennett–Della Rocca debate. Bennett's doubt receives its first
kernel-checked counter-model against one specific reconstruction,
Della Rocca's PSR-substance route. Stronger PSR variants, including
Della Rocca's "thoroughgoing PSR," remain unrefuted; §8 sketches
candidate formal signatures for that thoroughgoing form and the
difficulty of stating it non-trivially. The construction of further
counter-models, or the success of further derivation attempts under
stronger augmentations, is now an open mechanical project rather than
a prose dispute.

We replicate the methodology for axiom A15, a load-bearing companion
clause for Proposition XIV's claim that no substance besides God can
be granted. The result is analogous: A15 does not derive from a
plenitude-flavoured PSR commitment alone. A three-element
counter-model verified at kernel level, together with the same
meta-logical argument from kernel consistency, witnesses the
non-derivability. The decomposition route (plenitude plus
god-uniqueness) succeeds, but at the cost of replacing one
universality clause with another universality clause of equal
commitment strength: relocation, not elimination, of the commitment.

The two non-derivation results, together with two *successful*
derivation attempts for axioms A13 (substance involves existence) and
A14 (substance has at least one attribute), yield a four-axiom
reducibility-profile typology. The two universality clauses (A12,
A15) resist PSR-reduction; the two existence clauses (A13, A14)
translate into PSR-flavoured forms at equal strength. We develop the
typology in §7.

## §1.4 Relation to machine-checked philosophy

Machine-checked methods have been brought to philosophical arguments
before, but not to an *interpretive* dispute of this kind. The closest precedent is the computational-metaphysics
programme. Fitelson and Zalta (2007) mechanise fragments of Zalta's
object theory and use automated reasoners to find and check proofs in
it. Oppenheimer and Zalta (2011) use an automated theorem prover to
discover a one-premise simplification of Anselm's ontological
argument. Benzmüller and Woltzenlogel Paleo (2014) verify Gödel's
ontological argument in higher-order logic, confirming the
consistency of Scott's variant and exhibiting the modal-collapse
worry. These works adjudicate the *validity* of a self-contained
argument: does the conclusion follow from a fixed set of premises?

Our question is different in kind, and the difference is what locates
the contribution. It is interpretive and second-order: not "is this
argument valid?" but "which of the propositions a historical text
asserts are derivable from the resources the text grants itself, and
which encode substantive commitments imported by charitable
reconstruction?" The demote experiment (§4) is the instrument built
for that second-order question, and the Bennett–Della Rocca dispute
over Proposition V is, to our knowledge, the first interpretive
disagreement in the history of philosophy to receive a kernel-checked
adjudication of this form. The novelty we claim is accordingly
specific: not the first machine-checked philosophy, but the first
machine-checked intervention in an interpretive dispute over what a
canonical text's stated axioms do and do not entail.

## §1.5 What the paper does not claim

We do not claim that Bennett's doubt is vindicated in full
generality. The conjecture quantifies over *any* charitable
augmentation of Spinoza's resources; demonstrating its truth in that
generality would require counter-models surviving every candidate
augmentation. The counter-models we construct rule out one specific
augmentation each. They are first-step mechanical evidence on the
Bennett-line position, not closing argument. §8 spells out the scope
of the claims in detail, including the candidate stronger PSR
augmentations not yet tested, and the Spinoza-fidelity caveats in the
counter-model construction that bear on philosophical relevance
without affecting the meta-logical non-derivation claim.

What the paper does claim is that the prose-level dispute over
Proposition V can be replaced, at least in part, by a mechanical
discipline: stating the axioms precisely, attempting derivation, and
constructing counter-models when derivation fails. The forty-year
dispute over what Spinoza's text "really" delivers admits a new
evidence category that neither party can dismiss without engaging the
kernel.

## §1.6 Structure of the paper

§2 gives the textual and interpretive background of the
Bennett–Della Rocca debate. §3 describes the Lean 4 formalisation of
*Ethica* Pars I, including the typeclass design, the Section III
categorisation of substantive commitments, and the translation step
from Spinoza's Latin to the formal axioms. §4 sets out the
demote-experiment methodology and the counter-model discipline. §5
and §6 present the A12 and A15 results respectively. §7 develops the
reducibility-profile typology. §8 discusses scope, limitations, and
open mechanical projects (including thoroughgoing-PSR formal
candidates and Spinoza-fidelity refinements). §9 concludes.

The Lean source is open at
\url{https://github.com/Nakammura/spinoza-ethica-lean}; readers who
wish to verify the counter-models, or to attempt stronger demote
augmentations, can do so against the project's `lake build` target.
