# Abstract

We give the first machine-checked contribution to an *interpretive*
dispute in the history of philosophy: the forty-year disagreement
between Jonathan Bennett and Michael Della Rocca over the
demonstration of Proposition V of Spinoza's *Ethica* Pars I. We formalise *Ethica*
Pars I in Lean 4, encoding Bennett's reading of Spinoza's stated
axioms as a typeclass and Della Rocca's substantive Principle of
Sufficient Reason (PSR) as an extension class, so that the question
*what is derivable from which axioms?* is decided by the kernel. The
derivation attempt yields a partial result, that substances sharing
all attributes are identical, but does not reach the full
"sharing-any-attribute implies identity" content of Proposition V;
it thereby tracks Bennett's own verdict that the demonstration
"cannot yield more than the conclusion that two substances could not
have all their attributes in common," whereas Spinoza's text
concludes that they cannot share *any* attribute. A four-element
counter-model that satisfies both axiom sets — Spinoza's stated
register A1–A7 with its definitional bridges, and the PSR extension —
while falsifying Proposition V's content establishes the
irreducibility against this specific augmentation; a second,
three-element counter-model
establishes the analogous result for axiom A15, a load-bearing
universality clause for Proposition XIV. Each non-derivability claim
is a meta-logical consequence of kernel consistency, witnessed by a
kernel-checked model rather than by the absence of a found proof.
The contribution is twofold: a concrete result, the first
kernel-checked counter-model against Della Rocca's PSR-substance
reconstruction; and a method, the *demote experiment*, that replaces
part of a prose dispute with a checkable discipline. Stronger PSR
variants, and the broader Bennett-line claim against every charitable
augmentation, remain open as mechanical projects.
