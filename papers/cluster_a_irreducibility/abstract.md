# Abstract

In *A Study of Spinoza's Ethics* (1984, §17), Jonathan Bennett
argues that the demonstration of Proposition V of Spinoza's
*Ethica* contains identifiable invalid moves and that, even
granted those moves, "cannot yield more than the conclusion
that two substances could not have all their attributes in
common" — while Spinoza concludes that they cannot share any.
Bennett doubts that any valid reconstruction is available from
Spinoza's stated resources without importing further
commitments. Michael Della Rocca (*Spinoza*, 2008, ch. 2)
responds that the proposition can be derived if the Principle
of Sufficient Reason (PSR) is committed substantively. The
debate has remained at the level of prose argument for forty
years.

This paper provides the first machine-checked evidence in the
debate. We formalise *Ethica* Pars I in Lean 4, encoding
Bennett's reading of Spinoza's stated axioms as a typeclass and
Della Rocca's substantive PSR as an extension class. The
derivation attempt yields a partial result — substances sharing
all attributes are identical — but cannot reach the full
"sharing-any-attribute → identity" content of Proposition V,
mechanically tracking Bennett's own all-attributes ceiling. A
four-element counter-model satisfying both axiom sets while
falsifying Proposition V's content establishes the
irreducibility against this specific augmentation. A second
counter-model establishes the analogous result for axiom A15, a
load-bearing universality clause for Spinoza's Proposition XIV.
Bennett's diagnosis receives its first kernel-checked
counter-model against the Della-Rocca PSR-substance
reconstruction (the non-derivability claim itself a meta-logical
consequence of kernel consistency); stronger PSR variants and
the broader narrative claim against the full Section I + II +
A1–A7 register remain open as future mechanical projects.
