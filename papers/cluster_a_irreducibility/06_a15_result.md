# §6 The A15 result and its counter-model

## §6.1 The target axiom A15

A15 is a load-bearing companion clause for Proposition XIV
(*Praeter Deum nulla dari neque concipi potest substantia*).
Formally: `∀ g s a : Thing, IsGod g → Substance s → Attribute a s
→ Attribute a g`. Spinoza's Proposition XIV demonstration uses
A15 implicitly: God has every attribute (Definition VI's
*substantiam constantem infinitis attributis*); any other
substance must therefore share an attribute with God; by A12,
the substance is identical to God. A15 is what makes the "must
therefore share" step go through. Like A12, A15 is currently a
Section III axiom; the demote question is whether it derives
from base axioms plus a Della-Rocca-flavoured PSR-plenitude
commitment.

## §6.2 The demote candidate — A25 + A26

The natural Della Rocca route to A15 is *plenitude*: every
realised substance attribute belongs to *some* god. Combined
with *uniqueness of god*, this delivers A15 (every realised
attribute belongs to *the* god). The candidate Σ for A15 is
therefore a typeclass `PSRPlenitude` with two fields:

```lean
ax_plenitude_attribute :
  ∀ a s : Thing, Substance s → Attribute a s →
    ∃ g, IsGod g ∧ Attribute a g

ax_god_unique :
  ∀ g₁ g₂ : Thing, IsGod g₁ → IsGod g₂ → g₁ = g₂
```

A25 (plenitude) and A26 (god uniqueness). Each is a Section III
commitment in our register. A26 in particular is essentially
Proposition XIV's content stated as axiom, a relocation rather than
a reduction of substantive commitment.

A25 alone is *strictly weaker* than A15: a model with two
distinct gods, each with its own attributes, can satisfy
plenitude (every realised attribute is in some god, namely its
owner) without satisfying A15 (the universality clause across
gods).

## §6.3 The decomposition

With both A25 and A26, A15 derives in three steps:

```lean
theorem prop_A15_demote_via_decomposition
    (g s a : Thing) (hgod : IsGod g) (hs : Substance s)
    (ha : Attribute a s) : Attribute a g := by
  obtain ⟨g', hgod', ha_g'⟩ :=
    PSRPlenitude.ax_plenitude_attribute a s hs ha
  have heq : g = g' :=
    PSRPlenitude.ax_god_unique g g' hgod hgod'
  exact heq ▸ ha_g'
```

A25 produces some god `g'` with the attribute; A26 collapses
`g = g'`; substitution delivers the conclusion.

The proof has the formal shape of a successful demote, but the
philosophical reading is mixed. We have replaced one universality
clause (A15: every god has every realised attribute) with two
commitments (plenitude, an existence claim about realised
attributes; uniqueness, a universality claim across gods). The
total commitment count rises from 1 to 2; the strength of the
commitments does not strictly diminish; A26 in particular is
itself a substantive claim (closely related to but, as §6.5
notes, strictly weaker than Proposition XIV).

This is *decomposition only*: the demote is a relocation of the
commitment across multiple Section III axioms, not a reduction
to weaker principles. Della Rocca's reading would describe this
as "PSR delivers A15 via plenitude and uniqueness, both natural
consequences of PSR-driven monism." Bennett's reading would
describe it as "the universality clause has been replaced by
another universality clause; the substantive commitment is
preserved, just relocated."

## §6.4 The non-derivation from plenitude alone

Plenitude alone (A25 without A26) does not derive A15. The
counter-model is three elements:

```lean
inductive T where
  | g₁ : T
  | g₂ : T
  | attr_g₂ : T
```

All three elements are substances (forced by A10 + A8, as in §5.4);
`g₁` and `g₂` are the two gods, while `attr_g₂` is a
substance-attribute of `g₂` that is not absolutely infinite, hence
not itself a god. The intellect-perception graph has `g₁` perceiving
itself, and `g₂` perceiving itself and `attr_g₂`:

```lean
def perceivesAsEssence : T → T → Prop
  | T.g₁, T.g₁ => True
  | T.g₂, T.g₂ => True
  | T.g₂, T.attr_g₂ => True
  | _, _ => False
```

The model satisfies the stated register `StatedAxioms T` (A1–A7
with the Section I bridges, every field trivial as in §5.4). Both
`g₁` and `g₂` satisfy `IsGod`: each is absolutely infinite, each has
an attribute (itself), and the fourth conjunct (every attribute
expresses eternal essence) is discharged via the uniform
`expressesEternalEssence := True` caveat (§8.3 F1). Each god being
its own attribute-bearer is a self-reference that is
Spinoza-unfaithful (§8.3 F3) but harmless to the meta-logical claim,
since the falsification of A15 depends only on the asymmetric
`attr_g₂` row. Plenitude holds: every realised attribute (`g₁`, `g₂`,
or `attr_g₂`) belongs to some god (`g₁`, `g₂`, or `g₂`
respectively). The non-derivation depends only on the asymmetric
`attr_g₂` row, not on the self-reference witnesses.

A15 fails. Take `g := g₁`, `s := g₂`, `a := attr_g₂`. Then
`IsGod g₁` holds, `Substance g₂` holds, `Attribute attr_g₂ g₂`
holds, but `Attribute attr_g₂ g₁` is false (the perception graph
sends `g₁ × attr_g₂` to false).

The non-derivation argument runs as in §5.4: an assumed
derivation of A15 from plenitude + the stated register would
specialise to this model, yielding `Attribute attr_g₂ g₁`; but the
model proves the negation; so we would derive `False`; the kernel
forbids; no derivation exists.

## §6.5 Discussion: A15's pattern and A26's status

A15 demotes via decomposition while A12 admits only partial
reduction. The structural difference: A12's content has a
single quantifier alternation (∀ s₁ s₂ ∃ a); A15's content has
a triple alternation (∀ g s a). Plenitude breaks A15 into two
simpler clauses (∃ g for plenitude; ∀ g₁ g₂ for uniqueness),
each PSR-tractable; A12's content admits no analogous PSR
decomposition. §7 systematises this distinction.

A26 (god uniqueness), formally
`∀ g₁ g₂, IsGod g₁ → IsGod g₂ → g₁ = g₂`, is a *universal
identity-claim*: a universally quantified statement whose
content is an identity. We refer to it as a *universality* clause
when emphasising its quantifier structure (as in §7's typology,
contrasting it with PSR's existence-explanatory shape) and as an
*identity* clause when emphasising its content (as in the
remainder of this section). Both descriptions refer to the same
formal statement.

A26 is strictly weaker than Proposition XIV. A26 says all gods
are identical; Proposition XIV says all substances are identical
to God. The latter requires that every substance is also a god,
which combines A26 with A15's universality reach across
substances. Stating A26 in the demote attempt is therefore not
stating Proposition XIV as axiom, but A26 remains Section III
strength, asserting a universal identity no base axiom delivers.

The pattern illustrates a methodological subtlety: a
"successful" demote can replace an axiom with one or more new
axioms whose total commitment is no smaller. The Della Rocca
line frames this as illuminating ("A15 was really plenitude
plus uniqueness"); the Bennett line as concealing ("the
substantive work has shifted to uniqueness"). The mechanical
contribution is that the replacement is *visible*: any reader
can inspect `PSRPlenitude` and judge whether the
two-axiom decomposition is more perspicuous than one-axiom A15.

The combined picture: A12 and A15, despite their different
demote outcomes (partial reduction for A12, decomposition for
A15), share a structural feature their counter-models bring to
light. §7 systematises the feature into a four-axiom typology.
