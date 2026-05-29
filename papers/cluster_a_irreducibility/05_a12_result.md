# §5 The A12 result and its counter-model

## §5.1 The target axiom A12

Recall §3.3: A12 (`ax_substanceIdByAttribute`) regiments
Proposition V's content as `∀ s₁ s₂ a : Thing, Attribute a s₁
→ Attribute a s₂ → s₁ = s₂`: a single shared attribute suffices
to force identity. The demote experiment asks whether A12 can
be derived from the base axioms plus a Della-Rocca-flavoured PSR
commitment.

## §5.2 The demote candidate — A22

The candidate Σ for A12 is the typeclass `PSRSubstance`,
introducing axiom A22:

```lean
ax_PSR_substance_distinguishability :
  ∀ s₁ s₂ : Thing,
    Substance s₁ → Substance s₂ → s₁ ≠ s₂ →
      ∃ a, (Attribute a s₁ ∧ ¬ Attribute a s₂) ∨
           (Attribute a s₂ ∧ ¬ Attribute a s₁)
```

A22 is the closest formal regimentation of Della Rocca's
argument: "Non-identities, by the PSR, require explanation, and
the way to explain non-identity is to appeal to some difference
in properties" (Della Rocca 2008, p. 47), specialised to
substance-individuation by the elimination of mode-based and
same-attribute-based individuators (pp. 47–48). A22 says
exactly this: distinct substances differ in at least one
attribute, with the disjunction reflecting that the difference
can be in either direction (one has it, the other doesn't, or
vice versa).

A22 is logically weaker than the *conjunction* A12 + A14 in our
framework: A12 together with A14 (substance has at least one
attribute) entails A22, while A22 does not entail A12, as the
counter-model in §5.4 witnesses. (A12 alone does not entail A22:
in a model with two distinct attribute-less substances, A12 holds
vacuously — no shared attribute forces any identity — while A22
*fails*, since the two substances then have no discriminating
attribute. A14 is what makes the entailment go through: it supplies
an attribute of one substance which, by A12, the other must lack.)
The asymmetry (A12 + A14 →
A22 holds, A22 → A12 fails) is what makes A22 a meaningful
demote candidate. If A12 followed from
A22 + base, then any model satisfying A22 + base would satisfy
A12; that this is not the case will be the substance of §5.4.

## §5.3 The partial reduction

The first thing the demote experiment establishes is positive
for the Della Rocca route: A12 *in a restricted form* does
follow from A22. We prove

```lean
theorem prop_5_demote_via_PSR_all_attributes
    (s₁ s₂ : Thing) (hs₁ : Substance s₁) (hs₂ : Substance s₂)
    (hshare_all : ∀ a, Attribute a s₁ ↔ Attribute a s₂) :
    s₁ = s₂ :=
  Classical.byContradiction fun hne => by
    obtain ⟨a, h⟩ :=
      PSRSubstance.ax_PSR_substance_distinguishability
        s₁ s₂ hs₁ hs₂ hne
    cases h with
    | inl h => exact h.2 ((hshare_all a).mp h.1)
    | inr h => exact h.2 ((hshare_all a).mpr h.1)
```

Six lines of tactic script: assume the substances are distinct;
A22 produces a discriminating attribute; the all-shared
hypothesis says both substances share every attribute, including
this one; the discriminator's "one-side-only" character
contradicts the all-shared hypothesis.

The hypothesis of `prop_5_demote_via_PSR_all_attributes` is
"sharing *every* attribute" — substantially stronger than A12's
"sharing *some* attribute". The proof shows that PSR rules out
indiscernibles in the all-attributes sense: two substances that
agree on every attribute must be identical.

This is Bennett-line-charitable. It confirms that PSR delivers a
substantial fragment of Proposition V's content: the
all-attributes case. The result mechanically tracks Bennett's
own §17 prediction that Spinoza's argument "cannot yield more
than the conclusion that two substances could not have all
their attributes in common" (Bennett 1984, p. 69): Bennett
identified the all-attributes ceiling in prose, and we recover it
at kernel level. The full content of Proposition V, however,
requires more.

## §5.4 The non-derivation

The full content of A12 — sharing *any* one attribute forces
identity — does not derive from A22 + base. We establish this
by constructing a counter-model.

The model is a four-element inductive type:

```lean
inductive T where
  | s₁ : T
  | s₂ : T
  | a_shared : T
  | a_only_s1 : T
```

All four elements are substances. This is forced by the stated
register: A10 (every attribute is per se conceived, Spinoza Ip10)
together with A8 (in-itself ↔ per-se-conceived) require any
attribute-thing to be in itself and per se conceived, hence a
substance by Definition III. The `EthicaWorld T` instance accordingly
sets `inItself` and `perSeConceived` true everywhere (and the
mode-side predicates `inAnother`, `conceivedThroughAnother` false),
so `a_shared` and `a_only_s1` are substances that serve as attributes
of others. The non-trivial assignment is `intellectPerceivesAsEssence`:

```lean
def perceivesAsEssence : T → T → Prop
  | T.s₁, T.s₁ => True
  | T.s₁, T.a_shared => True
  | T.s₁, T.a_only_s1 => True
  | T.s₂, T.s₂ => True
  | T.s₂, T.a_shared => True
  | T.a_shared, T.a_shared => True
  | T.a_only_s1, T.a_only_s1 => True
  | _, _ => False
```

Both `s₁` and `s₂` perceive `a_shared` as their essence, but only
`s₁` perceives `a_only_s1`; each attribute-substance perceives
itself. The shared row makes both `Attribute a_shared s₁` and
`Attribute a_shared s₂` hold (via Definition IV), giving a single
shared attribute between two distinct substances.

The model satisfies the full stated register `StatedAxioms T` —
A1–A7 with the Section I bridges — every field discharging trivially
because the ontological and conceptual predicates are constant and
A10 holds (every element is per se conceived). It also satisfies
`PSRSubstance T`: distinct substances differ in some attribute. Since
every element is a substance, the instance proof discharges all 16
case-pairs (4 × 4) with a `cases x <;> cases y` block; the four
identical pairs reduce to `(hne rfl).elim`, and each of the twelve
distinct pairs supplies a discriminating attribute (for `s₁` versus
`s₂` the discriminator is `a_only_s1`, which `s₁` has and `s₂` lacks;
the self-attributes `a_shared`, `a_only_s1` discriminate the
attribute-substance pairs).

The falsification of A12 on this model is one theorem:

```lean
theorem A12_falsified :
    ∃ x y a : T, Substance x ∧ Substance y ∧
        Attribute a x ∧ Attribute a y ∧ x ≠ y :=
  ⟨T.s₁, T.s₂, T.a_shared,
   ⟨trivial, trivial⟩,
   ⟨trivial, trivial⟩,
   ⟨⟨trivial, trivial⟩, trivial⟩,
   ⟨⟨trivial, trivial⟩, trivial⟩,
   by intro h; cases h⟩
```

`s₁` and `s₂` are substances, `a_shared` is an attribute of
both, and `s₁ ≠ s₂` (by induction on the equality assumption,
since the constructors are distinct).

The model and the falsification together establish the
non-derivation. Suppose, for contradiction, that A12 were
derivable from `[StatedAxioms T] + [PSRSubstance T]`. Specialise
the derivation to our concrete `T` and the available instances.
The result would be a Lean theorem of type
`∀ s₁ s₂ a : T, Attribute a s₁ → Attribute a s₂ → s₁ = s₂`.
(The `Substance` hypotheses one might expect are absorbed by
`Attribute`, since `Attribute a s` carries `Substance s`
constitutively, by Definition IV.) Apply it to the witnesses
provided by `A12_falsified`: we obtain `T.s₁ = T.s₂`. But
`A12_falsified`'s last clause provides `T.s₁ ≠ T.s₂`. So we
derive `False` from the assumed derivability of A12. Lean's
kernel does not admit `False`; therefore no derivation of A12
from `[StatedAxioms T] + [PSRSubstance T]` exists.

## §5.5 Discussion

The result has three components, each of which warrants
separate comment.

*The partial reduction is non-trivial.* PSR-substance is not
empty: it delivers the all-shared-attribute case of Proposition
V. Bennett 1984 §17's verdict that Spinoza's argument "cannot
yield more than the conclusion that two substances could not
have all their attributes in common" (Bennett 1984, p. 69)
applies to the *demonstratio* as a derivation of full A12, not
to the partial form `prop_5_demote_via_PSR_all_attributes`. A
charitable Bennett reading would acknowledge this partial
recovery; an uncharitable one would not. Our formalisation
makes the partial recovery explicit.

*The non-derivation is mechanical.* Bennett's expression of
doubt about Proposition V, that no valid argument from
Spinoza's stated resources is available, receives its first
machine-checked counter-model against the specific Della Rocca
PSR-substance reconstruction (the non-derivability claim itself
a meta-logical consequence of kernel consistency, §4.3). The
strict claim is irreducibility of A12 against `[StatedAxioms T] +
[PSRSubstance T]` — the full stated register (A1–A7 with the
Section I bridges) plus PSR, as §8.1 records. The result does not
apply to alternative PSR commitments (Della Rocca's "thoroughgoing
PSR" remains unrefuted, and indeed unspecified in Della Rocca
2008's prose), nor to alternative reconstructions (Garrett's
strong-Definition-III route is a different demote candidate, not
yet attempted).

*The Spinoza-fidelity caveats apply.* The four-element
counter-model treats every element as a substance (with `a_shared`
and `a_only_s1` as substance-attributes), so it contains no modes,
and it assigns `expressesEternalEssence` uniformly true. Neither
caveat affects the meta-logical claim: the falsification of A12
depends only on the `intellectPerceivesAsEssence` graph, which the
caveats leave untouched. They do, however, bear on the philosophical
interpretation: a Spinoza purist would object that the model has no
genuine modes and that `expressesEternalEssence` is over-applied.
(An earlier construction instead treated the attribute-things as
modes, which left the stated-axiom register unsatisfiable; §8.3
records the retirement of that choice.) We discuss the philosophical
bearing in §8 and treat the caveats as opportunities for refinement
in future work rather than as defects in the present claim.

*The result is a kernel-level test of the Negative-based reply
specifically.* As §2.3 noted in connection with Garrett 2018's
Postscript, A22 regiments the *Negative* aspect of the
substance–mode asymmetry (substance is not in and not
conceived through its modes) by asserting that distinct
substances differ in some attribute, an existence-claim about
discriminator attributes that the Negative aspect makes
available. The partial-reduction theorem is therefore a
kernel-level test of the Negative-based PSR reply to the
Hooker-Bennett and Leibniz-Bennett objections. Garrett 2018's
Postscript argues that the full defence and explanation of the
negative-based reply "effectively requires appeal to" its
positive-based counterpart (Garrett 2018, p. 93); whether a
Positive-based PSR (substance is *in* and *conceived through* its
attributes more strictly than its modes) admits a formal
regimentation reaching A12's full content is open future work.

The combined picture: PSR-substance + base axioms reach the
all-shared-attribute fragment of Proposition V's content; the
wider any-shared-attribute content is irreducible to this
specific PSR commitment. Bennett's doubt is confirmed against
this specific reconstruction; Della Rocca's PSR reconstruction
is vindicated for the all-shared-attribute fragment but not for
the wider content; the residual irreducibility is what §6
replicates for the universality clause of Proposition XIV and
§7 systematises.
