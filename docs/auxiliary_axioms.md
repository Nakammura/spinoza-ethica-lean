# Auxiliary Axioms Register — Spinoza's *Ethica* in Lean 4

This document catalogues every auxiliary axiom we have added *beyond*
Spinoza's seven (A1–A7) — in the `Pars1Axioms` and `CausalAxioms`
typeclasses and in the extension typeclasses layered on them
(`TheologiaAxioms`, `MereologyAxioms`, `InherenceAxioms`,
`ConsecutioAxioms`, and the modal-layer classes). Each auxiliary axiom is a commitment we make on
Spinoza's behalf where the source text leaves a step implicit; the
register's purpose is to put those commitments under a spotlight,
not hide them behind a `class`.

The closure protocol in `gaps.md` step 3 requires a corresponding
entry here for any auxiliary axiom introduced to discharge a `GAP`.
This file is the system of record for those entries.

The auxiliary axioms split into three qualitatively distinct
sections. Mixing them in one flat list hides the philosophical
weight differences:

- **Section I — Definitional bridges**. Make explicit the
  definitional or conceptual coextensions Spinoza uses tacitly. The
  commentary literature broadly accepts these are operative in the
  text; we make them machine-checkable. Light commitments.
- **Section II — Substantive promotions of `Pars1Axioms`
  placeholders (A4, A5)**. Promote Spinoza's own A1–A7 from `True`
  placeholders to substantive content within an extended typeclass.
  Currently A4 and A5 are promoted (A1, A2, A7 are already
  substantive in `Pars1Axioms`; A3 / A6 await modal / Pars II
  layers). Medium commitments.
- **Section III — Substantive metaphysical commitments**. Fill
  demonstrably-incomplete steps in Spinoza's *demonstrationes*.
  Commentary literature widely acknowledges these gaps; the axioms
  here are our considered reconstructions. **Heavy** commitments —
  swap a Section III axiom and you change the Spinoza system, not
  just its presentation.

---

# Section I — Definitional bridges

---

## A1ₑ — Exclusivity of *in se* and *in alio*

**Lean signature**:
```lean
ax1_exclusive : ∀ x : Thing, ¬ (inItself x ∧ inAnother x)
```

**Why we add it**: Spinoza's A1 (*Omnia, quae sunt, vel in se, vel
in alio sunt*) uses *vel… vel*, which in classical Latin can be
inclusive or exclusive. The Demonstrationes throughout Pars I
*assume* exclusivity (e.g. Prop. I's disjointness fragment uses it),
but Spinoza never asserts it as a separate axiom.

**Commentary**: We adopt the exclusive reading because the chain
of demonstrations in Pars I (P1, P4, P5) silently requires it.
Bennett 1984 §16 treats this exclusivity as a substantive
metaphysical commitment about ontological categories (substance
vs. mode), not a logical property of *vel*. We make the choice
visible at the axiom layer and document the alternative.

**Used by**: `prop_1_substanceDisjointFromModes`.

**Closes**: GAP-1.

---

## A8 — Ontological–conceptual parallelism (*in se* / *per se*)

**Lean signature**:
```lean
ax_inItself_iff_perSeConceived :
  ∀ x : Thing, inItself x ↔ perSeConceived x
```

**Why we add it**: Def. III ("substance = in se est et per se
concipitur") pairs the ontological clause "in itself" with the
conceptual clause "per se conceived". Spinoza never asserts they
are coextensive; A1 + A2 alone do not force the iff. To prove the
substance/mode partition (Prop. IV), we need the bridge.

**Commentary**: This is a *PSR-flavoured* commitment. Della Rocca
2008 ch. 1–2 makes it constitutive (the Principle of Sufficient
Reason forces ontological dependence to track conceptual
dependence). Curley 1988 ch. 1 treats it as a tacit Spinozistic
principle. **Bennett 1984 §16 explicitly rejects the coextension** —
he argues self-existent items conceived through another are
logically possible and Spinoza simply assumes their absence.
Adopting A8 commits us to the Della Rocca / Curley reading.

**Used by**: `prop_4_partition`.

**Closes**: GAP-4 (in-half).

**Cross-reference (attribute-collapse)**: A8, together with A10,
A12, A14, and A15, feeds `Realitas.lean`'s attribute-collapse
theorem — in any `Pars1Axioms` world with a God, every attribute of
every substance equals that God (`attribute_collapse`). A8's role:
its `.mpr` direction is what upgrades an attribute's "per se
conceived" status (A10) to "in itself", i.e. to substance-hood
(`attribute_is_substance`). Any future revision of the attribute
ontology touching A8 must renegotiate this result — see
`coverage.md`'s "Attribute-collapse result" subsection.

**Update (Attributum session — the renegotiation)**: it has now been
done, in the parallel branch `Ethica/Attributum/` rather than by
touching A8. There A8 keeps its full strength *on things* and simply
has no attribute to apply to: attributes live in a separate type
`Attr`, so `inItself a` is ungrammatical for `a : Attr` and no A8′
exists or can be written. This is precisely Bennett 1984 §16's
position — he declined the A8 coextension for attributes on
philosophical grounds — enforced by typing instead of by an axiom
restriction. A8 itself is unchanged in `Pars1Axioms`. See
`Ethica/Attributum/Core.lean`'s header, the §Attributum section at
the end of this file, and `gaps.md` GAP-25 (✅ closed).

---

## A9 — Ontological–conceptual parallelism (*in alio* / *per alio*)

**Lean signature**:
```lean
ax_inAnother_iff_conceivedThroughAnother :
  ∀ x : Thing, inAnother x ↔ conceivedThroughAnother x
```

**Why we add it**: The mode-side counterpart of A8.

**Commentary**: Same PSR caveat as A8.

**Used by**: `prop_4_partition`.

**Closes**: GAP-4 (alio-half).

### Quiet payoff of A8 + A9

A consequence not separately axiomatised but worth recording:
`perSeConceived` and `conceivedThroughAnother` are mutually exclusive
without a fresh axiom. The argument is one line —
A1ₑ gives `¬ (inItself x ∧ inAnother x)`; transferring through A8
and A9 gives `¬ (perSeConceived x ∧ conceivedThroughAnother x)`. So
introducing A8/A9 spares us a hypothetical "A2ₑ" exclusivity
counterpart for the conceptual side. Documented here so we do not
accidentally re-axiomatise it later.

---

## A10 — Attribute–substance identity-of-conception

**Lean signature**:
```lean
ax_attribute_perSe :
  ∀ a s : Thing, Attribute a s → perSeConceived a
```

**Why we add it**: Spinoza's Prop. X demonstration is one sentence:
"Attributum enim est id quod intellectus de substantia percipit
tanquam ejus essentiam constituens (per def. 4) adeoque (per def. 3)
per se concipi debet." The leap from "substance is per se
conceived" (Def. III) to "the *attribute* is per se conceived"
presupposes that conceiving substance under attribute `a` is
conceiving `a` itself.

**Commentary**: Della Rocca 2008 ch. 2 reads attributes as the
modes of conception under which substance is grasped, making this
identity definitional. Garrett *Spinoza on the Essence of the Human
Mind* treats it similarly. The hypothesis of A10 is the full
`Attribute a s` (which carries `Substance s`) rather than an
arbitrary `intellectPerceivesAsEssence s a`: the latter would be
over-strong, licensing the conclusion on spurious
essence-attributions.

**Used by**: `prop_10_attributePerSe`.

**Closes**: GAP-5.

**Cross-reference (attribute-collapse)**: A10 supplies the
`perSeConceived a` half of `attribute_is_substance`
(`Realitas.lean`) — the first step of the attribute-collapse
theorem (with A8, A12, A14, A15). See A8's cross-reference note
above and `coverage.md`'s "Attribute-collapse result" subsection.

---

## A11 — *Causa sui* clause-equivalence

**Lean signature**:
```lean
ax_causaSui_iff :
  ∀ x : Thing, involvesExistence x ↔ natureRequiresExistence x
```

**Why we add it**: Def. I — *Per causam sui intelligo id cujus
essentia involvit existentiam, sive id cujus natura non potest
concipi nisi existens* — joins two clauses with *sive*. Curley
1985 p. 408 reads *sive* here as *id est*: the second clause
re-expresses the first. We define `causaSui` as the first clause
only; A11 lets us recover the second on demand.

**Commentary**: Encoding `causaSui` as the *conjunction* of both
clauses would be a stronger commitment than *sive = id est* warrants.
The single-clause definition + bridging axiom A11 keeps the
definition aligned with the biconditional reading.

**Used by**: `prop_7_natureRequiresExistence` (corollary of Prop. VII;
the first load-bearing use of A11). Also used in `prop_11_godNecessarilyExists`
and `prop_19_godIsEternal`/`prop_19_attributesAreEternal`
(`Theologia.lean`) — the Prop. XI "aggregation" this entry
originally flagged as future work.

---

## A28 — Nature-requiring-existence implies eternity (Def. VIII bridge)

**Lean signature** (in `TheologiaAxioms`, `Ethica/Pars1/Theologia.lean`):
```lean
ax_natureRequiresExistence_eternal :
  ∀ x : Thing, natureRequiresExistence x → eternal x
```

**Why we add it**: Def. VIII defines eternity as "*ipsam
existentiam, quatenus ex sola rei aeternae definitione necessario
sequi concipitur*" — existence conceived as following necessarily
from the definition alone. The bridge from `natureRequiresExistence`
(already mechanised, Def. I's second clause via A11) to `eternal`
is exactly the definitional unfolding Spinoza performs in Prop.
XIX's *demonstratio* ("*per definitionem 8*"), with no further
argument offered — a Section I definitional bridge in the same
spirit as A8/A9.

**Commentary**: Standard reading; Def. VIII is stated as a
definition and Prop. XIX's demonstration invokes it directly by
citation ("*per definitionem 8*"), so the bridge is textually
explicit rather than reconstructed.

**Used by**: `prop_19_godIsEternal`, `prop_19_attributesAreEternal`
(`Theologia.lean`).

---

## A30 — *Causa sui* + unconstrained implies free (Def. VII bridge)

**Lean signature** (in `TheologiaAxioms`, `Ethica/Pars1/Theologia.lean`):
```lean
ax_causaSui_unconstrained_free :
  ∀ x : Thing, causaSui x → ¬ constrained x → freelyExistent x
```

**Why we add it**: Def. VII: "*libera dicetur ea res, quae ex sola
suae naturae necessitate existit*" — free is what exists "from the
sole necessity of its own nature". `causaSui` supplies the
necessity-of-own-nature half; `¬ constrained` supplies the
"sola/alone" half; A30 composes the two into `freelyExistent`,
following the same definitional-unfolding pattern as A28.

**Commentary**: The composition mirrors Def. VII's own two-clause
structure (existence-clause + the "alone" qualifier), so the
bridge stays close to the text rather than introducing new content.

**Used by**: `prop_17_godIsFree` (`Theologia.lean`).

---

## A39 — Following-absolutely is a way of following

**Lean signature** (in `ConsecutioAxioms`, `Ethica/Pars1/Consecutio.lean`):
```lean
ax_absolute_consecution :
  ∀ x y : Thing, followsAbsolutely x y → followsFrom x y
```

**Why we add it**: `ConsecutioWorld` keeps two consecution
primitives — `followsFrom` ("*ex necessitate naturae ejus
sequitur*") and `followsAbsolutely` (Prop. XXI's "*ex absoluta
natura … sequi*"). "*Absoluta natura*" specialises, and never
contradicts, bare "*natura*": whatever follows from the absolute
nature of a thing follows, full stop, from the necessity of that
thing's nature. A39 records the definitional relationship between
the two primitives — the same light-commitment role as A8/A9/A28.

**Commentary**: This is not a further metaphysical commitment; it
is what "absolute" *means* in Prop. XXI's contrast with Prop.
XXII's "*quatenus modificatum*" (following via a modification).
No commentator reads the two as independent relations.

**Used by**: available for downstream chaining of Prop. XXI's
consequents into `followsFrom`-consuming results (e.g. combining
with A38 to get causation from absolute consecution); not yet
load-bearing in a mechanised proposition.

---

# Section II — Substantive promotions of `Pars1Axioms` placeholders (A4, A5)

---

## A4ₛ — Effect intelligible through cause (*substantive form of A4*)

**Lean signature** (in `CausalAxioms`):
```lean
ax4_effectIntelligibleThroughCause :
  ∀ c e : Thing, Cause c e → intelligibleThrough e c
```

**Why we add it**: A4 in `Pars1Axioms` is a `True : Prop`
placeholder; the real epistemic content needs the `Cause` and
`intelligibleThrough` primitives introduced in `CausalWorld`.

**Commentary**: A separate `ax3_causeGroundsIntelligibility` field
would carry literally the same Lean signature, so it is omitted;
A3's distinct *ontological-necessitation* content awaits the modal
layer (tracked as GAP-7).

**Used by**: `prop_3_noCommonNoCause`.

---

## A5ₛ — No common nature, no intelligibility (*substance-restricted*)

**Lean signature** (in `CausalAxioms`):
```lean
ax5_noCommonNoIntelligibility :
  ∀ x y : Thing, Substance x → Substance y →
    ¬ sameNature x y → ¬ intelligibleThrough x y
```

**Why we add it**: Spinoza's A5 ("things sharing nothing in common
cannot be understood through one another") in its general form,
combined with the GAP-2 closure that derives `sameNature` from
`Attribute` (hence implicitly substance-only), would force
`¬ Cause m₁ m₂` for every pair of modes — collapsing the
finite-mode causation Pars II–V depend on. The substance-restricted
form preserves Prop. III's substance-side use while leaving
mode-causation expressible.

**Commentary**: The substance-restriction is a soundness fix. The
fully general A5 will be reinstated at the modal layer, where a
separate `hasAttribute : Thing → Thing → Prop` relation will give
`sameNature` proper coverage over modes as well.

**Used by**: `prop_3_noCommonNoCause`.

**Closes**: the GAP-2 soundness regression (restricting A5ₛ to
substances so that finite-mode causation survives).

---

## A29 — Attributes of a substance involve existence

**Lean signature** (in `TheologiaAxioms`, `Ethica/Pars1/Theologia.lean`):
```lean
ax_attribute_involvesExistence :
  ∀ a s : Thing, Attribute a s → involvesExistence a
```

**Why we add it**: Prop. XIX's *demonstratio* argues that the
attributes of God "express existence" — each attribute expresses
the eternal essence of substance (Def. VI) and substance's essence
involves existence (Prop. VII, i.e. A13); the transfer of
`involvesExistence` from substance to its attributes is used by
Spinoza without separate statement. This is a substantive
promotion of that usage to kernel-usable form, not a definitional
unfolding — the transfer from *substance* involving existence to
*attribute* involving existence is not forced by Defs. III/IV
alone.

**Commentary**: Standard reading (Curley 1985, Della Rocca 2008):
attributes just *are* substance's essence expressed under different
conceptions (compare A10's identity-of-conception reading), so
whatever holds of substance's essence transfers to its attributes.

**Used by**: `prop_19_attributesAreEternal` (`Theologia.lean`).

---

## A31 — No substance is constrained

**Lean signature** (in `TheologiaAxioms`, `Ethica/Pars1/Theologia.lean`):
```lean
ax_substance_not_constrained : ∀ s : Thing, Substance s → ¬ constrained s
```

**Why we add it**: Constraint (Def. VII) is determination *by
another*. A substance cannot be produced/determined by another
substance (Prop. VI); determination by modes is excluded by the
priority of substance over its affections (Prop. I). Spinoza uses
this composite without separate argument in Prop. XVII's
*demonstratio* ("*nulla res extra ipsum*"). The mode-side exclusion
outruns what Prop. I's mechanised disjointness fragment
(`prop_1_substanceDisjointFromModes`) delivers — full priority
needs GAP-6's `conceptualDep` machinery — hence this is a Section
II substantive promotion rather than a derivation from what is
currently mechanised.

**Commentary**: Standard reading; the composite (no substance-side
determination via Prop. VI, no mode-side determination via Prop. I
priority) is exactly what Spinoza's demonstration cites, just not
fully re-derivable from the base layer's current mechanised
fragments.

**Used by**: `prop_17_godIsFree` (`Theologia.lean`).

---

## A33 — Every mode is in some substance (Def. V promotion)

**Lean signature** (in `InherenceAxioms`, `Ethica/Pars1/Inherence.lean`):
```lean
ax_mode_inheres_in_substance :
  ∀ x : Thing, Mode x → ∃ s, Substance s ∧ inheresIn x s
```

**Why we add it**: Def. V calls modes "*substantiae affectiones,
sive id quod in alio est*" — affections OF SUBSTANCE. The unary
`inAnother` clause used to define `Mode` (Def. V's left conjunct)
does not by itself say the "*alio*" a mode is in is a *substance*;
Spinoza's usage throughout — especially Prop. XV's *demonstratio*
("*Modi autem [...] sine substantia nec esse nec concipi
possunt*") — treats it as such without separate argument. A33
promotes that usage to a kernel-usable binary axiom, using the new
`inheresIn : Thing → Thing → Prop` primitive introduced in
`InherenceWorld` (the binary form of Def. V's "*in alio esse*").

**Commentary**: Standard reading; no commentator disputes that
Spinoza's modes are modes *of substance* specifically, but the
formal step from unary `inAnother` to a substance-typed binary
relation is not forced by Defs. III/V alone.

**Used by**: `prop_15_allInGod` (`Inherence.lean`).

---

## A34 — Inherence entails causation (Curley 1969 reading)

**Lean signature** (in `InherenceAxioms`, `Ethica/Pars1/Inherence.lean`):
```lean
ax_inherence_causation :
  ∀ x y : Thing, inheresIn x y → Cause y x
```

**Why we add it**: The bridge from "x is in y" to "y causes x" is
exactly Curley's celebrated reading of Spinoza's "in" (Curley 1969,
*Spinoza's Metaphysics*: to be in God is to be caused by God).
Spinoza himself licenses the move in Prop. XVIII's *demonstratio*:
"*omnia quae sunt, in Deo sunt [...] adeoque [...] Deus rerum quae
in ipso sunt, est causa*" — "are in" is used to conclude "is the
cause of". Without this bridge, Prop. XVIII's "*causa immanens*"
would have no causal content at the level this layer works.

**Commentary**: Curley's reading is influential but not universally
accepted as the *sole* content of "in" — some commentators read
Spinozistic inherence as broader than strict efficient causation.
We adopt Curley's reading because it is the reading that makes
Prop. XVIII's causal conclusion follow from its "in" premises, as
the *demonstratio* itself does.

**Used by**: `prop_18_godImmanentCause` (`Inherence.lean`).

**Redundancy note (post-Consecutio)**: A34 is now **derivable**
from A37 + A38 — `inheresIn x y → followsFrom x y` (A37) chains
with `followsFrom x y → Cause y x` (A38) to give A34's exact
content. A34 is nonetheless **retained** as its own
`InherenceAxioms` field for backward compatibility: existing
proofs (`prop_18_godImmanentCause` et al.) consume it directly
without going through the consecution layer, and `InherenceAxioms`
must remain instantiable without a `ConsecutioWorld` structure.
The redundancy is intentional and recorded here per A38's
docstring; readers counting independent commitments should count
A34 *or* A37+A38, not both.

---

## A36 — Every mode is constrained (Def. VII second-clause promotion)

**Lean signature** (in `InherenceAxioms`, `Ethica/Pars1/Inherence.lean`):
```lean
ax_mode_constrained :
  ∀ x : Thing, Mode x → constrained x
```

**Why we add it**: Def. VII: "*coacta [...] quae ab alio
determinatur ad existendum et operandum*" — the constrained is
what is determined *by another* to exist and to act. A mode, being
in another and conceived through another (Def. V), is determined
by that other in just this sense; Spinoza deploys the reading
without separate argument in the demonstrationes of Props. XXVI
and XXIX ("*Res quae [...] determinata est*" / "*determinata
sunt*"). The action-clause half of Def. VII ("*ad operandum*")
awaits Pars II's action machinery (the GAP-9 family, already
flagged for `Free`/`Constrained` in `Definitions.lean`); what is
committed here is the existence-clause fragment.

**Commentary**: Standard reading of the mode/substance asymmetry;
the restriction to the existence-clause keeps the commitment
honest about what Def. VII's second clause actually needs versus
what awaits Pars II.

**Used by**: `prop_26_modesDeterminedByGod` (partial),
`prop_29_nothingContingent` (mode case), both in
`Inherence.lean`.

---

## A37 — Inherence entails consecution (Della Rocca unified-dependence reading)

**Lean signature** (in `ConsecutioAxioms`, `Ethica/Pars1/Consecutio.lean`):
```lean
ax_inherence_consecution :
  ∀ x y : Thing, inheresIn x y → followsFrom x y
```

**Why we add it**: The XV→XVI move. Spinoza glides between "*in
Deo est*" (Prop. XV's inherence) and "*ex necessitate divinae
naturae sequitur*" (Prop. XVI's consecution) without separate
argument across the demonstrationes of Props. XVI–XVIII — compare
Prop. XVIII's *demonstratio*, which moves from "*in Deo sunt*"
straight to a causal conclusion via Prop. 16 Cor. I, treating the
two as interchangeable. A37 makes the bridge from `inheresIn` to
`followsFrom` a visible commitment rather than an unstated
identification.

**Commentary**: Della Rocca 2008 ch. 2 reads inherence, causation,
and consecution as facets of one underlying conceptual-dependence
relation — A37 (with A38) is that unified reading committed
axiomatically. Readers who keep the three relations genuinely
distinct would have to supply Prop. XVI some other way.

**Used by**: `prop_16_modesFollowFromGod` (`Consecutio.lean`) —
the qualitative clause of Prop. XVI.

---

## A38 — Consecution entails causation (Prop. XVI Cor. I's move)

**Lean signature** (in `ConsecutioAxioms`, `Ethica/Pars1/Consecutio.lean`):
```lean
ax_consecution_causation :
  ∀ x y : Thing, followsFrom x y → Cause y x
```

**Why we add it**: Prop. XVI Corollary I's move: from "*ex
necessitate divinae naturae … sequi debent*" Spinoza concludes
"*Deum omnium rerum … esse causam efficientem*" — consecution
entails efficient causation, without further argument. We commit
to that entailment directly.

**Commentary**: The other half of the Della Rocca
unified-dependence reading (see A37). Together A37 + A38 subsume
A34's content — see A34's redundancy note above: A34 is retained
for backward compatibility, and independent-commitment counts
should include A34 *or* A37+A38, not both.

**Used by**: `prop_16_cor1_godEfficientCause`,
`prop_36_nothingWithoutEffect` (converting A43's consecution
content into the causal form), both `Consecutio.lean`.

---

# Section III — Substantive metaphysical commitments

The Section III register has grown across the project's lifetime
to ~19 commitments. Sub-categorisation by role:

- **§III.A** — Base `Pars1Axioms` Section III commitments (A12,
  A13, A14, A15). The four substantive metaphysical claims that
  fill demonstratio gaps in Spinoza's text.
- **§III.A′** — Extension-typeclass base-layer commitments (A27,
  A32, A35, A40–A43, and now A44). Same weight and role as §III.A,
  but committed in typeclasses extending `Pars1Axioms`
  (`TheologiaAxioms`, `MereologyAxioms`, `InherenceAxioms`,
  `ConsecutioAxioms`, `ClassificatioAxioms`) rather than in
  `Pars1Axioms` itself.
- **§III.B** — Modal-layer conceptual asymmetry candidates (A16,
  A17). The Prop. I priority asymmetry between substance and
  mode dependence.
- **§III.C** — Modal-layer PSR demote axioms (A22-A26). PSR-
  flavoured commitments introduced for the demote-attempt
  experiments. These have a **recursive role**: they are
  Section III axioms introduced *to derive* §III.A axioms — and
  the demote outcome documents whether the derivation is a
  reduction (Della Rocca line) or a relocation / partial-fail
  (Bennett line).

A note on the structural adjacency of A14 and A15:

A14 (`∀ s, Substance s → ∃ a, Attribute a s`) and A15
(`∀ g s a, IsGod g → Substance s → Attribute a s → Attribute a g`)
are structurally adjacent — both are claims about substances and
attributes — and easy to conflate in prose discussion. The
mechanical separation:

- A14 is **existence over attributes** (`∃ a`): each substance
  has *at least one* attribute. PSR-flavoured existence axioms
  demote it cleanly (see A24).
- A15 is **universality over attributes**: every god has *every*
  realised attribute. PSR-flavoured axioms cannot reach this on
  their own — see A25/A26 and the counter-model in
  `Ethica/Pars1/Models/Counterexamples.lean`.

Whenever Spinoza commentary discusses "Spinoza's commitment to
substance having attributes", clarify which of A14 or A15 is
meant.

---

## §III.A — Base `Pars1Axioms` commitments

---

## A12 — Indiscernibility of substance by attribute

**Lean signature**:
```lean
ax_substanceIdByAttribute :
  ∀ s₁ s₂ a : Thing, Attribute a s₁ → Attribute a s₂ → s₁ = s₂
```

**Why we add it**: This is, in essence, the content of Prop. V
("In nature there cannot be two substances of the same attribute")
adopted as an axiom rather than derived. We do this **because
Spinoza's *demonstratio* of Prop. V is widely held in the commentary
literature to be invalid or incomplete as it stands**, and the
additional commitment required to make it work cannot be hidden
inside a "derivation" without dishonesty.

The hypothesis is the full `Attribute a s` in both arguments
(which carries `Substance s`); the redundant `Substance s₁`,
`Substance s₂` hypotheses are dropped — same hygiene as A10.

**Commentary**:
- *Bennett 1984 §17* identifies "one dubious move and one invalid
  one" in Prop. V's demonstration (p. 67) and shows it can deliver
  at most the all-shared-attribute case (p. 69), not the
  any-shared-attribute case Spinoza announces.
- *Garrett 1990 ("Ethics IP5: Shared Attributes and the Basis of
  Spinoza's Monism")* argues that Prop. V holds under a strong
  reading of Definition III together with ID5 / IA1 / IA2; this
  combination is not entailed by the literal text of Spinoza's
  stated definitions and axioms.
- *Della Rocca 2008 ch. 2* rescues Prop. V via the Principle of
  Sufficient Reason (PSR), but PSR itself must be committed as an
  axiom; the rescue is a **relocation, not an elimination**, of
  the commitment.

We choose to commit visibly at the axiom layer rather than via
PSR-flavoured axioms strewn through a modal-layer derivation. The
Bennett–Della Rocca debate is preserved in the commentary record;
A12 represents Spinoza-as-Della-Rocca-reads-him.

**Caveat — downstream consequences**: A12 dramatically shortens the
proofs of Props. VI and XIV. Specifically:
- Prop. VI ("substance cannot be produced by another") follows in
  a few lines via Prop. III contrapositive + A12.
- Prop. XIV ("besides God, no substance") needs A12 *together with*
  a substantive form of Def. VI's "infinitis attributis" clause
  (currently weakened — GAP-8). Without GAP-8 closed, Prop. XIV
  cannot be proved from A12 alone.

This is not a bug — it reflects Della Rocca's PSR-driven reading
that Pars I propositions V–XIV are consequences of a single deep
commitment (indiscernibility-by-attribute) plus the cardinality
content of Def. VI. Readers preferring Bennett's reading (in which
Prop. V should not hold without further argument) can drop A12 to
recover that alternative.

**Used by**: `prop_5_uniqueSubstancePerAttribute`,
`prop_6_substanceNotProducedByAnother` (transitively),
`prop_8_substanceIsNotFinite`,
`prop_14_onlyGodIsSubstance` (via `private axiom` skeleton premises;
see Propositions.lean and GAP-8 / GAP-13 in `gaps.md`).

**Closes**: Prop. V mechanisation gap.

**Related GAP**: GAP-11 — modal-layer derivation of A12. Tracked
but **not guaranteed to succeed**: the Bennett line of commentary
holds that no such derivation is available within Spinoza's stated
axioms; closing GAP-11 may itself require a further axiom
(PSR or substance plenitude), in which case A12 stays in the
register permanently.

**Counter-model bench**: see
`Ethica/Pars1/Models/TwoSubstance.lean` for a model that exercises
A12 non-trivially (single-substance Unit model satisfies A12
vacuously and so cannot witness the axiom's bite).

**Cross-reference (attribute-collapse)**: A12 supplies the final
identification step of `attribute_collapse` (`Realitas.lean`) —
once an attribute-of-an-attribute is handed to God via A15, A12
identifies the original attribute with God. Joint with A8, A10,
A14, A15. See A8's cross-reference note above and `coverage.md`'s
"Attribute-collapse result" subsection.

---

## A13 — Substance involves existence

**Lean signature**:
```lean
ax_substance_involves_existence :
  ∀ s : Thing, Substance s → involvesExistence s
```

**Why we add it**: This is the content of Prop. VII
("Ad naturam substantiae pertinet existere") committed at the axiom
layer. Spinoza's *demonstratio* of Prop. VII chains Prop. VI
corollary with an unstated PSR-flavoured commitment, and both
links carry gaps:

- Prop. VI corollary's mode-extension. The corollary asserts that
  substance cannot be produced by anything (substances + modes
  exhaust the ontology, by A1 + Defs III/V, hence both cases must
  be ruled out). Spinoza rules out the substance case via Prop. VI
  proper. The mode case is asserted but not actually demonstrated
  in the *corollarium*. The *aliter* (alternative argument) appeals
  to A4 + Def. III, but requires a conceptual-uniqueness bridge
  ("if `x` is intelligible through `y ≠ x`, then `x` is not per se
  conceived") that we have not axiomatised — and adding such a
  bridge is itself a substantive commitment, not a definitional
  one.
- The "no external cause ⇒ self-caused" step. Even granted the
  corollary, deriving `causaSui` requires that *some* explanation
  for substance's existence is mandatory; this is the Principle of
  Sufficient Reason move (Della Rocca 2008 ch. 2).

**Commentary**:
- *Bennett 1984 §18* finds Prop. VII's *demonstratio* relying on
  the same kind of unstated commitments that flaw Prop. V's, with
  the gap closed only by reading Prop. VI corollary in its
  strongest form.
- *Della Rocca 2008 ch. 2* uses PSR to derive Prop. VII; PSR itself
  must then be axiomatised (mirroring the A12 situation).

We adopt A13 as the visible Section-III commitment that
encapsulates these tacit moves. Combined with A11 (causa-sui clause
equivalence), the *natureRequiresExistence* form of Def. I is
recovered on demand, and `causaSui s` follows directly for any
substance.

**Caveat — downstream consequences**: A13 makes Prop. VIII (every
substance is not finite-after-its-kind) provable via A12 + Def. II
+ A13; Prop. XI ("God necessarily exists") will require A13
together with the cardinality content of Def. VI (GAP-8) — Prop. XI
is what *aggregates* A13 into the unique necessarily-existent
absolutely-infinite substance.

**Used by**: `prop_7_existenceBelongsToSubstance`,
`prop_7_natureRequiresExistence` (via A11),
`prop_7_substanceIsCausaSui`, `prop_8_substanceIsNotFinite`
(transitively through A12).

**Closes**: Prop. VII mechanisation gap. First load-bearing use of
A11 (which previously had `Used by: not yet used`).

**Related GAP**: GAP-12 — modal-layer derivation of A13 from a
substantive PSR + the substantive A3/A4 of `Causation.lean`. Same
Bennett-honest scoping as GAP-11: derivation is not guaranteed; if
PSR itself must be axiomatised, A13 stays in Section III
permanently.

---

## A14 — Substance has at least one attribute

**Status**: ✅ **promoted**. Now a `Pars1Axioms` field
(`ax_substance_has_attribute`).

**Lean signature**:
```lean
ax_substance_has_attribute :
  ∀ s : Thing, Substance s → ∃ a, Attribute a s
```

**Why we add it**: Spinoza's Defs. III + IV do not entail that
every substance has an attribute (without A14, an attribute-free
substance was a model of `Pars1Axioms`). But Spinoza's *usage*
throughout Pars I treats the existence of attributes as
constitutive of substance. `prop_14`'s demonstration cannot start
without `∃ a, Attribute a s` for the substance `s`.

**Commentary**: Della Rocca 2008 takes this for granted under PSR;
Bennett 1984 §17 treats it as an independent commitment.

**Used by**: `prop_14_onlyGodIsSubstance`.

**Closes**: GAP-13.

**Bench note**: `Ethica/Pars1/Models/TwoSubstance.lean` *satisfies*
A14 — each element is its own attribute, so `∃ a, Attribute a s`
holds for both substances. **A14 is therefore not the cause of
TwoSubstance's loss of `Pars1Axioms` instance**; that loss is
incurred entirely on A15 (next entry). This matters for the
Bennett-line reading: Bennett rejects the *universality* clause
(A15) but does not necessarily reject the *existence* clause
(A14), so the philosophical geography of the two axioms — and
their migration costs — is distinct.

**Redundancy note**: A14 makes `IsGod`'s third conjunct
(`∃ a, Attribute a g`) **logically redundant** under any
`[Pars1Axioms Thing]` context — `Substance g` (first conjunct of
`IsGod`) plus A14 derive the third conjunct directly. The clause
is retained at the `Definitions.lean` layer for textual fidelity
to Spinoza's *substantia constantem … attributis* and to keep
`IsGod` self-contained at the `[EthicaWorld Thing]` level (no
hidden dependency on `Pars1Axioms`). See `coverage.md` Def. VI
row.

**Related GAP (Bennett-honest scoping)**: As with A12 and A13, the
modal-layer route to demote A14 from axiom to theorem is **not
guaranteed to succeed**. Della Rocca's PSR-driven derivation
(see GAP-13's Resolution path) requires (i) committing PSR and
(ii) bridging `intelligibleVia` to `Attribute` constitutively;
both are themselves substantive commitments. If the Bennett line
is correct, A14 stays in Section III permanently — the commitment
relocates rather than dissolves. We track the attempt; we do not
promise it closes.

**Cross-reference (attribute-collapse)**: A14 supplies
`attribute_is_substance`'s attribute-of-an-attribute witness in
`Realitas.lean`'s `attribute_collapse` theorem (step 4 of the
collapse's five-step chain). Joint with A8, A10, A12, A15. See A8's
cross-reference note above and `coverage.md`'s "Attribute-collapse
result" subsection.

---

## A15 — God has every substance's attribute (substantive Def. VI)

**Status**: ✅ **promoted**. Now a `Pars1Axioms` field
(`ax_IsGod_has_attribute_of`). Closes GAP-8b. Cardinality (GAP-8a)
remains separately tracked.

**Lean signature**:
```lean
ax_IsGod_has_attribute_of :
  ∀ g s a : Thing, IsGod g → Substance s → Attribute a s →
    Attribute a g
```

**Why we add it**: Def. VI defines God as a substance *constantem
infinitis attributis* — consisting of *infinitely many*
attributes. The full universal-attribute clause ("God has *every*
attribute") is what Prop. XIV requires, and is not captured by
`IsGod g`'s `∃ a, Attribute a g` clause (that only ensures
non-vacuity).

The cardinality form — "infinitely many" — is a separate concern
(GAP-8a, separately tracked); this axiom captures only the
*universality over substance attributes* (GAP-8b), which is what
`prop_14` actually consumes.

**Commentary**: Standard reading in Curley 1985, Della Rocca 2008.
Bennett 1984 §18 flags the universality clause as a substantive
metaphysical commitment in its own right.

**Used by**: `prop_14_onlyGodIsSubstance`. **Whether
`prop_11_GodNecessarilyExists` will also need A15 depends on
which of Bennett 1984 §18's four reading paths is mechanised** —
the *reductio-via-PSR* path uses A15, while the *causa-sui-direct*
and *power-based* paths do not (they require different additional
commitments; A16-candidate territory). Tracked in `coverage.md`'s
Prop. XI critical-path note.

**Closes**: GAP-8b (universality clause). GAP-8a (cardinality)
remains separately tracked — see `gaps.md`'s split treatment of
GAP-8.

**Related GAP (Bennett-honest scoping)**: The modal-layer route
to demote A15 is **not guaranteed**. Della Rocca's reading derives
universality from PSR + Spinoza's plenitude principle; both are
substantive metaphysical commitments. Bennett 1984 §18 holds that
universality cannot be derived from Spinoza's stated axioms. If
Bennett is correct, A15 stays in Section III permanently. We track
the attempt without promising it closes.

**Counter-bench**: `Ethica/Pars1/Models/TwoSubstance.lean`
provides a Bennett-style multi-substance world where A15 is
**falsified**. Because A15 is a `Pars1Axioms` field, that model
cannot carry a `Pars1Axioms` instance — the failure lives at the
type level. The falsification theorem `twosubst_falsifies_A15`
documents the concrete content of A15's commitment.

**Cross-reference (attribute-collapse)**: A15 supplies the final
transfer step of `attribute_collapse` (`Realitas.lean`) — handing
an attribute's own attribute to God, which A12 then uses to
identify the original attribute with God. Joint with A8, A10, A12,
A14; the consequence is that Def. VI's *infinitis attributis*
clause is unsatisfiable for any God in the register
(`def6_infinitis_attributis_unsatisfiable`). Any future revision of
the attribute ontology touching A15 — or any of A8/A10/A12/A14 —
must renegotiate this result; see `coverage.md`'s
"Attribute-collapse result" subsection and `gaps.md` GAP-25.

**Update (Attributum session — the renegotiation)**: done, without
touching A15. In `Ethica/Attributum/` the axiom is re-typed verbatim
as A15′ (`ax_IsGod_has_attributum_of`, attribute argument in `Attr`)
and its "final transfer step" role simply evaporates: with step 3 of
the chain (`attribute_is_substance`) ungrammatical, there is no
attribute-of-an-attribute to transfer. A15′ then does only the work
Spinoza asks of it, and
`Models/InfiniteAttribute.lean` satisfies Def. VI's *infinitis
attributis* clause outright (`inf_def6_recovered`) with A15′ in
force. See the §Attributum section below.

---

## §III.A′ — Extension-typeclass base-layer commitments (A27, A32, A35, A40–A44)

Unlike A12–A15, these eight live in typeclasses that *extend*
`Pars1Axioms` (`TheologiaAxioms`, `MereologyAxioms`,
`InherenceAxioms`, `ConsecutioAxioms`, `ClassificatioAxioms`)
rather than in `Pars1Axioms` itself — they are committed for their
own downstream propositions and are not prerequisites for anything
mechanised before their respective extension sessions. They share
§III.A's weight (heavy, demonstrably-incomplete-step-filling
commitments) and are catalogued here for that reason, kept
typographically distinct from A12–A15 to preserve the historical
record of what was in `Pars1Axioms` at v1.0.0.

**Irreducibility parity**: all three axioms of the first extension
batch (A27, A32, A35) now carry kernel-level irreducibility
witnesses (`Models/NoGod.lean`, `Models/CounterexamplesII.lean`),
each against a baseline **stronger** than the paper's
`StatedAxioms` register — see the individual entries. The
Consecutio batch's 📜-pattern axioms (A40–A43) and the Classificatio
batch's A44 do not yet have dedicated counter-models; their Section
III status rests on the demonstratio-gap grounds documented per
entry. A44 is additionally distinguished from A40–A43 by being
**demotable**: `Classificatio.lean` shows A42 (itself 📜-pattern)
is an equal-strength decomposition once A44 is granted — see A42's
and A44's entries below.

---

## A27 — God exists ("Deus datur")

**Lean signature** (in `TheologiaAxioms`, `Ethica/Pars1/Theologia.lean`):
```lean
ax_god_exists : ∃ g : Thing, IsGod g
```

**Why we add it**: This is the *instantiation* commitment of the
ontological argument. Spinoza's *demonstratio* of Prop. XI (the
reductio: "*Si negas, concipe, si fieri potest, Deum non existere.
Ergo (per axioma 7) ejus essentia non involvit existentiam. Atqui
hoc (per propositionem 7) est absurdum*") moves from *conceptual*
necessity (essence involves existence — a conditional established
by Prop. VII, i.e. A13, for anything that *is* a substance) to
*instantiation* (some thing in the domain is God). That step is
exactly the gap Gassendi and later Kant pressed against ontological
arguments: Prop. VII yields "IF g is a substance THEN its essence
involves existence", but nothing in A1–A15 puts a God-satisfying
element in the domain.

**Commentary**: Bennett 1984 §18 catalogues four reading paths
through the *demonstratio* (causa-sui direct; reductio via PSR;
power-based; *a posteriori* in the scholium); each needs at least
one commitment beyond the stated axioms. A27 is the minimal direct
form of that missing commitment, adopted visibly rather than
smuggled through a chain of PSR-flavoured moves.

**Why it cannot be derived**: `Models/NoGod.lean` supplies the
kernel-level irreducibility witness — a one-element world
(`NoGodThing`) satisfying ALL of `Pars1Axioms` (A1–A15, including
the Section III commitments A12–A15) with `absolutelyInfinite`
uniformly `False`, so `IsGod` is unsatisfiable there
(`noGodWorld_hasNoGod`, `A27_falsified`). Any Lean derivation of
`∃ g, IsGod g` from `Pars1Axioms` alone would specialise to this
model and yield `False`; hence no such derivation exists. This
baseline is **stronger** than the paper's A12/A15 counter-models in
`Models/Counterexamples.lean`, which run against `StatedAxioms`
(without the Section III commitments) only — A27's irreducibility
is machine-checked even after granting every other Section III
commitment the project has made.

**Used by**: `prop_11_godNecessarilyExists`, `prop_11_godIsCausaSui`
(`Theologia.lean`).

**Consistency witness**: `Models/GodWorld.lean` — `TheologiaAxioms
Unit`, reusing `SingleSubstance`'s `Unit` model (already interprets
its unique element as absolutely infinite).

---

## A32 — A proper part of a substance is a same-nature rival substance

**Lean signature** (in `MereologyAxioms`, `Ethica/Pars1/Mereology.lean`):
```lean
ax_substancePart_sameNatureSubstance :
  ∀ s p : Thing, Substance s → properPart p s →
    Substance p ∧ sameNature p s ∧ p ≠ s
```

**Why we add it**: Spinoza's *demonstratio* of Prop. XII runs a
dilemma on a hypothesised division of substance into parts: either
(i) the parts *retain* the nature of the substance — in which case
two or more substances of the same nature would exist, absurd per
Prop. V — or (ii) the parts do *not* retain that nature — in which
case the substance could lose its nature and cease to exist,
absurd per Prop. VII. Prop. XIII's *demonstratio* reruns the same
dilemma for absolutely infinite substance. Horn (ii) requires
destruction/persistence machinery the base layer does not have
(GAP-20); horn (i) is the load-bearing one for the actual
contradiction and needs no such machinery — it is a purely
synchronic claim about what a hypothesised part *would be*. A32
encodes exactly the premise horn (i) needs.

**Commentary**: Bennett 1984 §21–22 reads Spinoza's rejection of
the divisibility of substance as resting on precisely this "parts
would be rival substances" premise — a genuine part of a substance
could only be conceived, per Def. III/IV, as itself *in itself*
and *per se conceived*, i.e. as itself a substance sharing the
whole's nature. We commit to that premise visibly, as a Section
III axiom, rather than deriving it from Defs. III/IV (which do not
by themselves force a *part* of a substance to inherit
substancehood).

**Why it cannot be derived**: `ModeParts` in
`Models/CounterexamplesII.lean` supplies the kernel-level
irreducibility witness (closing the gap this entry previously
flagged as future work). It is a two-element world (`whole`/`part`)
embodying the **parts-as-modes** reading of extended substance
(Letter 12 to Meyer; Curley): a substance whose sole proper part is
a *mode*, not a rival substance. The model satisfies the **full
register** `Pars1Axioms` (A1–A15) + `CausalAxioms` +
`TheologiaAxioms` (A27–A31) + `InherenceAxioms` (A33–A36) —
instances `modeParts_pars1Axioms`, `modeParts_causalAxioms`,
`modeParts_theologiaAxioms`, `modeParts_inherenceAxioms` — while
falsifying A32 (`A32_falsified`). Any Lean derivation of A32 from
that register would specialise to `ModeParts` and yield `False`;
hence A32 is a genuine interpretive *choice* (horn (i)'s
parts-as-rival-substances against the live parts-as-modes
alternative), not forced by any other commitment the formalisation
has made. This baseline is stronger than the paper's
`StatedAxioms`-based A12/A15 counter-models — parity with
`NoGod.lean`'s A27 result.

**Used by**: `prop_12_substanceIndivisible`,
`prop_13_absolutelyInfiniteSubstanceIndivisible`,
`prop_13_cor_noSubstanceDivisible` (`Mereology.lean`), combined
with A12 in each case.

**Consistency witness**: `Models/MereologyWitness.lean` — `Unit`
with `properPart _ _ := False`, so A32 discharges vacuously.

**Caveat**: A32 commits to horn (i) of Prop. XII's dilemma only;
horn (ii) (destruction/persistence) is not formalised — see
`gaps.md` GAP-20. The proposition's own epistemic wrapper ("*vere
concipi*") is also not mechanised — see GAP-16.

---

## A35 — No mode's essence involves existence

**Lean signature** (in `InherenceAxioms`, `Ethica/Pars1/Inherence.lean`):
```lean
ax_mode_not_involvesExistence :
  ∀ x : Thing, Mode x → ¬ involvesExistence x
```

**Why we add it**: This IS Prop. XXIV's content, adopted directly
as an axiom — the same 📜-pattern as A13/Prop. VII. Spinoza's
*demonstratio* is a single line — "*Patet ex definitione 1*" —
reasoning that if a produced thing's essence involved existence,
it would be *causa sui* and hence not produced by another. That
inference needs a converse link ("produced by another ⇒ not *causa
sui*") that the axioms stated so far do not deliver: A7
(`ax7_conceivableAsNonExistent`) runs the *other* direction
(non-necessity of nature ⇒ no involved existence), and nothing else
in `Pars1Axioms` or `CausalAxioms` connects being a mode to *not*
involving existence.

**Commentary**: We commit visibly, exactly as A13 (Prop. VII's
content) was committed in `Axioms.lean` — the honest-promotion
pattern, not a derivation dressed up as one.

**Why it cannot be derived**: `NecessaryMode` in
`Models/CounterexamplesII.lean` supplies the kernel-level
irreducibility witness (closing the gap this entry previously
flagged). It is a two-element world (`g`/`m`) with a
**necessarily-existing mode** — precisely the profile Spinoza
assigns the infinite modes (Props. XXI–XXIII), except with the
necessity lodged in the mode's own essence rather than in its
cause. The model satisfies `Pars1Axioms` (A1–A15) +
`CausalAxioms` + `TheologiaAxioms` (A27–A31) in full (instances
`necessaryMode_pars1Axioms`, `necessaryMode_causalAxioms`,
`necessaryMode_theologiaAxioms`) **together with the other three
`InherenceAxioms` fields** — A33, A34, A36, proved as standalone
theorems `necessaryMode_satisfies_A33/34/36` (a full
`InherenceAxioms` instance would prove A35 itself) — while
falsifying A35 (`A35_falsified`). Hence A35 (= Prop. XXIV) is what
enforces the distinction between existing necessarily *through
one's cause* and *through one's own essence*; nothing else in the
register rules the configuration out. Machine-checked confirmation
that Spinoza's "*patet ex definitione 1*" conceals a substantive
premise — A7 runs only the opposite direction.

**Used by**: `prop_24_producedEssenceNotInvolveExistence` (direct),
`prop_24_cor_modeNotCausaSui` (corollary fragment, definitionally
identical), both `Inherence.lean`.

**Consistency witness**: `Models/InherenceWitness.lean` — `Unit`
with `inheresIn _ _ := False`; A35 (like A33, A36) discharges
vacuously since `Mode ()` is `False` on `Unit`.

---

## A40 — Absolute followers are eternal and infinite (📜 Prop. XXI)

**Lean signature** (in `ConsecutioAxioms`, `Ethica/Pars1/Consecutio.lean`):
```lean
ax_absoluteConsecution_eternalInfinite :
  ∀ x a g : Thing, IsGod g → Attribute a g → followsAbsolutely x a →
    Eternal x ∧ ¬ finitumInSuoGenere x
```

**Why we add it**: This IS Prop. XXI's content, adopted directly
as an axiom — the same honest-promotion 📜-pattern as A13/A27/A35.
Spinoza's *demonstratio* is a two-part reductio run through
*duration* (a mode supposed to have "*determinatam existentiam
sive durationem*") and finitude-limitation over time ("*aliquando
non exstitisse vel non exstitura*") — machinery the base layer
simply does not have: there are no temporal operators anywhere in
`EthicaWorld`. We commit to the conclusion directly rather than
fake a derivation the layer cannot support.

**Commentary / honest caveat**: the `Eternal` primitive used here
is the same one Def. VIII supplies for God's own essence-grounded
eternity (`prop_19_godIsEternal`); Prop. XXI's "*aeterna*" for
infinite modes is arguably a *derivative* sempiternity-through-a-
cause rather than essence-grounded eternity (a distinction
Spinoza's own "*per idem attributum aeterna*" glosses over). A40
conflates the two senses, as Spinoza's text itself invites —
tracked as **GAP-21**; disentangling awaits the modal layer's
world-relative existence machinery.

**Used by**: `prop_21_absoluteFollowersEternalInfinite`
(`Consecutio.lean`).

**Consistency witness**: `Models/ConsecutioWitness.lean` —
discharges non-vacuously on `ConsecutioW` (`Eternal` uniformly
`True`; `finitumInSuoGenere` unsatisfiable on a one-element
carrier).

---

## A41 — Infinite-mode transfer of eternity/infinity (📜 Prop. XXII)

**Lean signature** (in `ConsecutioAxioms`, `Ethica/Pars1/Consecutio.lean`):
```lean
ax_infiniteModeTransfer :
  ∀ x m : Thing, Mode m → Eternal m → ¬ finitumInSuoGenere m →
    followsFrom x m → Eternal x ∧ ¬ finitumInSuoGenere x
```

**Why we add it**: This IS Prop. XXII's content (📜-pattern).
Spinoza's own *demonstratio* just refers back to Prop. XXI's
("*eodem modo*"), inheriting the same durational-machinery gap
A40 documents.

**Commentary / honest caveat**: Spinoza's statement is genuinely
**ternary** — "*ex aliquo Dei attributo, quatenus modificatum est
modificatione quae …*": a thing following from an
*attribute-as-modified-by-a-modification*, not simply from the
modification on its own. `ConsecutioWorld` has only the binary
`followsFrom : Thing → Thing → Prop`, so the
attribute-relativisation cannot be represented; A41 flattens
Prop. XXII to a binary transfer along `followsFrom` from the
infinite mode itself. Tracked as **GAP-22**; a ternary consecution
relation (thing / attribute / modification) would be needed for
the full statement. A41 also shares A40's eternity/sempiternity
conflation (GAP-21).

**Used by**: `prop_22_infiniteModeTransfer` (`Consecutio.lean`).

**Consistency witness**: `Models/ConsecutioWitness.lean` — same
non-vacuous discharge as A40.

---

## A42 — Every finite mode is caused by another finite mode (📜 Prop. XXVIII)

**Lean signature** (in `ConsecutioAxioms`, `Ethica/Pars1/Consecutio.lean`):
```lean
ax_finiteMode_causedByFiniteMode :
  ∀ x : Thing, Mode x → finitumInSuoGenere x →
    ∃ y, Mode y ∧ finitumInSuoGenere y ∧ y ≠ x ∧ Cause y x
```

**Why we add it**: This IS Prop. XXVIII's content in its
non-iterated single-step form (📜-pattern); the "*et sic in
infinitum*" iteration is *derived* from it as
`prop_28_cor_noFirstFiniteCause`. Spinoza's *demonstratio* chains
Props. XXI and XXII with an **exhaustiveness premise** — every
mode follows absolutely, or via an infinite modification, or via
a finite one (the trichotomy that is Prop. XXIII's content) — to
rule out the first two horns. Prop. XXIII is not mechanised (it
is itself uncommitted machinery — **GAP-23**), so rather than fake
a derivation through an unavailable trichotomy, we commit to the
destination directly.

**Commentary**: This is the **backbone of finite-mode causation**
that Pars II–V consume throughout — the positive counterpart of
the A5ₛ substance-restriction (review §3.1) that protected
finite-mode causation from collapse. The honest-minimal-form
argument: committing the conclusion visibly is cheaper and more
honest than committing the trichotomy plus the horn-exclusion
premises it would take to derive it.

**Used by**: `prop_28_finiteModeCausedByFiniteMode` (direct),
`prop_28_cor_noFirstFiniteCause` (derived), both
`Consecutio.lean`.

**Consistency witness**: `Models/ConsecutioWitness.lean` —
discharges vacuously (`Mode` unsatisfiable on `ConsecutioW`).

**Demote outcome (equal-strength decomposition, post-Classificatio)**:
`Classificatio.lean`'s `A42_demote_via_trichotomy` proves A42's full
content from Σ = `TrichotomySigma` — the base+inherence register
plus duplicated signatures for A38, A40, A41, and **A44**
(`ax_consecution_trichotomy`), deliberately excluding A42 itself.
The proof case-splits on the trichotomy A44 supplies: the first two
horns (absolute consecution / infinite-mode transfer) are ruled out
by A40/A41's own eternity conclusion contradicting the finite-mode
hypothesis; the third horn hands back almost exactly A42's
conclusion, with A38 converting the surviving `followsFrom` to
`Cause`. Mirrors the A15 outcome (`ModalForm.lean`,
`prop_A15_demote_via_decomposition`): A42 is an **equal-strength
decomposition**, not a reduction — the destination axiom (A44) is
no weaker than A42, and Prop. XXIII's own classification content is
exactly what Prop. XXVIII's finite-mode-causal chain needs, no more
and no less. Unlike A15's decomposition (one axiom → two, neither
weaker), A42's decomposition trades one axiom for a register
{A38, A40, A41, A44} already committed elsewhere for independent
reasons (A38 for Prop. XVI Cor. I; A40/A41 for Props. XXI/XXII)
*plus* exactly one new commitment (A44) — so the net new-commitment
cost of dropping A42 in favour of A44 is a single axiom. Contrast
with A27/A32/A35, which resist decomposition entirely
(counter-witnessed in `Models/`). `instance
trichotomySigma_of_classificatio` shows Σ is non-vacuously
satisfiable by every model this project already trusts (every
`ClassificatioAxioms` instance yields a `TrichotomySigma` instance).
See README's demote-experiments table (A42 row) and A44's entry
below.

---

## A43 — Everything has some effect follow from it (📜 Prop. XXXVI)

**Lean signature** (in `ConsecutioAxioms`, `Ethica/Pars1/Consecutio.lean`):
```lean
ax_omnia_effectum : ∀ x : Thing, ∃ e, followsFrom e x
```

**Why we add it**: This IS Prop. XXXVI's consecution content
("*nihil existit ex cujus natura aliquis effectus non sequatur*"),
📜-pattern. Spinoza's *demonstratio* routes through Prop. XXV cor.
plus Prop. XXXIV ("*Dei potentia est ipsa ipsius essentia*") — the
whole argument turns on the *potentia* machinery of Props.
XXXIV–XXXV, which is not formalised anywhere in the project (both
propositions deferred; no `potentia` primitive exists at this
layer). Rather than fabricate a power relation solely to route
this one proof, we commit the consecution conclusion directly.

**Commentary**: Note the division of labour: A43 commits only the
*consecution* form; the *causal* form of Prop. XXXVI
(`∃ e, Cause x e`) is **derived** from A43 via A38 in
`prop_36_nothingWithoutEffect` — a genuine (small) derivation,
not a second commitment. A43 is also the axiom that forces
`Models/ConsecutioWitness.lean` to use a positive-profile carrier:
unlike A33–A36 it has no `Mode` hypothesis to discharge vacuously
and needs an actual witness `e` for every `x`.

**Used by**: `prop_36_nothingWithoutEffect` (via A38,
`Consecutio.lean`).

**Consistency witness**: `Models/ConsecutioWitness.lean` —
discharges non-vacuously (the unique element is its own witness;
`followsFrom` uniformly `True`).

---

## A44 — Consecution trichotomy (Section III; Prop. XXVIII's silent premise)

**Lean signature** (in `ClassificatioAxioms`, `Ethica/Pars1/Classificatio.lean`):
```lean
ax_consecution_trichotomy :
  ∀ x : Thing, Mode x →
    (∃ g a, IsGod g ∧ Attribute a g ∧ followsAbsolutely x a) ∨
    (∃ m, Mode m ∧ Eternal m ∧ ¬ finitumInSuoGenere m ∧ followsFrom x m) ∨
    (∃ y, Mode y ∧ finitumInSuoGenere y ∧ y ≠ x ∧ followsFrom x y)
```

**Why we add it**: A42's own docstring already flagged that Prop.
XXVIII's *demonstratio* silently consumes an exhaustiveness premise
— every mode follows either absolutely from an attribute of God
(Prop. XXI's route), from an eternal-and-infinite mode (Prop.
XXII's route), or from another finite mode (the route Prop. XXVIII
itself concludes to, by elimination of the first two): "*at id
quod finitum est … ab absoluta natura alicujus Dei attributi
produci non potuit* … *at ex Deo vel aliquo ejus attributo quatenus
affectum est modificatione quae aeterna et infinita est, sequi
etiam non potuit* … *debuit ergo sequi* … *a Deo vel aliquo ejus
attributo quatenus modificatum est modificatione quae finita est*".
An elimination argument of this shape only closes if the three
horns are jointly exhaustive — a fact Spinoza nowhere argues for
independently. This is precisely **Prop. XXIII's own content**
(the trichotomy clause, minus the necessarily-infinite exclusion —
see `coverage.md`'s Prop. XXIII row), committed here directly so
Prop. XXVIII's elimination step has a visible premise to rest on.

**Commentary**: Bennett 1984 §25 flags the classification as an
unargued premise of the infinite-mode doctrine — exactly the target
this entry commits visibly rather than leaving buried in Prop.
XXVIII's *demonstratio*.

**Used by**: `prop_23_partial_classification` (direct,
`Classificatio.lean` — the trichotomy clause of Prop. XXIII);
`A42_demote_via_trichotomy` (the A42 demote experiment, same file —
see A42's entry above for the decomposition outcome).

**Consistency witness**: `Models/ClassificatioWitness.lean` — A44
discharges vacuously on `ConsecutioW` (`Mode x` is `False` there),
exactly as A42 does in `Models/ConsecutioWitness.lean`.

**Caveat**: A44 commits only the trichotomy's *exhaustiveness*, not
Prop. XXIII's further exclusion of the finite branch for
necessarily-infinite modes — that residue needs a finite-source
transfer principle not committed anywhere in this formalisation
(cross-ref `gaps.md` GAP-23's residual half, and GAP-22 for the
ternary-relation prerequisite the fully general form would need).

---

# Modal-layer auxiliary axioms

The following auxiliary axioms live in
`Ethica/Pars1/ModalForm.lean` and are committed at the modal
layer (not in the base `Pars1Axioms`). Section labelling follows
the same I / II / III geometry as the base layer.

---

## A18 — Essential existence is necessary existence (Section I, modal)

**Lean signature** (in `ModalEthicaAxioms`):
```lean
ax_involvesExistence_iff_necExists :
  ∀ s : Thing, involvesExistence s ↔ ∀ w : World, existsAt s w
```

**Why we add it**: Without this bridge, the modal layer's
`existsAt` primitive floats free of the base layer's
`involvesExistence`. A model could have `involvesExistence s`
true and `existsAt s w` false at every `w`, which contradicts
Spinoza's identification of essential existence with necessary
existence (Della Rocca 2008 ch. 4).

**Commentary**: PSR-flavoured (Della Rocca line). Bennett-line
readers might allow `involvesExistence` to express *modal
de-re* essence without committing to actual existence at every
world; the present design takes the Della-Rocca reading.

**Used by**: prerequisite for any A12 / A13 demote attempt at
the modal layer.

---

## A19 — `perSeConceived` is no external conceptual dependence (Section I, modal)

**Lean signature** (in `ConceptualBridges`):
```lean
ax_perSe_iff_no_external_dep :
  ∀ x : Thing, perSeConceived x ↔
    (∀ y : Thing, conceptualDep x y → y = x)
```

**Why we add it**: Bridges the base layer's `perSeConceived`
predicate to the modal layer's `conceptualDep` relation. Without
this, A16-candidate / A17-candidate (asymmetry) sit beside
`perSeConceived` without telling us they have anything to do with
"per se conceiving".

**Commentary**: Della Rocca 2008 ch. 2 reads `per se concipi`
as exactly "no conceptual dependence on anything else". Bennett
1984 §16 might allow self-referential conceptual loops (`x`
depends on `x`); the present axiom permits self-loops too
(`y = x` is a valid case) so this much is Bennett-compatible.
Strict readings rejecting all loops would tighten further.

**Used by**: prerequisite for using `prop_1_priority` in
combination with base-layer `perSeConceived`-flavoured
arguments.

---

## A20 — `conceivedThroughAnother` is external conceptual dependence (Section I, modal)

**Lean signature** (in `ConceptualBridges`):
```lean
ax_throughAnother_iff_external_dep :
  ∀ x : Thing, conceivedThroughAnother x ↔
    (∃ y : Thing, y ≠ x ∧ conceptualDep x y)
```

**Why we add it**: Mode-side counterpart of A19. Connects
`conceivedThroughAnother` to the existence of an `≠ x` thing on
which `x` conceptually depends.

**Commentary**: Same PSR-flavoured caveat as A19.

**Used by**: same as A19.

---

## A21 — `Cause` is necessary causation (Section I, modal)

**Lean signature** (in `ModalCausalAxioms`):
```lean
ax_cause_iff_necCauseAt :
  ∀ c e : Thing, Cause c e ↔ ∀ w : World, causeAt c e w
```

**Why we add it**: Without this, the world-uniform `Cause`
relation in `Causation.lean` and the world-relative `causeAt` in
the modal layer are unrelated primitives. Spinoza's deterministic
metaphysics treats causation as essential, hence world-invariant.

**Commentary**: Della Rocca 2008 ch. 2's reading. Bennett-line
readers who hold causation can be world-relative would weaken
this to `→` only (giving up the `∀ w` direction). The
biconditional commits the Della Rocca line.

**Used by**: prerequisite for the A4ₛ-from-A3-substantive demote
attempt (deferred).

---

## §III.B — Modal-layer conceptual asymmetry candidates

---

## A16-candidate — Modes depend on substances (Section III, modal)

**Status**: ⏳ **not yet promoted**. Currently a
`ConceptualDepAxioms` field in `Ethica/Pars1/ModalForm.lean`.

**Lean signature**:
```lean
ax_mode_depends_on_substance :
  ∀ m : Thing, Mode m →
    ∃ s : Thing, Substance s ∧ conceptualDep m s
```

**Why we add it**: Spinoza Prop. I priority requires that every
mode depend conceptually on some substance. Defs III/V plus the
parallelism axioms (A8, A9) do not entail this on their own —
nothing in the base layer requires modes to *have* a substance
they depend on.

**Commentary**: Della Rocca 2008 ch. 2 derives this from PSR;
Bennett 1984 §16 treats it as an independent commitment. Same
geography as A14: Della Rocca says "follows from PSR", Bennett
says "independent commitment", we record it visibly.

**Used by**: `prop_1_priority` in `ModalForm.lean`.

**Closes**: GAP-6 (substance side of priority).

**Related GAP (Bennett-honest scoping)**: derivation from PSR
+ base axioms (Della Rocca demote attempt) is **not guaranteed**
to succeed. If Bennett is correct, A16 stays in modal-layer
Section III permanently.

---

## §III.C — Modal-layer PSR demote axioms

These axioms are introduced for the demote-attempt experiments
(§δ through §δ-4 in `ModalForm.lean`). They have a recursive
role: they are Section III commitments introduced *in order to
derive* §III.A axioms (A12-A15). The demote outcomes document
the structural status of the §III.A axioms:

| Target | Demote axioms | Outcome | Pattern |
|--------|--------------|---------|---------|
| A12 | A22 (`PSRSubstance`) | Partial only | Irreducible (Bennett-line evidence #1) |
| A13 | A23 (`PSRSelfCause`) + A18 bridge | Full success | Modal translation, equal strength |
| A14 | A24 (`PSREssencePerception`) | Full success | Trivial redescription, equal strength |
| A15 | A25 + A26 (`PSRPlenitude`) | Decomposition only | Irreducible (Bennett-line evidence #2) |

**Counter-models** (`Ethica/Pars1/Models/Counterexamples.lean`)
provide the kernel-level hard facts for the two irreducibility
results:
- `A12CounterModel`: a `StatedAxioms` + `PSRSubstance` instance
  where two distinct substances share an attribute → A12 not
  derivable from the stated register + PSR.
- `A15CounterModel`: a `StatedAxioms` instance with two
  attribute-distinct gods, plenitude holding, A15 falsified →
  A15 not derivable from the stated register + plenitude.

---

## A22 — PSR for substance distinguishability (Section III, modal)

**Status**: ✅ committed as a `PSRSubstance` field in
`Ethica/Pars1/ModalForm.lean`. The class is independently
optional — proofs that need PSR-flavoured demote attempts
require `[PSRSubstance Thing]`; theorems that don't, don't.

**Lean signature**:
```lean
ax_PSR_substance_distinguishability :
  ∀ s₁ s₂ : Thing, Substance s₁ → Substance s₂ → s₁ ≠ s₂ →
    ∃ a, (Attribute a s₁ ∧ ¬ Attribute a s₂) ∨
         (Attribute a s₂ ∧ ¬ Attribute a s₁)
```

**Why we add it**: Della Rocca 2008 ch. 2's reading of Spinoza's
PSR for substances. Distinct substances must have a sufficient
reason for being distinct; per Prop. IV the only available reason
is an attribute difference (modes are posterior — Prop. I
priority). Hence: distinct → some attribute distinguishes them.

**Used by**: `prop_5_demote_via_PSR_all_attributes` —
demonstrating that the *partial* form of A12 (substances sharing
**all** attributes are identical) demotes via PSR.

**Crucial mechanical finding**: full A12 (substances sharing
**any** attribute are identical — Spinoza's actual Prop. V
content) is **NOT** derivable from `[PSRSubstance Thing]` +
base axioms alone. The kernel-level evidence is **a
counter-model**: see `Ethica/Pars1/Models/Counterexamples.lean`
`A12CounterModel`, a 4-element `StatedAxioms` + `PSRSubstance`
instance (all four elements substances) where two distinct
substances share an attribute, falsifying A12. If A12 were derivable
from the stated register + PSR, the derivation would yield `False`
on this model.

A marker theorem `A12_full_NOT_demotable_from_PSR_alone : True :=
trivial` would be a Lean-as-rhetoric trick (`True` proves nothing
about provability); the counter-model replaces any such marker with
a kernel-level hard fact.
This is the **first mechanical evidence in the project for
Bennett 1984 §17's reading** that Spinoza's Prop. V exceeds what
PSR-alone can deliver.

**Bennett-honest scoping**: this axiom and its consequences are
PSR-flavoured (Della Rocca line). Bennett-line readers might
weaken or drop it; in either case, the demote-attempt result
above stands as evidence for Bennett's Prop. V irreducibility
claim.

---

## A23 — PSR for substance self-causation (Section III, modal)

**Status**: ✅ committed as a `PSRSelfCause` field in
`Ethica/Pars1/ModalForm.lean`. The class is independently
optional — like A22 (PSRSubstance), proofs that need this
flavour of PSR-derivation require `[PSRSelfCause Thing World]`.

**Lean signature**:
```lean
ax_substance_self_caused_at_every_world :
  ∀ s : Thing, ∀ w : World, Substance s →
    ModalCausalWorld.causeAt s s w
```

**Why we add it**: Della Rocca 2008 ch. 2's reading of Spinoza's
Prop. VII via PSR. Every substance has a sufficient reason for
its own existence; per Prop. VI corollary the reason cannot be
external; hence it must be internal — substance is *causa sui*,
which on the modal layer reads as "self-caused at every world".

**Used by**: `prop_7_demote_via_PSR` —
demonstrating that A13 (`Pars1Axioms.ax_substance_involves_existence`)
**fully demotes** via the modal-translation route. Combined with
A18 (existence bridge) and A3-first-clause (cause necessitates
effect), A23 delivers
`∀ s, Substance s → involvesExistence s`, which is A13's content.

**Crucial mechanical finding (asymmetry with A12)**:
- A12 demote attempt was **partial only**: PSR-distinguishability
  delivers the all-shared-attribute case, full A12 is strictly
  stronger (Bennett-line evidence).
- A13 demote attempt **fully succeeds via modal translation**:
  A23 + bridges deliver A13's full content. **But** A23 is not
  weaker than A13 — it is a redescription of "substance has
  necessary existence" in modal-causation vocabulary.

The asymmetry reflects philosophical content: A12's universality
clause has no modal equivalent in our vocabulary, while A13's
existence clause does (via modal causation). A12 is **irreducibly
substantive**; A13 is **modally translatable**. Bennett's
irreducibility survives intact for A12; for A13 both readings
can claim partial victory — Della Rocca that A13 *just is* A23,
Bennett that the commitment hasn't decreased in strength.

**Bennett-honest scoping**: A23 is PSR-flavoured (Della Rocca
line). Bennett-line readers who reject A23 retain A13 in its
original Section III form. Either way, the demote-attempt
documents the *structure* of Spinoza's commitment system as
seen through modal vocabulary.

**Translation cost — A18 dependency**: the equivalence between
A23 and A13 holds **modulo A18** (the bridge
`involvesExistence ↔ ∀ w, existsAt`). The A13 demote thus
replaces one `Pars1Axioms` commitment (A13) with one modal-layer
commitment (A23) **plus reliance on the A18 bridge**. The total
commitment count is unchanged; only the locus shifts. Without
A18, A23 alone does not deliver A13's content.

---

## A24 — PSR for substance-essence perception (Section III, modal)

**Status**: ✅ committed as a `PSREssencePerception` field in
`Ethica/Pars1/ModalForm.lean`. Independently optional like A22,
A23.

**Lean signature**:
```lean
ax_substance_has_essence_perception :
  ∀ s : Thing, Substance s →
    ∃ a, intellectPerceivesAsEssence s a
```

**Why we add it**: Della Rocca 2008 ch. 2's reading: every
substance is intelligible (PSR), and intelligibility is mediated
by attributes (Def. IV); hence every substance has an essence the
intellect perceives.

**Used by**: `prop_A14_demote_via_PSR` —
demonstrating that A14 (`Pars1Axioms.ax_substance_has_attribute`)
**fully demotes** via essence-perception. The proof unwraps
`Attribute a s := Substance s ∧ intellectPerceivesAsEssence s a`
and attaches the substance hypothesis to the perception A24
provides.

**Mechanical finding**: A14 is the **trivially redescribable**
case in the demote taxonomy. A24 has the exact same shape as
A14 (`∀ s, Substance s → ∃ a, …`) with `Attribute a s` replaced
by its only non-trivial component `intellectPerceivesAsEssence s
a`. Logically equivalent modulo unfolding. Equal commitment-
strength.

**Why A14 demotes but A15 does not**: A14
(`∀ s, Substance s → ∃ a, Attribute a s`) is substance-universal
but attribute-*existential*, so PSR-style existence axioms
demote it cleanly. A15 is universal in *both* substance and
attribute (every god has *every* realised substance attribute),
which PSR's existence-explanatory shape cannot reach. The
distinction sharpens the categorisation of which axioms are
PSR-reducible and which are not.

**Demote taxonomy after §δ, §δ-2, §δ-3**:

| Axiom | Demote outcome | Pattern |
|-------|----------------|---------|
| A12 | Partial only — full content irreducible | Bennett-line evidence (universality of attribute-individuation) |
| A13 | Full success via modal translation | Redescription at equal strength (existence ↔ self-causation) |
| A14 | Full success, trivially | Redescription at equal strength (Attribute ↔ essence-perception) |
| A15 | Pending §δ-4 | Predicted: irreducible (true universality clause) |

**Bennett-honest scoping**: A24 is PSR-flavoured. Same caveat as
A22, A23 — the demote tells us about the *structure* of
Spinoza's commitments, not their elimination.

---

## A25, A26 — PSR plenitude + god uniqueness (Section III, modal)

**Status**: ✅ committed as fields of a `PSRPlenitude` class in
`Ethica/Pars1/ModalForm.lean`. Two axioms in one class because
they jointly demote A15 — neither alone suffices.

**Lean signatures**:
```lean
ax_plenitude_attribute :
  ∀ a s, Substance s → Attribute a s →
    ∃ g, IsGod g ∧ Attribute a g

ax_god_unique :
  ∀ g₁ g₂, IsGod g₁ → IsGod g₂ → g₁ = g₂
```

**Why we add them**: Della Rocca 2008 ch. 2's reading of A15
decomposes into (i) plenitude — every realised substance attribute
is realised in some god — and (ii) uniqueness — all gods are
identical.

**Used by**: `prop_A15_demote_via_decomposition` —
demonstrating that A15 fully demotes from A25 + A26 jointly.

**Mechanical finding**: A15 demote requires **both** axioms.
Plenitude alone is genuinely weaker than A15: see
`Ethica/Pars1/Models/Counterexamples.lean` `A15CounterModel`,
where plenitude holds but A15 fails. Hence A15 cannot be reduced
to plenitude alone — it is **irreducible** in the same sense A12
is. This is the **second mechanical evidence in the project for
Bennett 1984 §17 / §18's reading**: PSR's existence-explanatory
power does not reach genuinely universal claims (over attributes).

**A26 is strictly weaker than Prop. XIV**: A26 asserts only that
any two gods are identical — it does not rule out non-god
substances. Prop. XIV (`Praeter Deum nulla dari neque concipi
potest substantia` — *every* substance is god) is strictly
stronger: it requires combining A26 with the universality reach
of A15 to conclude `∀ s, Substance s → s = god`. The previous
self-assessment "A26 is essentially Prop. XIV's content" was too
generous; the corrected reading: **the A15 demote via A25 + A26
trades one universality (over attributes) for two commitments —
an existence (plenitude over attributes) plus a different
universality (over gods) — neither strictly weaker than A15.**

The decomposition into A25 + A26 is **not a reduction**:
universality of attribute-presence in gods (A15) is replaced by
universality of god-identity (A26) plus existence of god-bearers
(A25). The direction of universality shifts, but the
total Section III commitment count goes from 1 to 2.

**Bennett-honest scoping**: A25 + A26 are PSR-flavoured. The
decomposition documents the *structure* of A15's commitment,
showing it splits into existence (plenitude) + identity
(uniqueness) — each at Section III strength.

---

## A17-candidate — Substances do not depend on modes (Section III, modal)

**Status**: ⏳ **not yet promoted**. Currently a
`ConceptualDepAxioms` field.

**Lean signature**:
```lean
ax_substance_not_dep_on_mode :
  ∀ s m : Thing, Substance s → Mode m → ¬ conceptualDep s m
```

**Why we add it**: The asymmetry of Prop. I priority. Defs III/V
+ parallelism do not exclude substance-on-mode dependence; this
is precisely the asymmetric content Curley 1988 ch. 1 reads into
"prior natura".

**Commentary**: Same Bennett-vs-Della-Rocca geography as A16.

**Used by**: `prop_1_priority`.

**Closes**: GAP-6 (asymmetry side).

**Related GAP (Bennett-honest scoping)**: same as A16.

---

# Attributum-layer auxiliary axioms (re-typed)

`Ethica/Attributum/` is a **parallel branch** adopting escape route
(iii) of GAP-25: attributes are typed off the `Thing` universe. It
modifies nothing under `Ethica/Pars1/`; the v1.0.0 register and the
published irreducibility results stand untouched.

The layer re-types the four attribute-mentioning axioms of
`Pars1Axioms`. Each keeps its Section classification, its
philosophical justification and its commentary **verbatim** — the
only change is the type of the attribute argument. What re-typing
changes is not the weight of any single axiom but what the axioms
can be *combined into*: the five-step attribute-collapse chain loses
its step 3, because `attribute_is_substance` becomes ungrammatical.

**A8 has no primed counterpart, by design.** It is the axiom that
turned an attribute into a substance, and its bite on attributes is
exactly what this layer withdraws. No A8′ exists or can be written:
`inItself : Thing → Prop` cannot be applied to `a : Attr`. Bennett
1984 §16.

| Pars I | field | Attributum | field | Section |
|--------|-------|------------|-------|---------|
| A10 | `ax_attribute_perSe` | A10′ | `ax_attributum_perSe` | I |
| A12 | `ax_substanceIdByAttribute` | A12′ | `ax_substanceIdByAttributum` | III |
| A14 | `ax_substance_has_attribute` | A14′ | `ax_substance_has_attributum` | III |
| A15 | `ax_IsGod_has_attribute_of` | A15′ | `ax_IsGod_has_attributum_of` | III |

---

## A10′ — Every attribute of a substance is per se conceived (re-typed)

**Lean signature**:
```lean
ax_attributum_perSe :
  ∀ (a : Attr) (s : Thing),
    Attributum a s → AttrStructure.perSeConceivedAttr a
```

**Why we add it**: it is Prop. X (*Unumquodque unius substantiae
attributum per se concipi debet*), stated in the attribute-side
vocabulary. Pars I's A10 concluded `perSeConceived a` with
`a : Thing`; here the conclusion is `perSeConceivedAttr a` with
`a : Attr`, where `perSeConceivedAttr` is a field of
`AttrStructure Attr` — a class that does not mention `Thing` at all.

**Commentary**: the substantive difference is what is now *missing*.
In Pars I this conclusion fed A8 and yielded `Substance a`. Here it
terminates: nothing connects `perSeConceivedAttr` to the `Thing`
side, and the class signature makes that visible rather than
merely true. Prop. X is preserved; the inference from Prop. X to the
substance-hood of attributes is not.

**Used by**: `prop_10_attributumPerSe`.

**Consistency witness**: `Models/DualAttribute.lean`,
`Models/InfiniteAttribute.lean` (both discharge it non-vacuously).

---

## A12′ — Indiscernibility of substance by attribute (re-typed)

**Lean signature**:
```lean
ax_substanceIdByAttributum :
  ∀ (s₁ s₂ : Thing) (a : Attr),
    Attributum a s₁ → Attributum a s₂ → s₁ = s₂
```

**Why we add it**: verbatim Pars I A12. Spinoza's *demonstratio* of
Prop. V is widely judged to need this commitment.

**Commentary**: unchanged (Bennett 1984 §17, Garrett 1990, Della
Rocca 2008 ch. 2). Re-typing does **not** weaken A12: it still
collapses any two substances sharing an attribute. What it can no
longer do is collapse an *attribute* into God, because an attribute
is not a substance and so is not in A12's range.

**Used by**: `prop_5_uniqueSubstancePerAttributum`.

**Consistency witness**: `Models/DualAttribute.lean`,
`Models/InfiniteAttribute.lean`.

---

## A14′ — Substance has at least one attribute (re-typed)

**Lean signature**:
```lean
ax_substance_has_attributum :
  ∀ s : Thing, Substance s → ∃ a : Attr, Attributum a s
```

**Why we add it**: verbatim Pars I A14, existential ranging over
`Attr`.

**Commentary**: Della Rocca 2008 ch. 2 takes it for granted under
PSR; Bennett 1984 §17 treats it as an independent commitment. In
Pars I it supplied step 4 of the collapse chain, handing an
attribute to the substance an attribute had just been shown to be.
With step 3 gone it has no such role and does only the work Spinoza
asks of it.

**Consistency witness**: `Models/DualAttribute.lean`,
`Models/InfiniteAttribute.lean`.

---

## A15′ — God has every substance's attribute (re-typed)

**Lean signature**:
```lean
ax_IsGod_has_attributum_of :
  ∀ (g s : Thing) (a : Attr),
    IsGodAttr g → Substance s → Attributum a s → Attributum a g
```

**Why we add it**: verbatim Pars I A15, the universality reading of
Def. VI (GAP-8b).

**Commentary**: unchanged (Bennett 1984 §18 flags the universality
clause as a substantive commitment; Della Rocca derives it from PSR
plus plenitude). In Pars I this was step 5, the axiom that handed an
attribute-of-an-attribute to God so A12 could identify the two. Here
it lands harmlessly: `Attributum a g` for many distinct `a : Attr`
is exactly what Def. VI wants.

**Used by**: `prop_9_cor_godMaximalRealityAttr`.

**Consistency witness**: `Models/DualAttribute.lean` (two
attributes), `Models/InfiniteAttribute.lean` (infinitely many).

**Closes**: the consistency half of GAP-8a —
`inf_def6_recovered : HasInfiniteAttrs deus` satisfies Def. VI's
*infinitis attributis* clause with A15′ in force, which
`def6_infinitis_attributis_unsatisfiable` shows is impossible in the
Pars I register.

---

## Note on the extension classes

The Attributum layer re-types the `Pars1Axioms` attribute axioms
only. The attribute quantifiers in the *extension* classes — A29
(`Theologia.lean`), A40 (`Consecutio.lean`), A44
(`Classificatio.lean`) — are not yet re-typed; they are re-typed as
Pars II consumes them. Tracked in `gaps.md` GAP-25's residue note
rather than as a separate gap.
