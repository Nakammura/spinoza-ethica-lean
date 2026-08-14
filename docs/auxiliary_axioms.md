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

**Commentary**: This was intended as the **backbone of finite-mode
causation** that Pars II–V consume throughout — the positive
counterpart of the A5ₛ substance-restriction (review §3.1) that
protected finite-mode causation from collapse. The
honest-minimal-form argument: committing the conclusion visibly is
cheaper and more honest than committing the trichotomy plus the
horn-exclusion premises it would take to derive it.

> **⚠ Vacuity correction (batch 1.3).** The backbone claim does not
> hold, and the reason is structural rather than model-specific.
> `finitumInSuoGenere x` unfolds through `sameNature x y`, which
> GAP-2 path (b) defined as `∃ a, Attribute a x ∧ Attribute a y` —
> and `Attribute a s` carries `Substance s`. So
> `finitumInSuoGenere x` **entails `Substance x`**, and substances
> are disjoint from modes (`prop_1_substanceDisjointFromModes`).
> A42's hypothesis is therefore unsatisfiable in **every**
> `Pars1Axioms` world:
>
> ```lean
> theorem pars1_prop_28_vacuous_for_modes :
>     ¬ ∃ x : Thing, Mode x ∧ finitumInSuoGenere x
> ```
>
> (`Ethica/Pars2/Parallelismus.lean`; the model-side face is
> `mens_not_finite`.) A42 is committed and never fires; Prop.
> XXVIII is mechanised but delivers nothing downstream. The working
> replacement is **A59** (`ax_singulare_causatum`), which states the
> same content on `ResSingularis` — Pars II Def. VII rebuilt on
> `modeUnder`. A42 is left unedited because `Ethica/Pars1/` is
> frozen at v1.0.0; see A59's entry and GAP-2's batch-1.3 update.

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

---

# Pars II auxiliary axioms (A45–A50)

Introduced by `Ethica/Pars2/Idea.lean` (batch 1.1: Props. II.I,
II.II, II.III, II.VII). All live in `Pars2Axioms`, which extends
`ConsecutioAxioms` (hence `InherenceAxioms`, `CausalAxioms`,
`Pars1Axioms`) and `AttrAxioms`.

> **Base-class change, batch 1.2.** `Pars2Axioms` originally extended
> `CausalAxioms`. It was re-based onto `ConsecutioAxioms` so that
> Props. I.XV (`prop_15_allInGod`) and I.XVI cor. I
> (`prop_16_cor1_godEfficientCause`) are available to Pars II. That
> single change turned GAP-26 and Prop. II.VI's positive clause from
> pending axioms into derivations. No A45–A50 signature changed.

Consistency witness for all six: `Ethica/Pars2/Models/MensWitness.lean`.

---

## A45 — An idea has at most one object (Section II — promotion of Spinoza's A6)

**Lean signature**:
```lean
ax6_idea_unique_ideatum :
  ∀ i x y : Thing, ideaOf i x → ideaOf i y → x = y
```

**Why we add it**: Pars I carried Spinoza's own A6 (*Idea vera debet
cum suo ideato convenire*) as a `True` placeholder annotated
"idea/ideatum machinery is Pars II" (`Axioms.lean`). This is that
promotion — **the oldest placeholder in the project, now retired**.

**Commentary**: "*convenire*" is read here as **functionality** — an
idea determines its object uniquely. That is the weakest content the
word can carry and all batch 1.1 consumes. The stronger
correspondence content (an adequate idea has all the intrinsic
denominations of a true idea, Def. II.IV *idea adæquata*) needs the
adequacy machinery of batch 1.4 and is **not** claimed here. Flagged
in the field docstring as a reading, not a rendering.

**Used by**: `prop_2_9_ideaSingularisAbAliaIdea`
(`Pars2/Parallelismus.lean`) — **first consumer, batch 1.3**. It is
the step that makes Prop. IX's two ideas distinct: `y ≠ x` among the
things forces `j ≠ i` among their ideas precisely because an idea
has at most one object. Without A45 the regress could revisit the
same idea and "*et sic in infinitum*" would not follow.

Recorded for the history: batches 1.1 and 1.2 both left A45
**unconsumed** (Props. V–VI turn on `modeUnder`/`causeUnder`, not on
ideatum uniqueness), and this entry said so, on the ground that an
unused axiom is a claim the project carries without earning. It is
earned now. The stronger correspondence reading remains for the
adequacy machinery of batch 1.5.

---

## A46 — *Cogitatio* is an attribute of God (Section III, 📜 Prop. II.I)

**Lean signature**:
```lean
ax_cogitatio_attributum :
  ∀ g : Thing, IsGodAttr g → Attributum (cogitatio Thing) g
```

**Why we add it**: Spinoza's *demonstratio* runs from singular
thoughts being modes expressing God's nature (Prop. I.25cor) through
Def. I.5 to Def. I.6. The step unavailable to us is the first
premise's **existential import** — that there *are* singular
thoughts. Spinoza supplies it from Pars II's own Axiom II (*Homo
cogitat*), an avowedly empirical premise; the scholium offers an
independent route through conceiving an infinite thinking being.
Rather than import an empirical axiom or reconstruct the scholium,
we commit the conclusion directly — the 📜-pattern of
A13/A27/A35/A40/A41.

**Commentary**: Bennett 1984 §36 discusses the peculiar status of
Pars II's opening propositions at length.

**Used by**: `prop_2_1_cogitatioAttributumDei`,
`prop_2_1_2_deusHabetDuoAttributa`.

---

## A47 — *Extensio* is an attribute of God (Section III, 📜 Prop. II.II)

**Lean signature**:
```lean
ax_extensio_attributum :
  ∀ g : Thing, IsGodAttr g → Attributum (extensio Thing) g
```

**Why we add it**: Spinoza's entire *demonstratio* is "*Hujus eodem
modo procedit ac demonstratio præcedentis propositionis*", so this
axiom stands or falls exactly with A46.

**Used by**: `prop_2_2_extensioAttributumDei`,
`prop_2_1_2_deusHabetDuoAttributa`.

---

## A48 — Thought and extension are distinct (Section III)

**Lean signature**:
```lean
ax_cogitatio_ne_extensio : (cogitatio Thing : Attr) ≠ extensio Thing
```

**Why we add it**: Spinoza never states this as a proposition; it is
presupposed by the whole architecture of Pars II — by the
parallelism (Prop. VII), vacuous if the two orders were one, and by
Prop. VI's insistence that modes of one attribute have God as cause
*only* under that attribute.

**Commentary**: **this axiom is why the Attributum layer had to be
built.** Under Pars I's typing, A46 + A47 + A48 are jointly
inconsistent with the existence of a God — proved in Pars I's own
vocabulary by `pars2_opening_triple_inconsistent_in_pars1`
(`Pars2/Idea.lean`), which routes through
`god_is_own_only_attribute`. The inconsistency is a defect of the
Prop. X scholium reading, not of Spinoza's commitments. See GAP-25.

**Used by**: `prop_2_1_2_deusHabetDuoAttributa` (the injectivity
half).

---

## A49 — Everything has an idea (Section III, 📜 Prop. II.III)

**Lean signature**:
```lean
ax_god_has_idea_of_all : ∀ x : Thing, ∃ i : Thing, ideaOf i x
```

**Why we add it**: Spinoza's *demonstratio* chains Prop. II.I +
Prop. I.16 (God can form the idea), Prop. I.35 (whatever is in God's
power necessarily is), and Prop. I.15 (only in God). The
load-bearing middle step, **Prop. I.35, is ⏳ deferred** in this
formalisation — it needs the *potentia* machinery, along with
Prop. I.34. So the conclusion is committed directly rather than
derived through unavailable machinery, the discipline A42's
docstring applies to Prop. XXVIII.

**Used by**: `prop_2_3_ideaOmnium`, `prop_2_3_ideaInDeo`,
`prop_2_7_cor_ideaePariter`.

**Open**: ~~the *in Deo* localisation ("*non nisi in Deo*") is not
claimed — GAP-26.~~ **Closed in batch 1.2 without strengthening this
axiom**: re-basing `Pars2Axioms` onto `ConsecutioAxioms` made
`prop_15_allInGod` available, and `prop_2_3_ideaInDeo` derives the
localisation from it — which is Spinoza's own route ("*per
propositionem 15 partis I*"). A49's signature is unchanged.

---

## A50 — The idea order tracks intelligibility (Section II — bridge)

**Lean signature**:
```lean
ax_idea_tracks_intelligibility :
  ∀ e c : Thing, intelligibleThrough e c →
    ∀ ie ic : Thing, ideaOf ie e → ideaOf ic c → Cause ic ie
```

**Why we add it**: Prop. VII's *demonstratio* is two sentences —
"*Patet ex axiomate 4 partis I. Nam cujuscunque causati idea a
cognitione causæ cujus est effectus, dependet.*" A4ₛ
(`ax4_effectIntelligibleThroughCause`) delivers the first;
this axiom is the second, carrying intelligibility-dependence among
*things* to causal dependence among their *ideas*.

**Commentary**: classified **Section II** rather than III
deliberately — Spinoza asserts precisely this sentence as the
content of his demonstration, so it is a promotion of stated
material, not a reconstruction of a missing step. It is what makes
Prop. VII a genuine derivation here rather than a 📜 commitment.

**Used by**: `prop_2_7_ordoEtConnexio` (hence
`prop_2_7_cor_ideaePariter` and, with A55, the biconditional
`prop_2_7_ordoEtConnexio_iff`).

**Open**: ~~the converse direction~~ (closed in batch 1.2 by A55) and
the identity reading of "*idem est*" — GAP-27b.

---

# *Quatenus*-layer auxiliary axioms (A51–A55)

Introduced by `Ethica/Pars2/Quatenus.lean` (batch 1.2: Props. II.V,
II.VI, and the biconditional form of Prop. II.VII). All live in
`QuatenusAxioms`, which extends `Pars2Axioms`.

**All five are Section II.** That is the headline fact about this
batch: the *quatenus* machinery is expensive in **primitives**
(three new relations, the first attribute-relativised ones in the
project) and costs **nothing in Section III commitments**. Every one
of A51–A55 is a sentence Spinoza writes in the relevant
*demonstratio*, promoted to usable content. No 📜-pattern axiom
appears in this batch — Props. V and VI are genuine derivations, not
adopted conclusions.

Consistency witness for all five:
`Ethica/Pars2/Models/MensWitness.lean`, which discharges A51–A54
**non-vacuously** (its `modeUnder` / `causeUnder` /
`involvesConceptOf` relations genuinely refuse `extensio`, so the
exclusion clauses hold substantively rather than by an empty
relation) and A55 on real structure (its `Cause` is not constant —
see `mens_cause_irreflexive_deus`).

---

## A51 — Modes involve the concept of their own attribute only (Section II)

**Lean signature**:
```lean
ax_modeUnder_conceptum :
  ∀ (x : Thing) (a : Attr), modeUnder x a →
    involvesConceptOf x a ∧ ∀ b : Attr, b ≠ a → ¬ involvesConceptOf x b
```

**Why we add it**: Prop. VI's *demonstratio*, second sentence, is
exactly this: "*Quare uniuscujusque attributi modi conceptum sui
attributi, non autem alterius involvunt*." The two clauses are one
Latin sentence and are kept as one conjunctive field. The first
clause extends Prop. I.10 (each attribute is conceived through
itself) to modes; the second is the exclusion that gives Props. V
and VI their entire force.

**Commentary**: Bennett 1984 §17 identifies this as the strongest
form of Spinoza's attribute-separation doctrine — the point at which
attributes cease to be mere aspects and become explanatorily sealed
compartments. Della Rocca 1996 ch. 1 calls it "conceptual barrier"
and treats it as the premise the parallelism has to work around.
Neither reads it as needing separate argument: Spinoza asserts it as
a corollary of Prop. I.10, and so do we.

**Used by**: `prop_2_6_modiSubSuoAttributo` (exclusion clause),
hence `prop_2_6_cor_nonPerCogitationem`,
`prop_2_5_ideaeSubCogitatione`, `prop_2_5_cor_nonSubExtensione`.

---

## A52 — Causation under an attribute requires that attribute's concept (Section II — Ax. I.4 relativised)

**Lean signature**:
```lean
ax_causeUnder_involvesConcept :
  ∀ (c e : Thing) (a : Attr), causeUnder c e a → involvesConceptOf e a
```

**Why we add it**: both *demonstrationes* close "*per axioma 4
partis I*" — knowledge of an effect involves knowledge of its cause.
A4ₛ (`ax4_effectIntelligibleThroughCause`, `Causation.lean`) states
that for the binary `Cause`/`intelligibleThrough` pair. This is the
attribute-relativised form the *quatenus* clause needs, and it is
the direction Spinoza actually uses: from cause-under to
concept-involvement, so that the **absence** of the concept (A51's
second clause) rules the causal claim out.

**Commentary**: the relativisation is not a strengthening of A4ₛ —
it is A4ₛ read with the third argument slot the *quatenus*
construction supplies. Reading it the other way (concept-involvement
implies cause-under) would be a substantive and false addition; the
field states only the direction the demonstrations use.

**Used by**: `prop_2_6_modiSubSuoAttributo` (exclusion clause).

---

## A53 — God's causation of a mode is causation under that mode's attribute (Section II)

**Lean signature**:
```lean
ax_cause_refines_to_attribute :
  ∀ (g x : Thing) (a : Attr),
    CausalWorld.Cause g x → modeUnder x a → causeUnder g x a
```

**Why we add it**: Prop. I.XXV's corollary describes particular
things as "*Dei attributorum affectiones sive modi quibus Dei
attributa certo et determinato modo exprimuntur*" — a mode expresses
a **definite** attribute. Combined with
`prop_16_cor1_godEfficientCause` (Prop. I.XVI cor. I, already
mechanised: God is efficient cause of every mode), this refines the
bare causal claim into the *quatenus* form.

**Commentary**: this axiom adds **relativisation, not causation**.
The causal fact it consumes is a Pars I theorem, not a new
commitment; what A53 supplies is the claim that God's causing of a
mode happens *under* the attribute the mode belongs to rather than
under some other or under none. Curley 1969 ch. 2 treats exactly
this as what "*certo et determinato modo*" is doing in the Prop.
XXV corollary. This is why Prop. II.VI's positive clause is a
derivation here rather than a 📜 commitment.

**Used by**: `prop_2_6_modiSubSuoAttributo` (positive clause).

---

## A54 — Ideas are modes of thought (Section II — Prop. V's *demonstratio*)

**Lean signature**:
```lean
ax_idea_modeUnder_cogitatio :
  ∀ i x : Thing, ideaOf i x → modeUnder i (cogitatio Thing)
```

**Why we add it**: Prop. V's first *demonstratio* opens "*Esse
formale idearum modus est cogitandi (ut per se notum)*" — that the
formal being of an idea is a mode of thinking is, Spinoza says,
self-evident. We record it as the bridge it is rather than leave it
tacit.

**Commentary**: "*ut per se notum*" is precisely the marker this
project treats as a promotion candidate — a step Spinoza declines to
argue for. It is Section II rather than III because he *states* it;
the classification tracks whether the sentence is in the text, not
whether it is argued. This axiom is what turns Prop. VI into Prop.
V: the latter is the former specialised to `a := cogitatio`.

**Used by**: `prop_2_5_ideaeSubCogitatione`, hence
`prop_2_5_cor_nonSubExtensione`.

---

## A55 — The idea order reflects back to things (Section II — Prop. VII's "*idem est*")

**Lean signature**:
```lean
ax_idea_order_reflects :
  ∀ ic ie : Thing, CausalWorld.Cause ic ie →
    ∀ c e : Thing, ideaOf ic c → ideaOf ie e → CausalWorld.Cause c e
```

**Why we add it**: A50 carries the causal order from things to
ideas, which is the direction Prop. VII's *demonstratio* establishes
(via Ax. I.4). But Spinoza's **statement** is an identity — "*ordo
et connexio idearum idem est ac ordo et connexio rerum*" — and an
identity is symmetric. A55 is the other direction; with A50 it
delivers `prop_2_7_ordoEtConnexio_iff`.

**Commentary**: classified Section II on the ground that asserting
only one direction *misreads* the connective. "*Idem est ac*" is not
"*sequitur ex*"; a formalisation that renders it as a one-way
implication has weakened the sentence, not been cautious about it.
Della Rocca 1996 ch. 6 makes the symmetry central to the
parallelism doctrine.

**Open**: this closes GAP-27a only. The scholium's stronger claim —
that a mode of extension and its idea are "*una eademque res sed
duobus modis expressa*", one and the same *thing* rather than two
things in matching orders — needs cross-attribute identity of modes
and remains **GAP-27b**. A55 is about two *orders* coinciding; the
scholium is about two *things* being one.

**Used by**: `prop_2_7_ordoEtConnexio_iff`.

---

# *Esse objectivum*-layer auxiliary axioms (A56–A59)

Introduced by `Ethica/Pars2/Parallelismus.lean` (batch 1.3: Prop.
II.VII cor., Props. II.VIII and II.IX with their corollaries). All
live in `ParallelismusAxioms`, which extends `QuatenusAxioms`.

**Three Section II, one Section III.** The Section III one is A59,
and it is not new content: it is A42's commitment (Prop. I.XXVIII)
restated on a predicate that can actually be satisfied. So the
batch's net new metaphysics is zero, and its net new *usable*
metaphysics is a proposition Pars I had already paid for and could
not draw on.

**The definitions this layer rests on are not axioms.** `Parallelismus.lean`
also supplies

```lean
sameNatureUnder x y        ≝ ∃ a : Attr, modeUnder x a ∧ modeUnder y a
finitumInSuoGenereModal x  ≝ ∃ y, x ≠ y ∧ sameNatureUnder x y ∧ limitedBy x y
ResSingularis x            ≝ Mode x ∧ finitumInSuoGenereModal x
```

which is Pars II Def. VII, and the `hasAttribute` relation
`Definitions.lean` promised "*at the modal layer*". It closes the
GAP-2 caveat at the cost of exposing that **A42 never fires** — see
`pars1_prop_28_vacuous_for_modes` and A59 below.

Consistency witness for all four:
`Ethica/Pars2/Models/MensWitness.lean`, whose carrier gained a third
constructor (`res : Int → MensThing`) for this batch. A56 is
discharged **non-vacuously** (`durat` splits the carrier:
`mens_durat_splits`), A57 by the recursive clause of `mensDurat`,
A58 by `mens_singularis_of_index`, and A59 by `mens_pred_cause` —
which is why the index type has to be `Int`: on `Nat` the causal
chain would bottom out and A59 would be **false** in the model.

---

## A56 — Prop. VIII's containment biconditional (Section II, 📜 Prop. II.VIII)

**Lean signature**:
```lean
ax_prop8_esseObjectivum :
  ∀ (x i ig g : Thing), ResSingularis (Attr := Attr) x → ¬ durat x →
    ideaOf i x → IsGod g → ideaOf ig g →
      (comprehensaIn i ig ↔ ∃ a : Attr, essentiaFormalisIn x a)
```

**Why we add it**: Prop. VIII reads "*Ideæ rerum singularium sive
modorum non existentium ita debent comprehendi in Dei infinita idea
ac rerum singularium sive modorum essentiæ formales in Dei
attributis continentur*", and its entire *demonstratio* is "*Hæc
propositio patet ex præcedenti sed intelligitur clarius ex
præcedenti scholio*". Spinoza offers it as a **restatement** of Prop.
VII in the register of containment, not as a new commitment — hence
Section II rather than the 📜-pattern's usual Section III, even
though the axiom carries the proposition's content.

The "*ita … ac*" is a comparison of manner. What the corollary
actually draws on, and what this field states, is that the two
containments hold **together**: for a singular thing that does not
endure, its idea is comprehended in God's infinite idea iff its
formal essence is contained in some attribute.

Note that God's infinite idea is **not** a new primitive. It is the
idea of God, which A49 already guarantees exists; the `IsGod g` and
`ideaOf ig g` hypotheses pick it out. That is a small piece of
economy worth naming: Prop. VIII looks like it needs a distinguished
object and does not.

**Commentary**: Curley 1969 ch. 2 reads Prop. VIII as the point where
Spinoza's *esse objectivum* stops being a scholastic borrowing and
starts doing work — non-existent things have ideas, so the attribute
of thought is not indexed to actuality. Bennett 1984 §37 is harsher,
calling the rectangles-in-a-circle scholium "an analogy that
explains an obscurity by a clarity that does not resemble it"; on
his reading the manner-comparison is precisely the part that should
not be formalised, which is convenient, since it is the part we do
not formalise.

**Open**: the manner-comparison itself. Capturing "*in the same way
as*" would need a sameness-of-manner relation ranging over the two
containment predicates. Not committed; not tracked as a separate gap
because no downstream proposition consumes it.

**Used by**: `prop_2_8_ideaeRerumNonExistentium`.

---

## A57 — An idea endures iff its object endures (Section II — Prop. VIII cor.)

**Lean signature**:
```lean
ax_idea_durat_iff :
  ∀ i x : Thing, ideaOf i x → (durat i ↔ durat x)
```

**Why we add it**: Prop. VIII's corollary states both halves.
Negatively: "*quamdiu res singulares non existunt nisi quatenus in
Dei attributis comprehenduntur, earum esse objectivum sive ideæ non
existunt nisi quatenus infinita Dei idea existit*". Positively:
"*ubi res singulares dicuntur existere … earum ideæ etiam
existentiam per quam durare dicuntur, involvent*". A biconditional
is the compact form of the pair, and Spinoza asserts each half in
turn.

**Commentary**: this is the corollary that keeps the parallelism
from being a claim about eternal structure only. Della Rocca 1996
ch. 6 notes that without it, Prop. VII would be compatible with an
idea-order that never changes while the thing-order does — which
would make the *idem est* an equivocation.

Note what A57 does **not** say: nothing here makes `durat`
interesting on its own. A model may leave it empty, or universal,
and satisfy A57 either way. The consistency witness deliberately
makes it split the carrier so Prop. VIII is tested on both sides.

**Used by**: `prop_2_8_cor_esseObjectivum`,
`prop_2_8_cor_nonExistente`.

---

## A58 — The idea of a singular thing is itself singular (Section II — Prop. IX's *demonstratio*)

**Lean signature**:
```lean
ax_idea_singularis :
  ∀ i x : Thing, ideaOf i x → ResSingularis (Attr := Attr) x →
    ResSingularis (Attr := Attr) i
```

**Why we add it**: Prop. IX's *demonstratio* opens "*Idea rei
singularis actu existentis modus singularis cogitandi est et a
reliquis distinctus (per corollarium et scholium propositionis 8
hujus)*". The modehood and the attribute are already available — A54
makes every idea a mode of thought. What this field adds is the
**finitude**: that the idea is limited by other ideas, hence a *res
singularis*.

The addition is load-bearing rather than decorative. Without it the
regress of Prop. IX could not stay inside the class of singular
things, and A59 could not be reapplied at the next rung — which is
to say the "*et sic in infinitum*" would stop after one step.

**Commentary**: Spinoza's citation is to Prop. VIII's corollary and
scholium, i.e. to the rectangles: what distinguishes the ideas of
the two existing rectangles E and D from the ideas of all the rest
is that they involve those rectangles' existence. That is an
argument for distinctness, which is the "*a reliquis distinctus*"
half; the finitude half he takes as read. We record the whole
sentence as one bridge rather than pretend the second half was
argued.

**Used by**: `prop_2_9_deusQuatenusCogitans` (supplies the `Mode i`
Prop. V needs), `prop_2_9_ideaSingularisAbAliaIdea`.

---

## A59 — Every singular thing is caused by another singular thing (Section III, 📜 Prop. I.XXVIII at the modal layer)

**Lean signature**:
```lean
ax_singulare_causatum :
  ∀ x : Thing, ResSingularis (Attr := Attr) x →
    ∃ y : Thing, ResSingularis (Attr := Attr) y ∧ y ≠ x ∧
      CausalWorld.Cause y x
```

**Why we add it**: **this is A42 repaired, not A42 duplicated.**

A42 (`ax_finiteMode_causedByFiniteMode`, `Consecutio.lean`) states
exactly this claim using Pars I's `finitumInSuoGenere`. That
predicate unfolds through `sameNature`, which GAP-2 path (b) defined
as `∃ a, Attribute a x ∧ Attribute a y` — and `Attribute a s`
carries `Substance s`. So `finitumInSuoGenere x` **entails**
`Substance x`, and substances are provably disjoint from modes.
A42's hypothesis `Mode x ∧ finitumInSuoGenere x` is therefore
unsatisfiable in **every** `Pars1Axioms` world:

```lean
theorem pars1_prop_28_vacuous_for_modes :
    ¬ ∃ x : Thing, Mode x ∧ finitumInSuoGenere x
```

A42's own docstring calls it "the backbone of finite-mode causation
that Pars II–V consume throughout". It is not usable as such: it is
committed and never fires. A59 is the same commitment on
`ResSingularis`, which modes can satisfy.

Everything A42's entry says about the *demonstratio* applies
verbatim, and is not repeated here: Spinoza chains Props. XXI and
XXII with Prop. XXIII's trichotomy (now A44), and the direct
commitment to the conclusion is the honest minimal form.

**Why not simply strengthen A42?** Because `Ethica/Pars1/` is frozen
at v1.0.0 — the published irreducibility results (arXiv:2605.02331)
are anchored to that register, and editing `Definitions.lean`'s
`sameNature` would move all thirteen Pars I models and both demote
results. The repair goes in the parallel branch, exactly as GAP-25's
did. The frozen A42 stays where it is, with a vacuity theorem beside
it rather than a silent correction.

**Commentary**: the vacuity is not a defect of Spinoza's Def. II. It
is a consequence of resolving GAP-2 by *defining* sameness of nature
through `Attribute` — a good move for Prop. II, whose subject really
is substances, and one whose cost `Definitions.lean` flagged in the
same breath ("*For inter-mode or mode-vs-substance 'same kind'
comparisons … a separate `hasAttribute` relation will be added at
the modal layer*"). This is that layer, and this is that cost.

Bennett 1984 §21's objection to Prop. XXVIII — that the infinite
regress of finite causes is asserted rather than argued — stands
undisturbed, and is why A59 is Section III rather than II.

**Used by**: `prop_2_9_ideaSingularisAbAliaIdea`, hence
`prop_2_9_cor_nullaPrimaIdea`.

---

## Note on the extension classes

The Attributum layer re-types the `Pars1Axioms` attribute axioms
only. The attribute quantifiers in the *extension* classes — A29
(`Theologia.lean`), A40 (`Consecutio.lean`), A44
(`Classificatio.lean`) — are not yet re-typed; they are re-typed as
Pars II consumes them. Tracked in `gaps.md` GAP-25's residue note
rather than as a separate gap.
