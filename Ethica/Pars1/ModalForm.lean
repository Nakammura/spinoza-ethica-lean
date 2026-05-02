/-
  Spinoza, *Ethica* Pars I — Modal layer.

  Possible-world reconstruction of Spinoza's *Ethica* Pars I.
  Bridge axioms link world-relative primitives (`existsAt`,
  `causeAt`) and world-invariant primitives (`conceptualDep`)
  to the base `EthicaWorld` predicates, so the modal layer is
  fully connected to Pars1Axioms / CausalAxioms.

  Design choices
  --------------
  * **No Mathlib dependency** at this layer. Spinoza's modal
    content can be expressed with Lean-core `Prop`-valued
    accessibility relations parameterised by an abstract `World`
    type.
  * **Possible-world semantics, S5-flavoured** with universal
    accessibility (Della Rocca 2008 ch. 2).
  * **Three primitive classes**, each paired with an axioms class:
    - `ModalEthicaWorld Thing World` (data) +
      `ModalEthicaAxioms Thing World` (Prop) for world-relative
      existence and its bridge to `involvesExistence`.
    - `ConceptualStructure Thing` (data) + `ConceptualBridges Thing`
      (Prop) for world-invariant conceptual dependence and its
      bridges to `perSeConceived` / `conceivedThroughAnother`.
    - `ModalCausalWorld Thing World` (data) +
      `ModalCausalAxioms Thing World` (Prop) for world-relative
      causation, A3 substantive, and the bridge to `Cause`.
  * **Della Rocca interpretation explicitly committed**: the
    `World`-invariance of `conceptualDep` and the bridges
    `involvesExistence ↔ ∀ w, existsAt` and `Cause ↔ ∀ w, causeAt`
    are PSR-flavoured. **Bennett-line readers** (who hold conceptual
    dependence is itself revisable across conceptual schemes, or
    who deny the essential-existence ↔ necessary-existence
    biconditional) would need a different layer where these
    primitives are world-relative or independent. The current
    layer is **not Bennett-neutral**; it is the Della-Rocca-line
    formalisation, with the commitment cost made visible at the
    typing surface.

  Diamond inheritance
  -------------------
  Multiple classes (`ConceptualStructure`, `ModalEthicaWorld`,
  `CausalWorld`, `ModalCausalWorld`) extend `EthicaWorld`. When
  constructing a model that needs more than one, share a single
  `EthicaWorld` instance using the `toEthicaWorld := inferInstance`
  pattern:
  ```
  instance : EthicaWorld T := ...
  instance : ConceptualStructure T :=
    { toEthicaWorld := inferInstance, ... }
  instance : ModalEthicaWorld T W :=
    { toEthicaWorld := inferInstance, ... }
  ```
  This avoids the diamond divergence Lean 4's structure inheritance
  does not enforce automatically.

  ## Note on the implementation cost of separation
  -----------------------------------------------

  The four modal-layer structures (`ModalEthicaWorld`,
  `ConceptualStructure`, `ModalCausalWorld`, plus their axiom
  classes) cannot be merged into a single typeclass without
  introducing diamond inheritance from `EthicaWorld`. The
  cost — visible as `@`-application verbosity in cross-structure
  proofs (see `Models/SingleSubstance.lean` examples) — is itself
  **philosophical evidence**: Spinoza's PSR-driven *monism*
  (Della Rocca 2008 ch. 2), under which existence, conception, and
  causation are unified by sufficient reason, **cannot be directly
  expressed in Lean 4's type system**. Bennett 1984 §16's analytic
  decomposition of these concepts into separable claims is what
  Lean *naturally enforces*.

  That is, the engineering separation we were forced to adopt
  (data class + axiom class for each of existence, conception,
  causation) is the mechanical reflection of Bennett's analytic
  reading of Spinoza's modal/conceptual concepts. A genuine
  Della-Rocca formalisation — concepts unified at the type
  level — would need a typeclass mechanism Lean 4 does not
  provide. The engineering cost is not a workaround: it is a
  Bennett-line trace in the formalisation itself.

  Status of GAP attempts after this commit
  ----------------------------------------
  * **GAP-6** (Prop. I priority): scaffolding plus
    `ConceptualBridges` (definitional, Section I) plus
    `ConceptualDepAxioms` (substantive, Section III candidates
    A16/A17). `prop_1_priority` proved as one-line application of
    `ConceptualDepAxioms`. Remaining: derive
    `ConceptualDepAxioms` fields from PSR + base axioms (Della Rocca
    demote attempt). If it fails, A16/A17 stay in Section III on
    the modal layer.
  * **GAP-7** (A3 ontological): `ModalCausalAxioms` provides A3
    substantive in both clauses (necessitation and the
    "no cause → no effect" clause, which is *not* the
    contrapositive — see below). Bridge `Cause ↔ ∀ w, causeAt`
    now lives as a `ModalCausalAxioms` field, so base-layer
    Causation.lean's `Cause` is connected to the modal layer.
  * **A12 / A13 / A14 / A15 demote attempts**: not in this
    commit. Bridges established here are the prerequisite for
    those attempts.
  * **GAP-8a (cardinality)**: still requires Mathlib's
    `Set.Infinite` or equivalent; deferred.
-/
import Ethica.Pars1.Definitions
import Ethica.Pars1.Axioms
import Ethica.Pars1.Causation

namespace Ethica.Pars1.Modal

universe u v

/-! ## ModalEthicaWorld + ModalEthicaAxioms -/

/-- World-relative existence over `Thing`. Worlds are abstract;
    universal accessibility (S5) is the intended reading. -/
class ModalEthicaWorld (Thing : Type u) (World : Type v)
    extends EthicaWorld Thing where
  /-- `existsAt x w` : the thing `x` exists at world `w`. -/
  existsAt : Thing → World → Prop

/-- Bridge axiom for the modal layer: a thing's essence involves
    existence iff it exists at every world. This is the
    Della-Rocca-flavoured identification of *essential* existence
    (Def. I clause) with *necessary* existence. Without this, the
    `existsAt` primitive floats free of the base layer's
    `involvesExistence`. -/
class ModalEthicaAxioms (Thing : Type u) (World : Type v)
    [ModalEthicaWorld Thing World] : Prop where
  /-- A18 (modal definitional bridge): essential existence is
      necessary existence. -/
  ax_involvesExistence_iff_necExists :
    ∀ s : Thing,
      EthicaWorld.involvesExistence s ↔
        ∀ w : World, ModalEthicaWorld.existsAt s w

/-! ## ConceptualStructure + ConceptualBridges + ConceptualDepAxioms -/

/-- World-invariant conceptual dependence. `conceptualDep x y`
    reads "the conception of `x` requires the conception of `y`".
    Della Rocca 2008 ch. 2: conceptual dependence is essential,
    not contingent — hence world-invariant. Bennett-line readers
    who deny this would couple `conceptualDep` to `World`; the
    current design is not Bennett-neutral (see file-level note). -/
class ConceptualStructure (Thing : Type u)
    extends EthicaWorld Thing where
  /-- `conceptualDep x y` : `x` is conceived through `y`. -/
  conceptualDep : Thing → Thing → Prop

/-- Bridge axioms linking `conceptualDep` to base-layer
    `perSeConceived` and `conceivedThroughAnother`. These are
    definitional bridges (Section I) under the Della-Rocca
    reading. -/
class ConceptualBridges (Thing : Type u)
    [ConceptualStructure Thing] : Prop where
  /-- A19 (modal definitional bridge): `perSeConceived` is the
      absence of conceptual dependence on anything else. -/
  ax_perSe_iff_no_external_dep :
    ∀ x : Thing,
      EthicaWorld.perSeConceived x ↔
        (∀ y : Thing, ConceptualStructure.conceptualDep x y → y = x)
  /-- A20 (modal definitional bridge): `conceivedThroughAnother`
      is conceptual dependence on something distinct from
      oneself. -/
  ax_throughAnother_iff_external_dep :
    ∀ x : Thing,
      EthicaWorld.conceivedThroughAnother x ↔
        (∃ y : Thing, y ≠ x ∧ ConceptualStructure.conceptualDep x y)

/-! ## GAP-6 substantive — Prop. I priority via `conceptualDep`

  Spinoza Prop. I: "Substantia prior est natura suis affectionibus."
  Standard reading (Curley 1988 ch. 1; Bennett 1984 §16): *prior
  natura* = asymmetric conceptual dependence — every mode is
  conceived through some substance, but no substance is conceived
  through any mode.

  Strategy: state the asymmetry as a Section III candidate axiom
  class. The Della Rocca route to demote it requires deriving from
  PSR + Defs III/V; deferred. -/

/-- Section III candidate axioms (A16 + A17): the asymmetric
    conceptual dependence content of Prop. I priority. -/
class ConceptualDepAxioms (Thing : Type u)
    [ConceptualStructure Thing] : Prop where
  /-- A16-candidate: every mode conceptually depends on some
      substance. -/
  ax_mode_depends_on_substance :
    ∀ m : Thing, Mode m →
      ∃ s : Thing, Substance s ∧ ConceptualStructure.conceptualDep m s
  /-- A17-candidate: substances do not conceptually depend on
      modes (asymmetry). -/
  ax_substance_not_dep_on_mode :
    ∀ s m : Thing, Substance s → Mode m →
      ¬ ConceptualStructure.conceptualDep s m

section prop1_priority
variable {Thing : Type u}
  [ConceptualStructure Thing] [ConceptualDepAxioms Thing]
open ConceptualStructure

/-- Prop. I — priority form: every mode depends on some substance;
    no substance depends on any mode. Direct application of
    A16-candidate + A17-candidate. -/
theorem prop_1_priority :
    (∀ m : Thing, Mode m →
        ∃ s : Thing, Substance s ∧ conceptualDep m s)
    ∧
    (∀ s m : Thing, Substance s → Mode m → ¬ conceptualDep s m) :=
  ⟨ ConceptualDepAxioms.ax_mode_depends_on_substance
  , ConceptualDepAxioms.ax_substance_not_dep_on_mode ⟩

end prop1_priority

/-! ## A13 in modal form — first load-bearing use of A18

  Combines A13 (`Pars1Axioms.ax_substance_involves_existence`) with
  A18 (`ModalEthicaAxioms.ax_involvesExistence_iff_necExists`) to
  conclude that every substance exists at every world. This is the
  modal-layer counterpart of A13 and the modal critical-path
  precursor for Prop. XI (God necessarily exists at every world).

  Establishing this theorem turns A18 from a *registered* bridge
  into a *load-bearing* one, which is the role bridge axioms
  must play to count as part of the demonstration scaffold. -/

section substance_exists_at_every_world
-- Note: we list `[ModalEthicaWorld Thing World]` *before*
-- `[Pars1Axioms Thing]`. ModalEthicaWorld provides EthicaWorld via
-- `toEthicaWorld`, and Pars1Axioms's EthicaWorld dependence will
-- be unified through that path. Listing `[EthicaWorld Thing]`
-- explicitly here would create a second visible instance and
-- trigger diamond instance-resolution ambiguity (the cost flagged
-- in the file-level "implementation cost of separation" note).
variable {Thing : Type u} {World : Type v}
  [ModalEthicaWorld Thing World] [Pars1Axioms Thing]
  [ModalEthicaAxioms Thing World]
open EthicaWorld ModalEthicaWorld

/-- Modal A13: every substance exists at every world. Proof:
    A13 (substance involves existence) + A18 (essential existence
    ↔ necessary existence). -/
theorem substance_exists_at_every_world
    (s : Thing) (hs : Substance s) : ∀ w : World, existsAt s w :=
  (ModalEthicaAxioms.ax_involvesExistence_iff_necExists s).mp
    (Pars1Axioms.ax_substance_involves_existence s hs)

end substance_exists_at_every_world

/-! ## ModalCausalWorld + ModalCausalAxioms -/

/-- Modal causal layer: extends `ModalEthicaWorld` for `existsAt`
    and adds `causeAt : Thing → Thing → World → Prop` for
    world-relative causation. Note we do **not** extend
    `CausalWorld Thing` — Lean 4 cannot synthesise the inheritance
    instance because `CausalWorld` does not mention `World`, and
    Lean would have no way to recover `World` when looking up a
    `CausalWorld Thing` instance from a `ModalCausalWorld Thing W`.
    Code that needs both should declare them as separate
    requirements. The bridge between `CausalWorld.Cause` and
    `causeAt` lives in `ModalCausalAxioms`. -/
class ModalCausalWorld (Thing : Type u) (World : Type v)
    extends ModalEthicaWorld Thing World where
  /-- `causeAt c e w` : at world `w`, `c` is a determinate cause of
      `e`. -/
  causeAt : Thing → Thing → World → Prop

/-- Modal causal axioms. Requires both `ModalCausalWorld Thing
    World` and `CausalAxioms Thing` (the latter brings `Pars1Axioms`
    and `CausalWorld` along transitively). The bridge axiom
    `ax_cause_iff_necCauseAt` references `CausalWorld.Cause` and so
    needs `CausalAxioms` in scope.

    Same diamond rationale as `ModalCausalWorld`: not declaring
    `extends CausalAxioms` because the `World` parameter would be
    un-recoverable from a `CausalAxioms Thing` lookup. -/
class ModalCausalAxioms (Thing : Type u) (World : Type v)
    [ModalCausalWorld Thing World]
    [CausalWorld Thing] [CausalAxioms Thing] : Prop where
  /-- A3 first clause (cause necessitates effect): if `c` is a
      determinate cause of `e` at world `w`, then `e` exists at `w`.
      The ontological reading distinct from A4's epistemic
      reading. -/
  ax3_causeNecessitatesEffect :
    ∀ c e : Thing, ∀ w : World,
      ModalCausalWorld.causeAt c e w → ModalEthicaWorld.existsAt e w

  /-- A3 second clause (existence requires a cause): if no
      determinate cause obtains at `w`, no effect obtains at `w`.

      This is **not** the contrapositive of
      `ax3_causeNecessitatesEffect` (which would be automatic in
      classical logic). It is a substantively distinct commitment
      ruling out *spontaneously arising* effects. Spinoza's "si
      nulla detur determinata causa" requires both clauses for the
      full A3 reading; Bennett 1984 §15 discusses this two-clause
      structure of A3. -/
  ax3_noCauseNoEffect :
    ∀ e : Thing, ∀ w : World,
      (¬ ∃ c : Thing, ModalCausalWorld.causeAt c e w) →
      ¬ ModalEthicaWorld.existsAt e w

  /-- A21 (modal definitional bridge): the world-uniform `Cause`
      from `Causation.lean` is exactly necessary causation in the
      modal sense — `c` causes `e` iff `c` causes `e` at every
      world. Della Rocca 2008 ch. 2's reading; Bennett-line readers
      who hold causation can be world-relative would weaken this
      to `→` only. -/
  ax_cause_iff_necCauseAt :
    ∀ c e : Thing,
      CausalWorld.Cause c e ↔
        ∀ w : World, ModalCausalWorld.causeAt c e w

/-! ## §δ — Demote attempt for A12 via PSR (Della Rocca route)

  This section commits a Principle-of-Sufficient-Reason axiom for
  substance distinguishability and attempts to **demote** A12
  (`Pars1Axioms.ax_substanceIdByAttribute`, currently a Section
  III commitment) from axiom to theorem.

  ### Setup: PSR for substance distinguishability

  Della Rocca 2008 ch. 2's reading of Spinoza's PSR for substances:
  if two substances are distinct, their distinction has a
  sufficient reason; per Prop. IV the only available reason is an
  attribute difference (modes are posterior, Prop. I priority); so
  distinct substances must differ in some attribute. We commit
  this as a single modal-layer axiom:

  ```
  ∀ s₁ s₂, Substance s₁ → Substance s₂ → s₁ ≠ s₂ →
    ∃ a, (Attribute a s₁ ∧ ¬ Attribute a s₂) ∨
         (Attribute a s₂ ∧ ¬ Attribute a s₁)
  ```

  ### What demotes (partial success)

  With PSR and the base layer, we can derive a **partial** form of
  A12: substances sharing **all** attributes are identical. Proof:
  if distinct, PSR provides a discriminating attribute, contradicting
  shared-all-attributes.

  ### What does **not** demote (the predicted failure)

  Full A12 — substances sharing **any** attribute (one or more) are
  identical — is **strictly stronger**. PSR-distinguishability only
  rules out the case where there is **no** attribute distinguishing
  the two; it does not exclude the case where two substances share
  some attributes but differ on others. The any-shared-attribute
  reading of A12 (Spinoza's "ejusdem naturae sive attributi") goes
  beyond what PSR alone licenses.

  Bennett 1984 §17 makes essentially this point in prose: PSR rules
  out indiscernibles, but Spinoza's Prop. V demands more — that
  even **partial** attribute-sharing forces identity. The
  mechanical finding here is the predicted failure: PSR demotes A12
  partially, not fully. The remaining content of A12 — the strong
  individuation by *each* attribute, Curley / Garrett's strong
  reading of Def. III — must be retained as a separate Section III
  commitment.

  This is the **first mechanical evidence in the project for the
  Bennett line**: a Section III axiom predicted to be irreducible
  to PSR has been confirmed irreducible at the type level.
-/

/-- PSR axiom for substance distinguishability (Della Rocca 2008
    ch. 2). A modal-layer Section III commitment. -/
class PSRSubstance (Thing : Type u) [EthicaWorld Thing] : Prop where
  /-- A22 (PSR for substance distinguishability): distinct
      substances differ in at least one attribute. -/
  ax_PSR_substance_distinguishability :
    ∀ s₁ s₂ : Thing, Substance s₁ → Substance s₂ → s₁ ≠ s₂ →
      ∃ a : Thing,
        (Attribute a s₁ ∧ ¬ Attribute a s₂) ∨
        (Attribute a s₂ ∧ ¬ Attribute a s₁)

section demote_attempt
variable {Thing : Type u} [EthicaWorld Thing] [PSRSubstance Thing]

/-- **Partial demote of A12 via PSR**: substances sharing **all**
    attributes are identical. This is the half of Prop. V that
    PSR delivers. Proof: classical contradiction — if distinct,
    PSR provides a discriminating attribute, contradicting
    `share-all`.

    This theorem demonstrates that A12's content is *partially*
    derivable from PSR. The remaining gap (any-shared-attribute)
    is documented in `A12_full_NOT_demotable`. -/
theorem prop_5_demote_via_PSR_all_attributes
    (s₁ s₂ : Thing) (hs₁ : Substance s₁) (hs₂ : Substance s₂)
    (hshare_all : ∀ a, Attribute a s₁ ↔ Attribute a s₂) : s₁ = s₂ :=
  Classical.byContradiction fun hne => by
    obtain ⟨a, h⟩ :=
      PSRSubstance.ax_PSR_substance_distinguishability s₁ s₂ hs₁ hs₂ hne
    cases h with
    | inl h => exact h.2 ((hshare_all a).mp h.1)
    | inr h => exact h.2 ((hshare_all a).mpr h.1)

-- **Mechanical finding (Bennett-line evidence #1)**: full A12 is
-- NOT demotable from PSR alone. The evidence is **a counter-model**,
-- not a `True` marker theorem. See
-- `Ethica/Pars1/Models/Counterexamples.lean`,
-- `A12CounterModel`: a 4-element `EthicaWorld` + `PSRSubstance`
-- instance where two distinct substances share an attribute,
-- falsifying A12. If A12 were derivable from `[PSRSubstance T] +
-- [EthicaWorld T]`, the derivation would yield `False` on this
-- model — but `False` is not provable, hence A12 is not derivable.
-- Bennett 1984 §17 makes this point in prose; the project
-- mechanises it via the counter-model. (Review of 2026-05-03
-- §A.2 retired the previous `: True := trivial` marker as
-- Lean-as-rhetoric.)

end demote_attempt

/-! ## §δ-2 — Demote attempt for A13 via PSR self-causation

  A13 (`Pars1Axioms.ax_substance_involves_existence`) says
  `∀ s, Substance s → involvesExistence s`. Under A18 (modal
  bridge), this is equivalent to
  `∀ s, Substance s → ∀ w, existsAt s w`. We attempt to demote A13
  by introducing a single PSR-flavoured commitment about
  self-causation, then deriving the modal A13 form from it via
  the existing modal infrastructure (A3-first-clause + A18).

  ### The new commitment

  ```
  ax_substance_self_caused_at_every_world :
    ∀ s : Thing, ∀ w : World, Substance s → causeAt s s w
  ```

  Della Rocca 2008 ch. 2's reading: every substance is *causa sui*,
  and this self-causation holds at every possible world (causation
  being essential, world-invariant per A21). The PSR-flavoured
  commitment is "every substance has a sufficient reason for its
  existence, namely itself".

  ### What demotes (full success — but with caveats)

  With the new axiom A23, we can derive
  `Substance s → ∀ w, existsAt s w` directly via A3-first-clause
  (cause at w → effect exists at w). Combined with A18 (bridge to
  base-layer `involvesExistence`), this reproduces A13's content.

  ### Mechanical finding: this is a *modal translation*, not a
  *reduction*

  Unlike A12 — where the partial demote captured strictly less than
  A12's content (review §δ above) — A13 fully demotes here. But the
  philosophical price is that **A23 is not weaker than A13**: it
  asserts substance self-causation at every world, which is the
  modal-form content of A13. The demote is a translation between
  two equivalent expressions of "substance has necessary
  existence", not a derivation from genuinely weaker premises.

  Compare to A12:
  - A12 *partial demote*: PSR delivers only the all-shared-attribute
    case; full A12 is **strictly stronger** than what's delivered.
    Bennett-line evidence for irreducibility.
  - A13 *full demote via translation*: the modal-form A23
    delivers full A13 via existing bridges (A18, A3-first-clause).
    But A23 is itself at the same commitment-strength tier as A13
    — it's a redescription, not a reduction.

  This asymmetry is itself the philosophical content: A12's
  universality clause has no modal equivalent in the available
  vocabulary, while A13's existence clause does have one (via
  modal causation). A12 is **irreducibly substantive**; A13 is
  **modally translatable**.

  Bennett 1984 §17 vs Della Rocca 2008 ch. 2: Bennett's
  irreducibility claim survives intact for A12; for A13, both
  readings can claim partial victory — Della Rocca that A13 is
  "really" the modal A23, Bennett that the commitment hasn't
  decreased in strength.
-/

/-- PSR axiom for substance self-causation at every world.
    Modal-layer Section III commitment, A23 in
    `auxiliary_axioms.md`. -/
class PSRSelfCause (Thing : Type u) (World : Type v)
    [ModalCausalWorld Thing World] : Prop where
  /-- A23 (PSR for substance self-causation): every substance is
      its own cause at every world. -/
  ax_substance_self_caused_at_every_world :
    ∀ s : Thing, ∀ w : World, Substance s →
      ModalCausalWorld.causeAt s s w

section a13_demote
-- The instance dependencies are listed minimally. ModalCausalWorld
-- transitively provides ModalEthicaWorld and EthicaWorld. We must
-- still list CausalWorld + CausalAxioms because ModalCausalAxioms
-- requires them as separate args (cf. modal layer's diamond
-- discipline).
variable {Thing : Type u} {World : Type v}
  [ModalCausalWorld Thing World]
  [CausalWorld Thing] [CausalAxioms Thing]
  [ModalEthicaAxioms Thing World]
  [ModalCausalAxioms Thing World]
  [PSRSelfCause Thing World]
open EthicaWorld ModalEthicaWorld ModalCausalWorld

/-- **Full demote of A13 via modal translation**: under A18 + A23
    + A3-first-clause, every substance's essence involves
    existence. Proof chain: A23 gives self-causation at every
    world; A3-first-clause turns each into existence at that
    world; A18 bridges to `involvesExistence`.

    This proves the **same content** as A13
    (`Pars1Axioms.ax_substance_involves_existence`) without
    appealing to A13 itself. Demote successful — but A23 is not
    weaker than A13 (see file-level §δ-2 note). -/
theorem prop_7_demote_via_PSR
    (s : Thing) (hs : Substance s) : involvesExistence s := by
  -- Step 1: A23 gives causeAt s s w for every w.
  have hself : ∀ w : World, ModalCausalWorld.causeAt s s w := fun w =>
    PSRSelfCause.ax_substance_self_caused_at_every_world s w hs
  -- Step 2: A3-first-clause turns each causeAt into existsAt.
  have hexists : ∀ w : World, ModalEthicaWorld.existsAt s w := fun w =>
    ModalCausalAxioms.ax3_causeNecessitatesEffect s s w (hself w)
  -- Step 3: A18 bridges ∀ w, existsAt to involvesExistence.
  exact (ModalEthicaAxioms.ax_involvesExistence_iff_necExists s).mpr
    hexists

end a13_demote

/-! ## §δ-3 — Demote attempt for A14 via PSR essence-perception

  A14 (`Pars1Axioms.ax_substance_has_attribute`) says
  `∀ s, Substance s → ∃ a, Attribute a s`. The Della Rocca route:
  every substance is intelligible (PSR), and intelligibility is
  mediated by attributes (Def. IV); hence every substance has at
  least one attribute.

  ### The new commitment

  ```
  ax_substance_has_essence_perception :
    ∀ s : Thing, Substance s → ∃ a, intellectPerceivesAsEssence s a
  ```

  ### What demotes (full success — but trivially so)

  Unfolding `Attribute a s := Substance s ∧ intellectPerceivesAsEssence
  s a`, the new axiom delivers A14's content immediately. The proof
  is two lines.

  ### Mechanical finding: A14 is a *trivial redescription* of an
  essence-perception axiom

  A24-candidate is **logically equivalent** to A14 (modulo the
  vacuous `Substance s` re-attachment). The "demote" is even more
  obviously not a reduction than A13's case — A24 has the exact
  same `∀ s, Substance s → ∃ a, …` shape as A14, with `Attribute a s`
  replaced by its only non-trivial component
  `intellectPerceivesAsEssence s a`. Equal commitment-strength;
  just different surface vocabulary.

  ### Why the demote succeeds for A14 but not for A12 / A15

  A14 is itself an *existence* claim (each substance has *some*
  attribute, ∃-quantified), so PSR-flavoured axioms with a
  matching existence-explanatory shape demote it cleanly. The
  irreducibility-to-PSR phenomenon belongs to A15, where the
  universality is over *attributes* (god has *every* substance's
  attribute) — this is the genuinely universal clause, and its
  demote attempt is in §δ-4.

  ### Resulting taxonomy after §δ, §δ-2, §δ-3

  - **A12**: PSR demote *partial only*; full content irreducible.
  - **A13**: PSR demote *full success via modal translation*; A23
    is a redescription at equal strength. Both Bennett and
    Della Rocca readings claim partial victory.
  - **A14**: PSR demote *full success, trivially*; A24-candidate
    is equivalent in shape and strength to A14.
  - **A15**: see §δ-4.
-/

/-- PSR axiom for substance-essence perception. Modal-layer
    Section III commitment, A24 in `auxiliary_axioms.md`. -/
class PSREssencePerception (Thing : Type u) [EthicaWorld Thing] :
    Prop where
  /-- A24 (PSR for essence perception): every substance has an
      essence-perception, i.e. there exists something the intellect
      perceives as constituting its essence. -/
  ax_substance_has_essence_perception :
    ∀ s : Thing, Substance s →
      ∃ a, EthicaWorld.intellectPerceivesAsEssence s a

section a14_demote
variable {Thing : Type u} [EthicaWorld Thing] [PSREssencePerception Thing]

/-- **Full demote of A14 via PSR essence-perception**: every
    substance has at least one attribute. Proof: take the
    perception promised by A24 and pair it with the substance
    hypothesis to construct an `Attribute`. -/
theorem prop_A14_demote_via_PSR
    (s : Thing) (hs : Substance s) : ∃ a, Attribute a s := by
  obtain ⟨a, h⟩ :=
    PSREssencePerception.ax_substance_has_essence_perception s hs
  exact ⟨a, hs, h⟩

end a14_demote

/-! ## §δ-4 — Demote attempt for A15: irreducibility of universality

  A15 (`Pars1Axioms.ax_IsGod_has_attribute_of`) says:

    ∀ g s a, IsGod g → Substance s → Attribute a s → Attribute a g

  Universal over attributes: every realised attribute belongs to
  every god. This is the genuine universality clause Bennett 1984
  §17 / §18 identifies as resistant to PSR-style derivation.

  ### Plenitude alone fails

  The natural Della Rocca commitment is **plenitude**: every
  substance's attribute belongs to *some* god.

    ax_plenitude_attribute :
      ∀ a s, Substance s → Attribute a s →
        ∃ g, IsGod g ∧ Attribute a g

  Attempting to derive A15 from plenitude alone:
  ```
  -- Hypothesis: IsGod g, Substance s, Attribute a s.
  -- Plenitude: ∃ g', IsGod g' ∧ Attribute a g'.
  -- Want: Attribute a g.
  -- We have: g, g' (both gods), Attribute a g'.
  -- We do NOT have: g = g'.
  -- ⊥ — proof gets stuck without uniqueness of god.
  ```

  Plenitude is genuinely weaker than A15: in a model with two
  gods having different attributes, plenitude can hold while A15
  fails. Hence plenitude alone does not deliver A15.

  ### Plenitude + uniqueness-of-god demotes — at the cost of
  *two* axioms

  Adding god uniqueness:

    ax_god_unique :
      ∀ g₁ g₂, IsGod g₁ → IsGod g₂ → g₁ = g₂

  We can now prove A15: plenitude gives `g'` with the attribute;
  uniqueness collapses `g = g'`; substitution delivers the goal.
  But uniqueness-of-god is essentially Prop. XIV's content (which
  in our system depends on A15). Stating it as an *axiom* in a
  demote attempt for A15 is: replacing one Section III commitment
  with two, neither weaker than A15.

  ### Mechanical finding: decomposition, not reduction

  A15 demote requires either (a) plenitude + god-uniqueness (two
  Section III commitments) or (b) a single axiom equivalent to
  A15 itself. **No combination of strictly-weaker axioms suffices**
  to derive A15.

  This is **the second mechanical evidence in the project for the
  Bennett line**: PSR-style commitments cannot reduce A15 to a
  weaker form. The universality clause across attributes is
  irreducible to existence-flavoured PSR principles.

  Contrast with the prior demotes:
  * A12: partial only; full content irreducible.
  * A13: full demote, equal strength (modal translation).
  * A14: full demote, equal strength (trivial redescription).
  * A15: full demote *only via decomposition into ≥ 2 axioms*,
    none strictly weaker than A15.

  This completes the demote taxonomy for the four Section III
  axioms (A12, A13, A14, A15) currently committed in `Pars1Axioms`.
  Two patterns of irreducibility emerge: A12 (partial-only) and
  A15 (decomposition-only). Two patterns of equal-strength
  redescription: A13 (modal) and A14 (trivial).
-/

/-- PSR plenitude axiom for attributes. Modal-layer Section III
    commitment, A25 in `auxiliary_axioms.md`. *Strictly weaker*
    than A15 — does not alone deliver A15. -/
class PSRPlenitude (Thing : Type u) [EthicaWorld Thing] : Prop where
  /-- A25 (PSR plenitude): every realised substance attribute is
      also realised in some god. -/
  ax_plenitude_attribute :
    ∀ a s : Thing, Substance s → Attribute a s →
      ∃ g, IsGod g ∧ Attribute a g
  /-- A26 (god uniqueness): all gods are identical. Catalogued
      separately because it is independently load-bearing — when
      paired with plenitude it yields A15. -/
  ax_god_unique :
    ∀ g₁ g₂ : Thing, IsGod g₁ → IsGod g₂ → g₁ = g₂

section a15_demote
variable {Thing : Type u} [EthicaWorld Thing] [PSRPlenitude Thing]

/-- **A15 demote via decomposition**: with plenitude AND god
    uniqueness (two axioms in `PSRPlenitude`), A15's content is
    derivable. Note: this is *not* a reduction — both axioms are
    Section III strength, and uniqueness-of-god is essentially
    Prop. XIV's content stated as axiom. The demote replaces one
    commitment with two, none strictly weaker. -/
theorem prop_A15_demote_via_decomposition
    (g s a : Thing) (hgod : IsGod g) (hs : Substance s)
    (ha : Attribute a s) : Attribute a g := by
  obtain ⟨g', hgod', ha_g'⟩ :=
    PSRPlenitude.ax_plenitude_attribute a s hs ha
  have heq : g = g' :=
    PSRPlenitude.ax_god_unique g g' hgod hgod'
  exact heq ▸ ha_g'

-- **Mechanical finding (Bennett-line evidence #2)**: A15 cannot
-- be demoted from plenitude alone. The evidence is **a
-- counter-model**, not a `True` marker theorem. See
-- `Ethica/Pars1/Models/Counterexamples.lean`, `A15CounterModel`:
-- a 3-element `EthicaWorld` instance where plenitude holds (each
-- god is its own attribute-bearer) but A15 fails (g₁ does not
-- have g₂'s additional attribute). This model is not a
-- `PSRPlenitude` instance — god-uniqueness (A26) fails by
-- construction — exactly because uniqueness is the additional
-- commitment plenitude alone cannot supply.
--
-- If A15 were derivable from `[plenitude] + [EthicaWorld T]`
-- (without uniqueness), the derivation would yield `False` on
-- this model. Hence the demote requires the additional
-- god-uniqueness commitment (A26), and A15 is irreducible to
-- plenitude alone. Bennett 1984 §17 / §18 makes this point in
-- prose; the project mechanises it via the counter-model.
-- (Review of 2026-05-03 §A.6 retired the previous `: True :=
-- trivial` marker.)

end a15_demote

/-! ## What is *not* in this commit

  - **A12 / A13 / A14 / A15 demote attempts**. Bridges are now in
    place; demote attempts can be authored next. The strategic
    sequence: try to derive each `Pars1Axioms` Section III axiom
    from PSR + the modal-layer bridges. Success → Della Rocca
    line confirmed; failure → Bennett line confirmed.
  - **A4ₛ-from-A3-substantive demote**. With
    `ax_cause_iff_necCauseAt` and `ax3_causeNecessitatesEffect`,
    the chain is now expressible; deferred.
  - **GAP-8a (cardinality)**. Mathlib import judgement.
  - **Modal-layer instances on `SingleSubstance` / `TwoSubstance`**.
    A `ModalEthicaWorld Unit (Fin 1)` showing S5 modal collapse is
    the natural sanity-check; not in this commit.
-/

end Ethica.Pars1.Modal
