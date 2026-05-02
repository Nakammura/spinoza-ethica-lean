/-
  Spinoza, *Ethica* Pars I — counter-models for irreducibility claims.

  After the demote-attempt series (§δ through §δ-4), the project
  needed mechanical evidence that A12 and A15 are **not derivable**
  from PSR-flavoured commitments alone. Earlier marker theorems
  (`A12_full_NOT_demotable_from_PSR_alone : True := trivial` and
  the analogous A15 marker) used a Lean-as-rhetoric trick — `True`
  proves nothing about provability. Independence results
  (= "P is not derivable from axiom set Σ") are *meta-logical*
  statements about Lean and cannot be expressed as Lean theorems.

  The honest mechanical evidence is **a counter-model**: a concrete
  model that satisfies the alleged premises (e.g. `PSRSubstance`)
  while *falsifying* the conclusion (e.g. A12). If a derivation of
  the conclusion from the premises existed, it would yield `False`
  on this model, hence no such derivation exists.

  This file constructs:
  * **A12 counter-model** — an `EthicaWorld` + `PSRSubstance`
    instance where two distinct substances share an attribute,
    falsifying A12 (`Pars1Axioms.ax_substanceIdByAttribute`).
  * **A15 counter-model** — an `EthicaWorld` instance where two
    `IsGod` substances exist with disjoint attributes such that
    A15 (`Pars1Axioms.ax_IsGod_has_attribute_of`) fails while
    plenitude (A25) holds. Note we do **not** instantiate the
    full `PSRPlenitude` class because god-uniqueness (A26) fails
    by construction; the failure of A26 is itself part of the
    point.

  These are the **kernel-level hard facts** for the two
  Bennett-line irreducibility results in the project.

  Closure-protocol relevance: this file replaces the marker
  theorems removed from `ModalForm.lean` (review of 2026-05-03
  §A.2/§A.6).

  ## Scope of the irreducibility claims (review of 2026-05-03 §4.1)

  These counter-models establish a **strict claim** that is
  weaker than full Bennett-line irreducibility. The strict claim
  for each model:

  * **A12CounterModel**: A12 (`Pars1Axioms.ax_substanceIdByAttribute`)
    is **not provable** from `[EthicaWorld T] + [PSRSubstance T]`
    alone. Any putative derivation would yield `s₁ = s₂` on this
    model, contradicting the model's `s₁ ≠ s₂`.
  * **A15CounterModel**: A15 is **not provable** from
    `[EthicaWorld T] + plenitude alone`. Any putative derivation
    would yield `Attribute attr_g₂ g₁` on this model, contradicting
    the falsifying clause.

  The counter-models do **not** refute derivations of A12 / A15
  from:
  - stronger PSR variants (e.g. PSR over essences, Della Rocca's
    "thoroughgoing" PSR);
  - additional Spinozistic commitments not currently axiomatised
    (e.g. "substance is fully expressible by its attributes",
    Bennett's "substance plenitude", or substance pre-conception);
  - any hypothetical augmented system that adds new typeclasses
    beyond `PSRSubstance` / `PSRPlenitude`.

  **Bennett-line scope**: Bennett 1984 §17 / §18's full claim is
  that Spinoza's Prop. V / Prop. XIV is invalid against *any*
  reasonable augmentation of his stated axioms. Demonstrating
  that full claim would require counter-models surviving every
  augmentation Della Rocca might propose — an open project for
  any Spinoza-Lean formalisation. The counter-models here are
  **first-step evidence for the Bennett line, not closing
  argument**: they refute the specific PSR-flavoured demote
  routes the project has tried, leaving stronger demote routes
  unrefuted (and inviting their construction as future demote
  attempts).

  ## Spinoza fidelity caveats (review of 2026-05-03 §4.2, §4.3)

  Two design choices in the counter-model `EthicaWorld` instances
  are **deliberately Spinoza-unfaithful** in service of compact
  counter-model construction. Documenting them here so future
  readers do not mistake the choices for genuine Spinoza
  modelling:

  1. `expressesEternalEssence _ := True` (set uniformly across
     the universe). Spinoza reserves "expresses eternal essence"
     for *attributes* of substance (Def. VI explanation; Pars II
     Prop. VIII). Setting it `True` for every element of the
     counter-model's universe — including non-substance things
     like `a_shared` or `attr_g₂` — is convenient (it discharges
     `IsGod`'s fourth conjunct vacuously) but flatly contradicts
     Spinoza's restriction.

  2. `inAnother x := ¬ isSubstance x` (and same for
     `conceivedThroughAnother`). This treats every non-substance
     element of the universe as a mode, including
     attribute-things like `a_shared`. Spinoza's three-category
     ontology (substances, attributes, modes) is *conflated* into
     a two-category split (substance / non-substance) in the
     counter-model `Thing` universe. Attributes-as-things, which
     Spinoza treats as essence-aspects of substance rather than
     independent objects, become "modes" in the counter-model.

  Both choices are trade-offs for compact counter-model
  construction. They do **not** affect the meta-logical claim
  the counter-models establish (PSR + base does not derive
  A12 / A15) — the falsification depends only on the
  `intellectPerceivesAsEssence` graph being non-uniform. But a
  Spinoza scholar reading the counter-models should know these
  fidelity gaps before assessing the *philosophical* relevance
  of the irreducibility results to Bennett's reading of
  Spinoza's text.

  A more Spinoza-faithful future iteration could refine
  `expressesEternalEssence` to be attribute-of-substance-only and
  expand the type universe to track Spinoza's three categories
  separately. Cost-benefit calculation favours leaving the
  current compact form for now.

  ## Style note on `A12/A15_irreducibility_witness` definitions
  (review of 2026-05-03 §4.4)

  We use `∃ _ : EthicaWorld T, ∃ _ : Modal.PSRSubstance T, …` to
  package "the typeclass instances exist" inside the irreducibility
  witness definition. The more idiomatic Lean form is `Nonempty
  (EthicaWorld T)` etc. Both are sound; the current form is kept
  for now because the witness `example`s following each definition
  read more naturally with the existential pattern. A future
  refactor to `Nonempty` is a cleanup option but not essential.
-/
import Ethica.Pars1.Definitions
import Ethica.Pars1.ModalForm

namespace Ethica.Pars1.Models.Counterexamples

open Ethica.Pars1
open EthicaWorld

/-! ## Counter-model 1 — A12 not demotable from PSRSubstance alone

  Universe of 4 things: two distinct substances `s₁, s₂` sharing
  an attribute `a_shared`, plus an attribute `a_only_s1` that
  distinguishes them. The latter satisfies `PSRSubstance`'s
  distinguishability requirement; the former falsifies A12.
-/

namespace A12CounterModel

/-- Four-element universe. -/
inductive T where
  | s₁ : T
  | s₂ : T
  | a_shared : T
  | a_only_s1 : T
  deriving DecidableEq

/-- Mark substances. Only `s₁` and `s₂` are substances; `a_shared`
    and `a_only_s1` are merely attribute-things. -/
def isSubstance : T → Prop
  | T.s₁ => True
  | T.s₂ => True
  | _ => False

/-- The intellect-perception graph. `s₁` perceives all three of
    its essence-things (itself, the shared attribute, the
    s₁-only attribute); `s₂` perceives only its own and the
    shared attribute. -/
def perceivesAsEssence : T → T → Prop
  | T.s₁, T.s₁ => True
  | T.s₁, T.a_shared => True
  | T.s₁, T.a_only_s1 => True
  | T.s₂, T.s₂ => True
  | T.s₂, T.a_shared => True
  | _, _ => False

instance ethicaWorld : EthicaWorld T where
  inItself x := isSubstance x
  perSeConceived x := isSubstance x
  involvesExistence x := isSubstance x
  natureRequiresExistence x := isSubstance x
  inAnother x := ¬ isSubstance x
  conceivedThroughAnother x := ¬ isSubstance x
  limitedBy _ _ := False
  intellectPerceivesAsEssence := perceivesAsEssence
  absolutelyInfinite x := isSubstance x
  expressesEternalEssence _ := True
  freelyExistent x := isSubstance x
  constrained x := ¬ isSubstance x
  eternal x := isSubstance x

/-- `T` satisfies `PSRSubstance`: distinct substances differ in
    some attribute. The discriminator between `s₁` and `s₂` is
    `a_only_s1`. -/
instance psrSubstance : Modal.PSRSubstance T where
  ax_PSR_substance_distinguishability := by
    intro x y hs1 hs2 hne
    cases x <;> cases y
    -- s₁ × s₁: contradiction with hne
    case s₁.s₁ => exact (hne rfl).elim
    -- s₁ × s₂: take a_only_s1, left disjunct
    case s₁.s₂ =>
      refine ⟨T.a_only_s1, Or.inl ⟨?_, ?_⟩⟩
      · exact ⟨⟨trivial, trivial⟩, trivial⟩
      · intro ⟨_, h⟩; exact h.elim
    -- s₁ × non-substance: hs2 fails
    case s₁.a_shared => exact hs2.1.elim
    case s₁.a_only_s1 => exact hs2.1.elim
    -- s₂ × s₁: take a_only_s1, right disjunct
    case s₂.s₁ =>
      refine ⟨T.a_only_s1, Or.inr ⟨?_, ?_⟩⟩
      · exact ⟨⟨trivial, trivial⟩, trivial⟩
      · intro ⟨_, h⟩; exact h.elim
    case s₂.s₂ => exact (hne rfl).elim
    case s₂.a_shared => exact hs2.1.elim
    case s₂.a_only_s1 => exact hs2.1.elim
    -- non-substance × _: hs1 fails
    case a_shared.s₁ => exact hs1.1.elim
    case a_shared.s₂ => exact hs1.1.elim
    case a_shared.a_shared => exact hs1.1.elim
    case a_shared.a_only_s1 => exact hs1.1.elim
    case a_only_s1.s₁ => exact hs1.1.elim
    case a_only_s1.s₂ => exact hs1.1.elim
    case a_only_s1.a_shared => exact hs1.1.elim
    case a_only_s1.a_only_s1 => exact hs1.1.elim

/-- **A12 is falsified in this model**: `T.s₁` and `T.s₂` are
    distinct substances sharing the attribute `a_shared`. -/
theorem A12_falsified :
    ∃ x y a : T, Substance x ∧ Substance y ∧
        Attribute a x ∧ Attribute a y ∧ x ≠ y :=
  ⟨T.s₁, T.s₂, T.a_shared,
   ⟨trivial, trivial⟩,
   ⟨trivial, trivial⟩,
   ⟨⟨trivial, trivial⟩, trivial⟩,
   ⟨⟨trivial, trivial⟩, trivial⟩,
   by intro h; cases h⟩

/-- **The mechanical irreducibility result for A12**: if A12 were
    derivable from `[PSRSubstance T] + [EthicaWorld T]` alone, it
    would yield `s₁ = s₂` on this model, contradicting the
    `s₁ ≠ s₂` clause of `A12_falsified`. Hence A12 is *not*
    derivable from PSR-substance-distinguishability + base
    axioms. This is the **first kernel-level Bennett-line
    irreducibility result** (replacing the prior marker theorem
    in `ModalForm.lean` §δ).

    The argument is meta-logical (about provability), not a Lean
    theorem; this `def` records the witness data for the argument,
    namely the falsification given by `A12_falsified`. -/
def A12_irreducibility_witness : Prop :=
  ∃ _ : EthicaWorld T, ∃ _ : Modal.PSRSubstance T,
    ∃ x y a : T, Substance x ∧ Substance y ∧
      Attribute a x ∧ Attribute a y ∧ x ≠ y

example : A12_irreducibility_witness :=
  ⟨ethicaWorld, psrSubstance, T.s₁, T.s₂, T.a_shared,
   ⟨trivial, trivial⟩,
   ⟨trivial, trivial⟩,
   ⟨⟨trivial, trivial⟩, trivial⟩,
   ⟨⟨trivial, trivial⟩, trivial⟩,
   by intro h; cases h⟩

end A12CounterModel

/-! ## Counter-model 2 — A15 not demotable from plenitude alone

  Three-element universe with two `IsGod`-satisfying substances
  `g₁, g₂`, each with its own (different) attribute, plus a third
  thing `attr_g₂` perceived as g₂'s essence. Plenitude holds
  (every realised attribute is in some god — its owner). A15
  fails (g₁ does not have g₂'s attribute).

  Since A26 (god uniqueness) **fails** in this model (g₁ ≠ g₂ are
  both gods), we cannot instantiate the full `PSRPlenitude` class.
  This is the point: PSRPlenitude requires both plenitude *and*
  uniqueness, and the model demonstrates that plenitude alone is
  insufficient for A15 because uniqueness can independently fail.
-/

namespace A15CounterModel

/-- Three-element universe. `g₁` and `g₂` are two gods with
    distinct attribute graphs; `attr_g₂` is an attribute g₂ has
    that g₁ does not. -/
inductive T where
  | g₁ : T
  | g₂ : T
  | attr_g₂ : T
  deriving DecidableEq

/-- Both `g₁` and `g₂` are substances. `attr_g₂` is not. -/
def isSubstance : T → Prop
  | T.g₁ => True
  | T.g₂ => True
  | _ => False

/-- The intellect-perception graph. `g₁` only has itself as an
    attribute. `g₂` has itself and `attr_g₂`. -/
def perceivesAsEssence : T → T → Prop
  | T.g₁, T.g₁ => True
  | T.g₂, T.g₂ => True
  | T.g₂, T.attr_g₂ => True
  | _, _ => False

instance ethicaWorld : EthicaWorld T where
  inItself x := isSubstance x
  perSeConceived x := isSubstance x
  involvesExistence x := isSubstance x
  natureRequiresExistence x := isSubstance x
  inAnother x := ¬ isSubstance x
  conceivedThroughAnother x := ¬ isSubstance x
  limitedBy _ _ := False
  intellectPerceivesAsEssence := perceivesAsEssence
  absolutelyInfinite x := isSubstance x
  expressesEternalEssence _ := True
  freelyExistent x := isSubstance x
  constrained x := ¬ isSubstance x
  eternal x := isSubstance x

/-- Both `g₁` and `g₂` satisfy `IsGod` in this model. -/
theorem g₁_IsGod : IsGod T.g₁ :=
  ⟨ ⟨trivial, trivial⟩
  , trivial
  , ⟨T.g₁, ⟨⟨trivial, trivial⟩, trivial⟩⟩
  , fun _ _ => trivial ⟩

theorem g₂_IsGod : IsGod T.g₂ :=
  ⟨ ⟨trivial, trivial⟩
  , trivial
  , ⟨T.g₂, ⟨⟨trivial, trivial⟩, trivial⟩⟩
  , fun _ _ => trivial ⟩

/-- **Plenitude holds in this model**: every realised substance
    attribute is also realised in some god. The witness is just
    the substance itself (each god is its own attribute-bearer). -/
theorem plenitude_holds :
    ∀ a s : T, Substance s → Attribute a s →
      ∃ g, IsGod g ∧ Attribute a g := by
  intro a s hs ha
  -- s is a substance: s ∈ {g₁, g₂}.
  cases s
  case g₁ =>
    -- a is an attribute of g₁: ha.2 says perceivesAsEssence g₁ a.
    -- The graph: only g₁ is perceived, so a = g₁.
    cases a
    case g₁ => exact ⟨T.g₁, g₁_IsGod, ha⟩
    case g₂ => exact ha.2.elim
    case attr_g₂ => exact ha.2.elim
  case g₂ =>
    -- a is an attribute of g₂: a ∈ {g₂, attr_g₂}.
    cases a
    case g₁ => exact ha.2.elim
    case g₂ => exact ⟨T.g₂, g₂_IsGod, ha⟩
    case attr_g₂ => exact ⟨T.g₂, g₂_IsGod, ha⟩
  case attr_g₂ => exact hs.1.elim

/-- **A15 is falsified in this model**: g₁ is a god, g₂ is a
    substance with attribute `attr_g₂`, but g₁ does not have
    `attr_g₂` as an attribute. -/
theorem A15_falsified :
    ∃ g s a : T, IsGod g ∧ Substance s ∧ Attribute a s ∧
        ¬ Attribute a g :=
  ⟨T.g₁, T.g₂, T.attr_g₂,
   g₁_IsGod,
   ⟨trivial, trivial⟩,
   ⟨⟨trivial, trivial⟩, trivial⟩,
   by intro ⟨_, h⟩; exact h.elim⟩

/-- **The mechanical irreducibility result for A15**: this model
    satisfies plenitude (A25) and the base `EthicaWorld` axioms
    while falsifying A15. Hence A15 is *not* derivable from
    plenitude + base axioms; the demote requires the additional
    god-uniqueness commitment (A26). This is the **second
    kernel-level Bennett-line irreducibility result**. -/
def A15_irreducibility_witness : Prop :=
  ∃ _ : EthicaWorld T,
    (∀ a s : T, Substance s → Attribute a s →
      ∃ g, IsGod g ∧ Attribute a g) ∧
    ∃ g s a : T, IsGod g ∧ Substance s ∧ Attribute a s ∧
      ¬ Attribute a g

example : A15_irreducibility_witness :=
  ⟨ethicaWorld, plenitude_holds,
   T.g₁, T.g₂, T.attr_g₂,
   g₁_IsGod,
   ⟨trivial, trivial⟩,
   ⟨⟨trivial, trivial⟩, trivial⟩,
   by intro ⟨_, h⟩; exact h.elim⟩

end A15CounterModel

end Ethica.Pars1.Models.Counterexamples
