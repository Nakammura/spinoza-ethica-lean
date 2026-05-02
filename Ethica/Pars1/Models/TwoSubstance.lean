/-
  Spinoza, *Ethica* Pars I — Bennett-line counter-model.

  This file constructs a two-element universe with disjoint
  attribute graphs and demonstrates that **A15** (universality of
  God's attributes; `Pars1Axioms.ax_IsGod_has_attribute_of`) is
  *falsified* here. After A14 / A15 were promoted to `Pars1Axioms`
  fields (post-review of 2026-05-02 §A.α), this model can no longer
  instantiate `Pars1Axioms` — that is the philosophical point: it
  is a Bennett-style multi-substance world, not a Spinoza one.

  ## What this model is for

  Documenting *what is committed* by promoting A15 to `Pars1Axioms`.
  A reader who wants to see the bite of the universality axiom can
  read `twosubst_falsifies_A15` and trace the failure: both `s₁`
  and `s₂` satisfy `IsGod`, the attribute graph is the diagonal,
  so `s₂` has attribute `s₂` while `s₁` does not — universality
  fails.

  ## What this model is NOT

  - Not a `Pars1Axioms`-instance carrier. The `Pars1Axioms TwoSubst`
    instance was removed when A14 / A15 were promoted; this model
    cannot satisfy A15. Per closure-protocol step 6(d), the model
    is migrated to "Bennett-line non-Spinoza bench" status.
  - Not a `CausalAxioms`-instance carrier (since `CausalAxioms`
    extends `Pars1Axioms`).
  - Not a witness for Props. III / V / VI (those need `Pars1Axioms`
    or `CausalAxioms` instances). For witness-model checks of those
    propositions, see `Models/SingleSubstance.lean`.

  This is what closure-protocol step 6(d) calls *migration*: when a
  Section III axiom is promoted, models that falsify the axiom lose
  their typeclass instance and are reclassified.
-/
import Ethica.Pars1.Definitions
import Ethica.Pars1.Axioms
import Ethica.Pars1.Causation
import Ethica.Pars1.Propositions

namespace Ethica.Pars1.Models.TwoSubstance

open Ethica.Pars1
open EthicaWorld

/-- A two-element universe of "things". Each element represents a
    substance with its own self-attribute. -/
inductive TwoSubst where
  | s₁ : TwoSubst
  | s₂ : TwoSubst
  deriving DecidableEq

/-- Each element is its own (and only) attribute-essence-perception
    target. The two attribute-graphs are disjoint. -/
def perceivesAsEssenceGraph : TwoSubst → TwoSubst → Prop
  | TwoSubst.s₁, TwoSubst.s₁ => True
  | TwoSubst.s₂, TwoSubst.s₂ => True
  | _,           _           => False

/-- The bare `EthicaWorld` instance — Spinoza's ontological
    primitives, *without* the substantive metaphysical commitments
    of `Pars1Axioms`. -/
instance ethicaWorld : EthicaWorld TwoSubst where
  inItself                      _   := True
  perSeConceived                _   := True
  involvesExistence             _   := True
  natureRequiresExistence       _   := True
  inAnother                     _   := False
  conceivedThroughAnother       _   := False
  limitedBy                     _ _ := False
  intellectPerceivesAsEssence   x a := perceivesAsEssenceGraph x a
  absolutelyInfinite            _   := True
  expressesEternalEssence       _   := True
  freelyExistent                _   := True
  constrained                   _   := False
  eternal                       _   := True

/-! ## Sanity checks (no `Pars1Axioms` needed) -/

/-- Both elements are substances. -/
example : Substance TwoSubst.s₁ := ⟨trivial, trivial⟩
example : Substance TwoSubst.s₂ := ⟨trivial, trivial⟩

/-- The two substances are distinct (no spurious quotient). -/
example : TwoSubst.s₁ ≠ TwoSubst.s₂ := by intro h; cases h

/-- `s₁` is an attribute of itself. -/
example : Attribute TwoSubst.s₁ TwoSubst.s₁ :=
  ⟨⟨trivial, trivial⟩, trivial⟩

/-- `s₁` is **not** an attribute of `s₂`: the disjoint attribute
    graph rejects the off-diagonal case. -/
example : ¬ Attribute TwoSubst.s₁ TwoSubst.s₂ := by
  intro ⟨_, h⟩
  exact h.elim

/-- Both elements satisfy `IsGod` (this is what makes the model
    non-Spinoza: Spinoza's monism requires uniqueness of God,
    delivered by A12 + A15 in the intended reading). -/
example : IsGod TwoSubst.s₁ :=
  ⟨ ⟨trivial, trivial⟩
  , trivial
  , ⟨TwoSubst.s₁, ⟨⟨trivial, trivial⟩, trivial⟩⟩
  , fun _ _ => trivial ⟩

example : IsGod TwoSubst.s₂ :=
  ⟨ ⟨trivial, trivial⟩
  , trivial
  , ⟨TwoSubst.s₂, ⟨⟨trivial, trivial⟩, trivial⟩⟩
  , fun _ _ => trivial ⟩

/-! ## The headline counter-witness: A15 is falsified -/

/-- **Counter-witness**: `Pars1Axioms.ax_IsGod_has_attribute_of`
    (A15, GAP-8b) is **falsified** in this model. Concretely: `s₁`
    is a god, `s₂` is a substance with attribute `s₂`, but `s₁`
    does not have `s₂` as an attribute (the attribute graph is the
    diagonal, so `s₁` only has `s₁`).

    This is the Bennett-style point against Spinoza's universality
    clause — multi-substance worlds with disjoint attribute graphs
    satisfy the bare ontology (`EthicaWorld`) but falsify A15.
    Hence this model **cannot** carry a `Pars1Axioms` instance,
    which is precisely the migration outcome anticipated in
    closure-protocol step 6(d). -/
theorem twosubst_falsifies_A15 :
    ¬ (∀ g s a : TwoSubst, IsGod g → Substance s → Attribute a s →
        Attribute a g) := by
  intro h
  have isgod_s1 : IsGod TwoSubst.s₁ :=
    ⟨ ⟨trivial, trivial⟩
    , trivial
    , ⟨TwoSubst.s₁, ⟨⟨trivial, trivial⟩, trivial⟩⟩
    , fun _ _ => trivial ⟩
  have sub_s2 : Substance TwoSubst.s₂ := ⟨trivial, trivial⟩
  have attr_s2_s2 : Attribute TwoSubst.s₂ TwoSubst.s₂ :=
    ⟨⟨trivial, trivial⟩, trivial⟩
  have attr_s2_s1 : Attribute TwoSubst.s₂ TwoSubst.s₁ :=
    h TwoSubst.s₁ TwoSubst.s₂ TwoSubst.s₂ isgod_s1 sub_s2 attr_s2_s2
  exact attr_s2_s1.2.elim

/-
  Migration note (closure-protocol step 6(d)): when A15 was promoted
  to `Pars1Axioms.ax_IsGod_has_attribute_of`, this model lost its
  ability to carry a `Pars1Axioms` instance. `CausalWorld` /
  `CausalAxioms` instances were correspondingly removed (since
  `CausalAxioms extends Pars1Axioms`). The pre-migration
  identity-restricted causation graph is preserved as a comment in
  git history (commit 8d39962).

  This is the correct behaviour: the kernel inconsistency that the
  pre-soundness-fix `private axiom` encoding produced (review of
  2026-05-02 §A) is no longer re-introducible. Any attempt to
  `prop_14`-call into this model will fail at typeclass resolution,
  not at proof typecheck — the failure is now visible in the type
  system, not silently latent in the kernel base.
-/

end Ethica.Pars1.Models.TwoSubstance
