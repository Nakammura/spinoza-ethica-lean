/-
  Spinoza, *Ethica* Pars I — the multi-attribute substance bench.

  `docs/coverage.md` has listed a "multi-attribute substance" row as
  planned-future (⏳) since v1.0.0: GAP-8a's counting framework
  (`Ethica/Pars1/Realitas.lean`) needed a witness showing a substance
  with genuinely many — indeed infinitely many — attributes is
  consistent with the full `Pars1Axioms` register. This file delivers
  that witness.

  ## The model

  Carrier: `Nat`. This is deliberately an *infinite* carrier — a
  finite type could witness `hasAtLeastNAttributes _ n` for some
  fixed `n`, but not `HasInfiniteAttributes` for every `n`
  simultaneously.

  The attribute tree splits the carrier in two disjoint zones:
    - `0`'s attributes are ALL odd numbers;
    - every `k ≠ 0`'s sole attribute is `2 * k`.

  These zones are pairwise disjoint by construction — parity
  separates `0`'s (odd) attributes from everyone else's (even)
  attribute, and doubling (`k ↦ 2 * k`) is injective on `k ≠ 0` — and
  disjointness is exactly what A12 (indiscernibility of substance by
  shared attribute) demands: two substances sharing an attribute must
  be forced equal, and since only `0` ever shares an attribute with
  itself (there are infinitely many of them, all consistent with
  `s = 0`), A12 never has to identify `0` with any `k ≠ 0`.

  ## Why this model has no God

  `absolutelyInfinite _ := False` for every element — the
  load-bearing choice that makes `IsGod` unsatisfiable everywhere in
  this model (mirrors `Models/NoGod.lean`'s idiom). This is not
  incidental: `Ethica/Pars1/Realitas.lean`'s `attribute_collapse`
  theorem shows that *any* `Pars1Axioms` world containing a God
  forces every attribute to equal that God, capping every substance
  at exactly one attribute. A world with a substance that genuinely
  has two or more attributes (let alone infinitely many) therefore
  cannot contain a God — `multiAttribute_hasNoGod` below is not a
  modelling accident but the model witnessing exactly the escape
  route the collapse theorem leaves open.
-/
import Ethica.Pars1.Definitions
import Ethica.Pars1.Axioms
import Ethica.Pars1.Realitas

namespace Ethica.Pars1.Models.MultiAttribute

open Ethica.Pars1
open EthicaWorld

/-- Interpretation on `Nat`. Every fields other than
    `intellectPerceivesAsEssence` is set at its most generous
    constant, mirroring `Models/NoGod.lean`'s idiom: every natural
    number is `inItself`/`perSeConceived` (hence a `Substance`,
    trivially), involves and requires existence, is never `inAnother`
    / `conceivedThroughAnother` (hence never a `Mode`), and is
    eternal. The one load-bearing non-trivial field is
    `absolutelyInfinite _ := False`, which makes `IsGod`
    unsatisfiable here — see the file header. -/
instance ethicaWorld : EthicaWorld Nat where
  inItself                    _   := True
  perSeConceived               _   := True
  involvesExistence            _   := True
  natureRequiresExistence      _   := True
  inAnother                    _   := False
  conceivedThroughAnother      _   := False
  limitedBy                    _ _ := False
  -- The attribute tree: `0`'s attributes are all odd numbers; every
  -- `k ≠ 0`'s sole attribute is `2 * k`. Disjoint by parity /
  -- injectivity of doubling — exactly what A12 needs.
  intellectPerceivesAsEssence s a := (s = 0 ∧ a % 2 = 1) ∨ (s ≠ 0 ∧ a = 2 * s)
  absolutelyInfinite            _   := False
  expressesEternalEssence      _   := True
  freelyExistent                _   := True
  constrained                  _   := False
  eternal                       _   := True

/-- The full `Pars1Axioms` register (A1–A15, including all four
    Section III commitments) holds on `Nat` under `ethicaWorld`. -/
instance pars1Axioms : Pars1Axioms Nat where
  ax1_inItselfOrInAnother _ := Or.inl trivial
  ax1_exclusive _ h := h.2
  ax2_perSeOrThroughAnother _ := Or.inl trivial
  ax3_causationDeterminate := trivial
  ax4_effectKnowledgeFromCause := trivial
  ax5_nothingInCommonNoUnderstanding := trivial
  ax6_trueIdeaAgreesWithIdeatum := trivial
  ax7_conceivableAsNonExistent _ h := fun _ => h trivial
  ax_inItself_iff_perSeConceived _ := Iff.rfl
  ax_inAnother_iff_conceivedThroughAnother _ := Iff.rfl
  ax_attribute_perSe _ _ _ := trivial
  ax_causaSui_iff _ := Iff.rfl
  -- A12: case-split both `Attribute` hypotheses on the two disjuncts
  -- of `intellectPerceivesAsEssence`. The parity clash (odd vs.
  -- `2 * s`) and the injectivity of doubling (`2 * s₁ = 2 * s₂`) both
  -- close with `omega`.
  ax_substanceIdByAttribute := by
    intro s1 s2 a h1 h2
    obtain ⟨-, h1'⟩ := h1
    obtain ⟨-, h2'⟩ := h2
    rcases h1' with ⟨hs1, ha1⟩ | ⟨-, ha1⟩ <;>
      rcases h2' with ⟨hs2, ha2⟩ | ⟨-, ha2⟩ <;>
      omega
  -- A14: `0` gets attribute `1` (odd); every `s ≠ 0` gets attribute
  -- `2 * s`.
  ax_substance_has_attribute := by
    intro s _
    by_cases hs : s = 0
    · subst hs
      exact ⟨1, ⟨trivial, trivial⟩, Or.inl ⟨rfl, by decide⟩⟩
    · exact ⟨2 * s, ⟨trivial, trivial⟩, Or.inr ⟨hs, rfl⟩⟩
  -- A15: vacuous — `IsGod g` unfolds to a conjunction whose
  -- `absolutelyInfinite g` conjunct is `False`.
  ax_IsGod_has_attribute_of := by
    intro g _ _ hgod _ _
    exact hgod.2.1.elim
  ax_substance_involves_existence _ _ := trivial

/-- **This model has no God**: `IsGod` requires `absolutelyInfinite`,
    which is `False` for every natural number. -/
theorem multiAttribute_hasNoGod : ∀ g : Nat, ¬ IsGod g := fun _ hgod => hgod.2.1

/-- `f i := 2 * i.val + 1` witnesses two distinct odd attributes of
    `0` (namely `1` and `3`): oddness discharges by `omega`;
    injectivity reduces to `2 * i.val + 1 = 2 * j.val + 1 → i.val =
    j.val`, closed by `omega`, then lifted to `Fin` equality via
    `Fin.eq_of_val_eq`. -/
theorem multiAttribute_plurality : hasAtLeastNAttributes (0 : Nat) 2 := by
  refine ⟨fun i => 2 * i.val + 1, ?_, ?_⟩
  · intro i
    refine ⟨⟨trivial, trivial⟩, Or.inl ⟨rfl, ?_⟩⟩
    show (2 * i.val + 1) % 2 = 1
    omega
  · intro i j h
    apply Fin.eq_of_val_eq
    have h' : 2 * i.val + 1 = 2 * j.val + 1 := h
    omega

/-- `0` has infinitely many attributes: the same witness
    `f i := 2 * i.val + 1`, generalised to any `n`, gives an
    injection `Fin n → Nat` landing entirely in `0`'s (odd)
    attribute set — GAP-8a's cardinality desideratum, satisfied here
    by the infinite carrier `Nat`. -/
theorem multiAttribute_infinitude : HasInfiniteAttributes (0 : Nat) := by
  intro n
  refine ⟨fun i => 2 * i.val + 1, ?_, ?_⟩
  · intro i
    refine ⟨⟨trivial, trivial⟩, Or.inl ⟨rfl, ?_⟩⟩
    show (2 * i.val + 1) % 2 = 1
    omega
  · intro i j h
    apply Fin.eq_of_val_eq
    have h' : 2 * i.val + 1 = 2 * j.val + 1 := h
    omega

/-! ## Reading this bench together with `attribute_collapse`

  `Ethica/Pars1/Realitas.lean`'s `attribute_collapse` theorem shows
  that any `Pars1Axioms` world containing a God forces every
  attribute of every substance to equal that God — capping every
  substance at exactly one attribute. This model proves the
  incompatibility that theorem discovers is *sharp*, not an artifact
  of an impoverished counting framework: the FULL `Pars1Axioms`
  register tolerates a substance with infinitely many attributes
  (`multiAttribute_infinitude`, satisfying GAP-8a's desideratum via
  carrier `Nat`) precisely as long as no God exists in the model
  (`multiAttribute_hasNoGod`). Adding a God-existence commitment
  (A27, `TheologiaAxioms.ax_god_exists`) anywhere near this model is
  impossible without breaking attribute plurality; in any *godful*
  register, `attribute_collapse` caps every substance at one
  attribute regardless of how the rest of the model is built.
  Spinoza's Def. VI wants both a God AND attribute plurality
  ("*substantiam constantem infinitis attributis*"); the register
  formalised here grants exactly one of the two. -/

end Ethica.Pars1.Models.MultiAttribute
