/-
  Spinoza, *Ethica* Pars II — consistency witness for the idea layer,
  the *quatenus* layer and the *esse objectivum* layer (batches 1.1,
  1.2 and 1.3).

  Carries a full `ParallelismusAxioms` instance on one carrier:
  `Pars1Axioms` (A1–A15) + `CausalAxioms` (A4ₛ, A5ₛ) +
  `InherenceAxioms` (A33–A36) + `ConsecutioAxioms` (A37–A43) +
  `AttrAxioms` (A10′/A12′/A14′/A15′) + `Pars2Axioms` (A45–A50) +
  `QuatenusAxioms` (A51–A55) + `ParallelismusAxioms` (A56–A59). So no
  layer introduces a contradiction, and Props. II.I–II.IX are not
  vacuously true by explosion.

  **The carrier, and why it has three constructors.**

      inductive MensThing | deus | idea : MensThing → MensThing
                          | res  : Int → MensThing

  - `deus` — the unique substance.
  - `idea x` — *the* idea of `x`, including `idea (idea x)`. Batch 1.2
    established that this ladder is forced: A45 (an idea has a unique
    ideatum) with A49 (everything has an idea) and A54 (ideas are
    modes of thought, hence never the substance) are **jointly
    unsatisfiable on any finite carrier**.
  - `res n` — the stock of singular things, indexed by `Int`.

  The third constructor is what batch 1.3 needed, and the index type
  is not decoration. Prop. II.IX says the idea of a singular thing is
  caused by another idea, *et sic in infinitum*, while A43 says
  everything has an effect. Together they demand a causal order on
  the singular things with **neither a first nor a last element** —
  so `Nat` will not do and `Int` will. The witness is thus a small
  proof that Prop. IX's *in infinitum* is a two-sided requirement.

  Splitting `res` off from `idea` also buys two things the batch-1.2
  carrier could not have:

  - `idea deus`, God's infinite idea, is **not** a *res singularis*
    (`mensIndex` is `none` on the whole `idea…deus` family), which is
    what Prop. VIII needs it to be;
  - the modes of `extensio` are non-empty, so Prop. VI's exclusion
    clause is non-vacuous **in both directions** — see
    `mens_prop_6_extensio`, which batch 1.2's witness could not
    state.

  **`durat` genuinely splits the carrier**: `res n` endures exactly
  when `0 ≤ n`. So Prop. VIII's hypothesis (a singular thing that does
  *not* endure) is met by `res (-1)` and refuted by `res 0` — the
  proposition is tested here, not waved through.

  **The causal order is not constant.** `mensCause` says: nothing
  causes God; God causes everything else; among the singular things,
  `res m` causes `res n` exactly when `n < m`; and the idea of `c`
  causes the idea of `e` exactly when `c` causes `e`. Hence

  - `mens_cause_irreflexive_deus` — `Cause` is *not* uniformly `True`,
    so Prop. VII's biconditional (`prop_2_7_ordoEtConnexio_iff`) is
    not trivially satisfied;
  - A50 and A55 discharge on the recursive clause, not on a constant;
  - A43 needs `mens_succ_cause`'s induction and A59 needs
    `mens_pred_cause`'s.

  **A note on the direction of `res`.** Reading `res m` as causing
  `res n` when `n < m` makes the index a *countdown*: every singular
  thing has both a cause (`res (n+1)`) and an effect (`res (n-1)`).
  Nothing in the register orients the index the other way, because
  nothing in the register connects the causal order to the
  ideation order beyond the parallelism itself — which is exactly the
  observation GAP-28 records.

  **And it still holds both attribute verdicts at once**:

  - `mens_pars1_collapse_holds` — no God here has two `Thing`-typed
    attributes (`Ethica.Pars1.god_no_two_attributes` applies, because
    `Pars1Axioms` genuinely holds);
  - `mens_duo_attributa` — God *does* have two `Attr`-typed
    attributes.

  There is no tension: the `Thing`-typed attribution channel is
  degenerate exactly as the collapse theorem forces, while the
  load-bearing attribute structure lives in `MensAttr`.
-/
import Ethica.Pars1.Definitions
import Ethica.Pars1.Axioms
import Ethica.Pars1.Causation
import Ethica.Pars1.Propositions
import Ethica.Pars1.Realitas
import Ethica.Pars1.Inherence
import Ethica.Pars1.Consecutio
import Ethica.Attributum.Core
import Ethica.Attributum.Axioms
import Ethica.Pars2.Idea
import Ethica.Pars2.Quatenus
import Ethica.Pars2.Parallelismus

namespace Ethica.Pars2.Models.MensWitness

open Ethica.Pars1
open Ethica.Attributum
open Ethica.Pars2

/-- The thing universe: God, the infinite ladder of ideas above him,
    and an `Int`-indexed stock of singular things.

    `idea x` is *the* idea of `x` — including `idea (idea x)`, which
    Spinoza insists on (Prop. II.XXI sch.) and which A45 + A49 + A54
    jointly force any model to contain. `res n` supplies the finite
    modes: Prop. IX's regress and A43's "everything has an effect"
    together require an index with no first and no last element. -/
inductive MensThing where
  | deus
  | idea : MensThing → MensThing
  | res  : Int → MensThing
  deriving DecidableEq

/-- The attribute universe: the two attributes Spinoza names. Unlike
    the `Thing`-typed attribute channel this type has **two**
    elements, which is the whole point of the Attributum layer. -/
inductive MensAttr where
  | cogitatio
  | extensio
  deriving DecidableEq

/-! ## The carrier's shape -/

/-- No idea is God. Constructor disjointness; used throughout to show
    that ideas are modes. -/
theorem mens_idea_ne_deus (x : MensThing) : MensThing.idea x ≠ MensThing.deus :=
  fun h => MensThing.noConfusion h

/-- No singular thing is God. -/
theorem mens_res_ne_deus (n : Int) : MensThing.res n ≠ MensThing.deus :=
  fun h => MensThing.noConfusion h

/-- Every thing either is God or is not — by cases on the carrier, so
    A1 and A2 discharge without `Classical.em`. -/
theorem mens_deus_or_not (x : MensThing) :
    x = MensThing.deus ∨ x ≠ MensThing.deus := by
  cases x with
  | deus  => exact Or.inl rfl
  | idea y => exact Or.inr (mens_idea_ne_deus y)
  | res n  => exact Or.inr (mens_res_ne_deus n)

/-- Which attribute a thing is a mode of. God is a mode of none; the
    ideas are modes of thought; the singular things are modes of
    extension.

    This single function drives `modeUnder`, `involvesConceptOf` and
    `essentiaFormalisIn`, so all three are automatically *functional*
    — each thing involves the concept of exactly one attribute, which
    is what A51's exclusion clause needs. -/
def mensAttrOf : MensThing → Option MensAttr
  | .deus   => none
  | .idea _ => some .cogitatio
  | .res _  => some .extensio

/-- The singular index of a thing, if it has one: `res n` and every
    idea above it carry `n`; God and the ideas of God carry nothing.

    `mensIndex x ≠ none` is exactly "`x` is a *res singularis*" in
    this model — see `mens_singularis_iff_index`. It is what keeps
    `idea deus` (God's infinite idea) out of the singular class. -/
def mensIndex : MensThing → Option Int
  | .deus   => none
  | .idea x => mensIndex x
  | .res n  => some n

/-- Actual existence. God endures; an idea endures exactly when its
    object does (this is A57 built into the model); a singular thing
    endures exactly when its index is non-negative.

    The last clause is the point: `durat` **splits** the singular
    things, so Prop. VIII is tested on both sides. -/
def mensDurat : MensThing → Prop
  | .deus   => True
  | .idea x => mensDurat x
  | .res n  => 0 ≤ n

/-- The causal order. Nothing causes God; God causes everything else;
    `res m` causes `res n` exactly when `n < m`; and the idea of `c`
    causes the idea of `e` exactly when `c` causes `e`.

    The last clause is Prop. II.VII built into the model by
    construction — which is what makes A50/A55 discharge on structure
    rather than on a constant. -/
def mensCause : MensThing → MensThing → Prop
  | .idea c, .idea e => mensCause c e
  | .deus,   .deus   => False
  | .deus,   .idea _ => True
  | .deus,   .res _  => True
  | .idea _, .deus   => False
  | .idea _, .res _  => False
  | .res _,  .deus   => False
  | .res _,  .idea _ => False
  | .res m,  .res n  => n < m

/-- The recursive clause, as an `Iff` — the parallelism of the model,
    stated. -/
theorem mensCause_idea (c e : MensThing) :
    mensCause (MensThing.idea c) (MensThing.idea e) ↔ mensCause c e :=
  Iff.rfl

/-- **`Cause` is not uniformly `True` here.** Nothing causes God — in
    particular God does not cause himself under this relation (the
    *causa sui* of Def. I is carried by `involvesExistence`, not by
    `Cause`). This is what keeps Prop. VII's biconditional from being
    trivially satisfied. -/
theorem mens_cause_irreflexive_deus :
    ¬ mensCause MensThing.deus MensThing.deus :=
  fun h => h

/-- A thing that is not God is a mode of *some* attribute. -/
theorem mens_attrOf_isSome (x : MensThing) (h : x ≠ MensThing.deus) :
    ∃ a : MensAttr, mensAttrOf x = some a := by
  cases x with
  | deus   => exact absurd rfl h
  | idea _ => exact ⟨MensAttr.cogitatio, rfl⟩
  | res _  => exact ⟨MensAttr.extensio, rfl⟩

/-! ### The two step functions

  `mensSucc` walks one step *down* the singular index (an effect),
  `mensPred` one step *up* (a cause). Both commute with `idea`, which
  is how the parallelism is maintained at every rung of the ladder. -/

/-- One effect of `x`. God's is `res 0`; the effect of `res n` is
    `res (n-1)`; the effect of an idea is the idea of the effect. -/
def mensSucc : MensThing → MensThing
  | .deus   => .res 0
  | .idea x => .idea (mensSucc x)
  | .res n  => .res (n - 1)

/-- One cause of `x`, when `x` is singular. The cause of `res n` is
    `res (n+1)`; the cause of an idea is the idea of the cause. -/
def mensPred : MensThing → MensThing
  | .deus   => .deus
  | .idea x => .idea (mensPred x)
  | .res n  => .res (n + 1)

/-- Everything has an effect — by induction on the carrier. This is
    what discharges A43 (`ax_omnia_effectum`) **non-vacuously**; a
    one-element carrier gets A43 for free by reflexivity, this one
    does not. -/
theorem mens_succ_cause (x : MensThing) : mensCause x (mensSucc x) := by
  induction x with
  | deus       => trivial
  | idea _ ih  => exact ih
  | res n      => show (n : Int) - 1 < n; omega

/-- A43, packaged. -/
theorem mens_hasEffect (x : MensThing) : ∃ e, mensCause x e :=
  ⟨mensSucc x, mens_succ_cause x⟩

/-- `mensPred` preserves the attribute — so a thing and its cause are
    modes of the same attribute, which is what `sameNatureUnder`
    needs. -/
theorem mens_pred_attrOf (x : MensThing) :
    mensAttrOf (mensPred x) = mensAttrOf x := by
  cases x <;> rfl

/-- `mensPred` stays inside the singular class. -/
theorem mens_pred_index (x : MensThing) (h : mensIndex x ≠ none) :
    mensIndex (mensPred x) ≠ none := by
  induction x with
  | deus      => exact absurd rfl h
  | idea _ ih => exact ih h
  | res _     => exact fun hc => Option.noConfusion hc

/-- A singular thing is distinct from its cause — Spinoza's "*ab
    **alia** ejusdem naturæ*". -/
theorem mens_pred_ne (x : MensThing) (h : mensIndex x ≠ none) :
    x ≠ mensPred x := by
  induction x with
  | deus      => exact absurd rfl h
  | idea y ih => exact fun hc => ih h (MensThing.idea.inj hc)
  | res n     => exact fun hc => by have := MensThing.res.inj hc; omega

/-- Every singular thing really is caused by `mensPred` of it. This
    is the induction A59 (the repaired Prop. I.XXVIII) needs — and
    the reason the index type has to be `Int`: on `Nat` the chain
    would bottom out at `res 0`. -/
theorem mens_pred_cause (x : MensThing) (h : mensIndex x ≠ none) :
    mensCause (mensPred x) x := by
  induction x with
  | deus      => exact absurd rfl h
  | idea y ih => exact ih h
  | res n     => show (n : Int) < n + 1; omega

/-! ## The world -/

/-- The full world instance: Pars I's thirteen primitives, the
    Attributum layer's attribute channel, the causal / inherence /
    consecution relations, Pars II's `ideaOf` with its two named
    attributes, the three *quatenus* primitives and the three
    *esse objectivum* ones.

    Profile in one line: **`deus` is the unique substance, and
    everything else is a mode** — the ideas modes of `cogitatio`, the
    `res n` modes of `extensio`. `limitedBy` holds between distinct
    singular things, the `Thing`-typed attribute channel picks out
    `deus` alone, and the `Attr`-typed one gives `deus` both of its
    attributes.

    The *quatenus* primitives are genuinely selective and now
    selective in **both** directions: `modeUnder`, `causeUnder` and
    `involvesConceptOf` all route through `mensAttrOf`, which is
    single-valued, so each mode refuses every attribute but its own.
    Batch 1.2's witness could only exhibit the refusal of `extensio`;
    this one exhibits the refusal of `cogitatio` as well. -/
instance parallelismusWorld : ParallelismusWorld MensThing MensAttr where
  -- EthicaWorld (Pars I, `Definitions.lean`)
  inItself                    x     := x = MensThing.deus
  perSeConceived              x     := x = MensThing.deus
  involvesExistence           x     := x = MensThing.deus
  natureRequiresExistence     x     := x = MensThing.deus
  inAnother                   x     := x ≠ MensThing.deus
  conceivedThroughAnother     x     := x ≠ MensThing.deus
  limitedBy                   x y   :=
    mensIndex x ≠ none ∧ mensIndex y ≠ none ∧ x ≠ y
  intellectPerceivesAsEssence _ a   := a = MensThing.deus
  absolutelyInfinite          x     := x = MensThing.deus
  expressesEternalEssence     x     := x = MensThing.deus
  freelyExistent              x     := x = MensThing.deus
  constrained                 x     := x ≠ MensThing.deus
  eternal                     x     := x = MensThing.deus
  -- AttrStructure / AttrWorld (`Ethica/Attributum/Core.lean`)
  perSeConceivedAttr          _     := True
  expressesEternalEssenceAttr _     := True
  perceivedAsEssence          s _   := s = MensThing.deus
  -- CausalWorld (`Ethica/Pars1/Causation.lean`)
  Cause                             := mensCause
  intelligibleThrough         e c   := mensCause c e
  -- InherenceWorld (`Ethica/Pars1/Inherence.lean`)
  inheresIn                   x y   := x ≠ MensThing.deus ∧ y = MensThing.deus
  -- ConsecutioWorld (`Ethica/Pars1/Consecutio.lean`)
  followsFrom                 x y   := mensCause y x
  followsAbsolutely           _ _   := False
  -- Pars2World (`Ethica/Pars2/Idea.lean`)
  ideaOf                      i x   := i = MensThing.idea x
  cogitatio                         := MensAttr.cogitatio
  extensio                          := MensAttr.extensio
  -- QuatenusWorld (`Ethica/Pars2/Quatenus.lean`)
  modeUnder                   x a   := mensAttrOf x = some a
  causeUnder                  c e a := mensCause c e ∧ mensAttrOf e = some a
  involvesConceptOf           x a   := mensAttrOf x = some a
  -- ParallelismusWorld (`Ethica/Pars2/Parallelismus.lean`)
  durat                             := mensDurat
  essentiaFormalisIn          x a   := mensAttrOf x = some a
  comprehensaIn               i j   :=
    mensAttrOf i = some MensAttr.cogitatio ∧ j = MensThing.idea MensThing.deus

/-- `deus` is a substance; nothing else is. -/
theorem mens_substance_iff (x : MensThing) :
    Substance x ↔ x = MensThing.deus :=
  ⟨fun h => h.1, fun h => ⟨h, h⟩⟩

/-- Every idea is a mode. -/
theorem mens_idea_isMode (x : MensThing) : Mode (MensThing.idea x) :=
  ⟨mens_idea_ne_deus x, mens_idea_ne_deus x⟩

/-- Every singular thing is a mode — of `extensio`, which is what
    makes Prop. VI's corollary non-vacuous here. -/
theorem mens_res_isMode (n : Int) : Mode (MensThing.res n) :=
  ⟨mens_res_ne_deus n, mens_res_ne_deus n⟩

/-- **Nothing is finite-after-its-kind in Pars I's sense**, even now
    that `limitedBy` is a rich relation. The reason is structural, not
    a choice of this model: `finitumInSuoGenere` routes through
    `sameNature`, which carries `Substance`, and `limitedBy` here
    holds only of things with a singular index — never of `deus`.

    This is the model-side face of
    `Ethica.Pars2.pars1_prop_28_vacuous_for_modes`. -/
theorem mens_not_finite (x : MensThing) : ¬ finitumInSuoGenere x := by
  rintro ⟨_, _, ⟨_, hax, _⟩, hlim⟩
  have hx : x = MensThing.deus := hax.1.1
  subst hx
  exact hlim.1 rfl

/-! ### *Res singulares* in this model

  `ResSingularis x` holds exactly when `mensIndex x ≠ none` — that
  is, for `res n` and every idea above it, and for nothing in the
  `idea…deus` family. -/

/-- A *res singularis* has a singular index. -/
theorem mens_index_of_singularis (x : MensThing)
    (h : ResSingularis (Attr := MensAttr) x) : mensIndex x ≠ none := by
  obtain ⟨_, _, _, hlim⟩ := h.2
  exact hlim.1

/-- …and conversely. The limiting witness is `mensPred x`: it is
    distinct from `x`, is a mode of the same attribute
    (`mens_pred_attrOf`), and stays singular
    (`mens_pred_index`). -/
theorem mens_singularis_of_index (x : MensThing) (h : mensIndex x ≠ none) :
    ResSingularis (Attr := MensAttr) x := by
  have hne : x ≠ MensThing.deus := by
    intro hc; subst hc; exact h rfl
  obtain ⟨a, ha⟩ := mens_attrOf_isSome x hne
  exact ⟨⟨hne, hne⟩, mensPred x, mens_pred_ne x h,
    ⟨a, ha, (mens_pred_attrOf x).trans ha⟩,
    h, mens_pred_index x h, mens_pred_ne x h⟩

/-- The characterisation, as an `Iff`. -/
theorem mens_singularis_iff_index (x : MensThing) :
    ResSingularis (Attr := MensAttr) x ↔ mensIndex x ≠ none :=
  ⟨mens_index_of_singularis x, mens_singularis_of_index x⟩

/-- **God's infinite idea is not a singular thing.** Prop. VIII
    compares the two containments precisely because they are
    different; a model in which `idea deus` counted as a *res
    singularis* would collapse the comparison. -/
theorem mens_ideaDei_non_singularis :
    ¬ ResSingularis (Attr := MensAttr) (MensThing.idea MensThing.deus) := by
  intro h
  exact mens_index_of_singularis _ h rfl

/-! ## The axioms -/

/-- The full register on one carrier: A1–A15, A4ₛ/A5ₛ, A33–A43,
    A10′–A15′, A45–A50, A51–A55, A56–A59.

    Discharge notes, honestly:

    - **Vacuous**: A5ₛ (`sameNature deus deus` holds, so its
      `¬ sameNature` hypothesis is never met — and it is
      substance-restricted, so `deus` is the only case); A39/A40
      (`followsAbsolutely` is empty); A41 (a mode is never `Eternal`
      here); **A42** (nothing is finite-after-its-kind — and by
      `pars1_prop_28_vacuous_for_modes` that is not a defect of this
      model but of the predicate, which is exactly why A59 exists).
    - **Non-vacuous**: A33 (every non-God really is a mode and really
      inheres in `deus`), A34/A37/A38 (real causal facts), A43
      (`mens_succ_cause`'s induction), A45 (constructor injectivity,
      not carrier degeneracy), A46/A47 (two *distinct* attributes),
      A48 (a real constructor disequality), A49 (a genuine successor
      witness), A50/A55 (the `mensCause_idea` clause), A51–A54 (all
      three *quatenus* primitives refuse every attribute but the
      thing's own, in both directions), **A56** (`durat` splits the
      carrier, so Prop. VIII's hypothesis is met by `res (-1)` and
      failed by `res 0`), **A57** (an `Iff` that holds by the
      recursive clause of `mensDurat`), **A58** (needs
      `mens_singularis_of_index`), and **A59** (needs
      `mens_pred_cause`, and with it the `Int` index — on `Nat` the
      axiom would be false in this model). -/
instance parallelismusAxioms : ParallelismusAxioms MensThing MensAttr where
  -- Pars1Axioms (A1–A15)
  ax1_inItselfOrInAnother                  := mens_deus_or_not
  ax1_exclusive                    _ h     := h.2 h.1
  ax2_perSeOrThroughAnother                := mens_deus_or_not
  ax3_causationDeterminate                 := trivial
  ax4_effectKnowledgeFromCause             := trivial
  ax5_nothingInCommonNoUnderstanding       := trivial
  ax6_trueIdeaAgreesWithIdeatum            := trivial
  ax7_conceivableAsNonExistent     _ h     := h
  ax_inItself_iff_perSeConceived   _       := Iff.rfl
  ax_inAnother_iff_conceivedThroughAnother _ := Iff.rfl
  ax_attribute_perSe               _ _ h   := h.2
  ax_causaSui_iff                  _       := Iff.rfl
  ax_substanceIdByAttribute        _ _ _ h₁ h₂ := h₁.1.1.trans h₂.1.1.symm
  ax_substance_has_attribute       s hs    := ⟨MensThing.deus, hs, rfl⟩
  ax_IsGod_has_attribute_of        _ _ _ hgod _ ha := ⟨hgod.1, ha.2⟩
  ax_substance_involves_existence  _ hs    := hs.1
  -- CausalAxioms (A4ₛ, A5ₛ)
  ax4_effectIntelligibleThroughCause _ _ h := h
  ax5_noCommonNoIntelligibility := by
    intro x y hx hy hns
    have hx' : x = MensThing.deus := hx.1
    have hy' : y = MensThing.deus := hy.1
    subst hx'; subst hy'
    exact absurd ⟨MensThing.deus, ⟨⟨rfl, rfl⟩, rfl⟩, ⟨⟨rfl, rfl⟩, rfl⟩⟩ hns
  -- InherenceAxioms (A33–A36)
  ax_mode_inheres_in_substance x hm :=
    ⟨MensThing.deus, ⟨rfl, rfl⟩, hm.1, rfl⟩
  ax_inherence_causation := by
    intro x y h
    obtain ⟨hx, hy⟩ := h
    subst hy
    cases x with
    | deus   => exact absurd rfl hx
    | idea _ => trivial
    | res _  => trivial
  ax_mode_not_involvesExistence _ hm := hm.1
  ax_mode_constrained           _ hm := hm.1
  -- ConsecutioAxioms (A37–A43)
  ax_inherence_consecution := by
    intro x y h
    obtain ⟨hx, hy⟩ := h
    subst hy
    cases x with
    | deus   => exact absurd rfl hx
    | idea _ => trivial
    | res _  => trivial
  ax_consecution_causation _ _ h := h
  ax_absolute_consecution  _ _ h := h.elim
  ax_absoluteConsecution_eternalInfinite _ _ _ _ _ h := h.elim
  ax_infiniteModeTransfer _ m hm he _ _ := absurd he hm.1
  ax_finiteMode_causedByFiniteMode x _ hf := absurd hf (mens_not_finite x)
  ax_omnia_effectum := mens_hasEffect
  -- AttrAxioms (A10′, A12′, A14′, A15′)
  ax_attributum_perSe          _ _ _   := trivial
  ax_substanceIdByAttributum   _ _ _ h₁ h₂ := h₁.2.trans h₂.2.symm
  ax_substance_has_attributum  s hs    := ⟨MensAttr.cogitatio, hs, hs.1⟩
  ax_IsGod_has_attributum_of   _ _ _ hgod _ _ := ⟨hgod.1, hgod.1.1⟩
  -- Pars2Axioms (A45–A50)
  ax6_idea_unique_ideatum := by
    intro i x y hx hy
    subst hx
    injection hy
  ax_cogitatio_attributum _ hgod := ⟨hgod.1, hgod.1.1⟩
  ax_extensio_attributum  _ hgod := ⟨hgod.1, hgod.1.1⟩
  ax_cogitatio_ne_extensio := by decide
  ax_god_has_idea_of_all x := ⟨MensThing.idea x, rfl⟩
  ax_idea_tracks_intelligibility := by
    intro e c h ie ic hie hic
    subst hie; subst hic
    exact h
  -- QuatenusAxioms (A51–A55)
  ax_modeUnder_conceptum := by
    intro x a hxa
    refine ⟨hxa, ?_⟩
    intro b hb hcb
    exact hb (Option.some.inj (hcb.symm.trans hxa))
  ax_causeUnder_involvesConcept _ _ _ h := h.2
  ax_cause_refines_to_attribute _ _ _ hc hm := ⟨hc, hm⟩
  ax_idea_modeUnder_cogitatio := by
    intro i x h
    subst h
    rfl
  ax_idea_order_reflects := by
    intro ic ie h c e hic hie
    subst hic; subst hie
    exact h
  -- ParallelismusAxioms (A56–A59)
  ax_prop8_esseObjectivum := by
    intro x i ig g hx _ hi hgod hig
    have hg : g = MensThing.deus := hgod.1.1
    subst hg
    subst hig
    subst hi
    constructor
    · intro _
      exact mens_attrOf_isSome x hx.1.1
    · intro _
      exact ⟨rfl, rfl⟩
  ax_idea_durat_iff := by
    intro i x h
    subst h
    exact Iff.rfl
  ax_idea_singularis := by
    intro i x h hx
    subst h
    exact mens_singularis_of_index (MensThing.idea x)
      (mens_index_of_singularis x hx)
  ax_singulare_causatum := by
    intro x hx
    have hidx := mens_index_of_singularis x hx
    exact ⟨mensPred x, mens_singularis_of_index _ (mens_pred_index x hidx),
      (mens_pred_ne x hidx).symm, mens_pred_cause x hidx⟩

/-! ## The results -/

/-- `deus` is God in the re-typed sense. -/
theorem mens_deus_isGod : IsGodAttr (Attr := MensAttr) MensThing.deus :=
  ⟨⟨rfl, rfl⟩, rfl, ⟨MensAttr.cogitatio, ⟨rfl, rfl⟩, rfl⟩, fun _ _ => trivial⟩

/-- `deus` is also God in Pars I's sense — this model satisfies the
    full `Pars1Axioms` register, so Pars I's theorems apply to it. -/
theorem mens_deus_isGod_pars1 : IsGod MensThing.deus :=
  ⟨⟨rfl, rfl⟩, rfl, ⟨MensThing.deus, ⟨rfl, rfl⟩, rfl⟩, fun _ ha => ha.2⟩

/-- **Props. II.I and II.II hold together**: God has two distinct
    attributes here, via `prop_2_1_2_deusHabetDuoAttributa`. -/
theorem mens_duo_attributa :
    hasAtLeastNAttrs (Attr := MensAttr) MensThing.deus 2 :=
  prop_2_1_2_deusHabetDuoAttributa MensThing.deus mens_deus_isGod

/-- **And Pars I's collapse still holds, in the same world.** No God
    here has two `Thing`-typed attributes — `god_no_two_attributes`
    applies, because `Pars1Axioms` genuinely holds. -/
theorem mens_pars1_collapse_holds :
    ¬ hasAtLeastNAttributes MensThing.deus 2 :=
  god_no_two_attributes MensThing.deus mens_deus_isGod_pars1

/-- The coexistence, in one statement. -/
theorem mens_coexistence :
    hasAtLeastNAttrs (Attr := MensAttr) MensThing.deus 2 ∧
      ¬ hasAtLeastNAttributes MensThing.deus 2 :=
  ⟨mens_duo_attributa, mens_pars1_collapse_holds⟩

/-! ### Props. V and VI, applied to real modes of *both* attributes -/

/-- **Prop. II.VI on a mode of thought.** The idea of God is caused by
    God under `cogitatio` and under no other attribute. -/
theorem mens_prop_6 :
    QuatenusWorld.causeUnder MensThing.deus
        (MensThing.idea MensThing.deus) MensAttr.cogitatio ∧
      ∀ b : MensAttr, b ≠ MensAttr.cogitatio →
        ¬ QuatenusWorld.causeUnder MensThing.deus
            (MensThing.idea MensThing.deus) b :=
  prop_2_6_modiSubSuoAttributo MensThing.deus mens_deus_isGod_pars1
    (MensThing.idea MensThing.deus) (mens_idea_isMode MensThing.deus)
    MensAttr.cogitatio rfl

/-- **Prop. II.VI on a mode of extension** — the result batch 1.2's
    witness could not state, because its carrier had no such mode.
    `res 0` is caused by God under `extensio` and under no other
    attribute. -/
theorem mens_prop_6_extensio :
    QuatenusWorld.causeUnder MensThing.deus (MensThing.res 0) MensAttr.extensio ∧
      ∀ b : MensAttr, b ≠ MensAttr.extensio →
        ¬ QuatenusWorld.causeUnder MensThing.deus (MensThing.res 0) b :=
  prop_2_6_modiSubSuoAttributo MensThing.deus mens_deus_isGod_pars1
    (MensThing.res 0) (mens_res_isMode 0) MensAttr.extensio rfl

/-- Prop. II.VI cor. cashed out, **non-vacuously**: what is not a mode
    of thought is not caused by God *qua* thinking thing. `res 0` is a
    real mode with a real attribute, and `mens_prop_6_extensio.1`
    exhibits the same relation holding under `extensio`. -/
theorem mens_prop_6_cor_res :
    ¬ QuatenusWorld.causeUnder MensThing.deus (MensThing.res 0)
        MensAttr.cogitatio :=
  prop_2_6_cor_nonPerCogitationem MensThing.deus mens_deus_isGod_pars1
    (MensThing.res 0) (mens_res_isMode 0) MensAttr.extensio rfl
    (by decide)

/-- The exclusion clause of Prop. V: God does *not* cause the idea of
    God *qua* extended thing. -/
theorem mens_prop_5_non_extensione :
    ¬ QuatenusWorld.causeUnder MensThing.deus
        (MensThing.idea MensThing.deus) MensAttr.extensio :=
  prop_2_5_cor_nonSubExtensione MensThing.deus mens_deus_isGod_pars1
    (MensThing.idea MensThing.deus) MensThing.deus rfl
    (mens_idea_isMode MensThing.deus)

/-- **Prop. II.VII as a biconditional** (batch 1.2's GAP-27a result),
    instantiated. -/
theorem mens_prop_7_iff (c e : MensThing) :
    mensCause c e ↔ mensCause (MensThing.idea c) (MensThing.idea e) :=
  prop_2_7_ordoEtConnexio_iff (Attr := MensAttr) c e
    (MensThing.idea c) (MensThing.idea e) rfl rfl

/-! ### Batch 1.3's results, applied -/

/-- Every `res n` is a *res singularis*. -/
theorem mens_res_isSingularis (n : Int) :
    ResSingularis (Attr := MensAttr) (MensThing.res n) :=
  mens_singularis_of_index _ (fun h => Option.noConfusion h)

/-- `res (-1)` does not endure. -/
theorem mens_res_neg_non_durat :
    ¬ ParallelismusWorld.durat (MensThing.res (-1)) := by
  show ¬ ((0 : Int) ≤ -1)
  omega

/-- `res 0` does. -/
theorem mens_res_zero_durat :
    ParallelismusWorld.durat (MensThing.res 0) := by
  show (0 : Int) ≤ 0
  omega

/-- **Prop. II.VIII on a thing that really does not exist.**
    `res (-1)` is singular and does not endure, so the proposition's
    hypothesis is met; its idea is comprehended in God's infinite idea
    exactly as its formal essence is contained in an attribute. -/
theorem mens_prop_8 :
    ParallelismusWorld.comprehensaIn (MensThing.idea (MensThing.res (-1)))
        (MensThing.idea MensThing.deus) ↔
      ∃ a : MensAttr,
        ParallelismusWorld.essentiaFormalisIn (MensThing.res (-1)) a :=
  prop_2_8_ideaeRerumNonExistentium MensThing.deus
    (MensThing.idea MensThing.deus) (MensThing.res (-1))
    (MensThing.idea (MensThing.res (-1)))
    mens_deus_isGod_pars1 rfl (mens_res_isSingularis (-1))
    mens_res_neg_non_durat rfl

/-- The hypothesis of Prop. VIII is genuinely met — and genuinely
    fails elsewhere. `res (-1)` does not endure; `res 0` does. So the
    proposition is not satisfied here by an empty antecedent. -/
theorem mens_durat_splits :
    ¬ ParallelismusWorld.durat (MensThing.res (-1)) ∧
      ParallelismusWorld.durat (MensThing.res 0) :=
  ⟨mens_res_neg_non_durat, mens_res_zero_durat⟩

/-- **Prop. II.VIII cor.**: the idea of `res n` endures exactly when
    `res n` does. -/
theorem mens_prop_8_cor (n : Int) :
    ParallelismusWorld.durat (MensThing.idea (MensThing.res n)) ↔
      ParallelismusWorld.durat (MensThing.res n) :=
  prop_2_8_cor_esseObjectivum (Attr := MensAttr)
    (MensThing.idea (MensThing.res n)) (MensThing.res n) rfl

/-- **Prop. II.IX**: the idea of a singular thing is caused by another
    idea, itself the idea of a singular thing.

    Non-vacuous on every rung: the object is `res n`, the other
    singular cause is `res (n+1)`, and the causing idea is
    `idea (res (n+1))`. -/
theorem mens_prop_9 (n : Int) :
    ∃ j y : MensThing,
      ResSingularis (Attr := MensAttr) y ∧ y ≠ MensThing.res n ∧
        CausalWorld.Cause y (MensThing.res n) ∧
        Pars2World.ideaOf j y ∧ ResSingularis (Attr := MensAttr) j ∧
        j ≠ MensThing.idea (MensThing.res n) ∧
        CausalWorld.Cause j (MensThing.idea (MensThing.res n)) :=
  prop_2_9_ideaSingularisAbAliaIdea (Attr := MensAttr)
    (MensThing.idea (MensThing.res n)) (MensThing.res n) rfl
    (mens_res_isSingularis n)

/-- **Prop. II.IX's *et sic in infinitum*** applies here. Unlike
    `prop_28_cor_noFirstFiniteCause` in Pars I, whose hypothesis is
    unsatisfiable, this one refutes a class that is genuinely
    inhabited: `mens_res_isSingularis` supplies witnesses at every
    index. -/
theorem mens_prop_9_cor :
    ¬ ∃ i x : MensThing, Pars2World.ideaOf i x ∧
      ResSingularis (Attr := MensAttr) x ∧
      ∀ j : MensThing, ResSingularis (Attr := MensAttr) j → j ≠ i →
        ¬ CausalWorld.Cause j i :=
  prop_2_9_cor_nullaPrimaIdea (Attr := MensAttr)

/-- **Prop. I.XXVIII is vacuous here — and everywhere.** The Pars I
    finitude predicate cannot hold of a mode in *any* `Pars1Axioms`
    world, so A42 never fires; A59 is the repair, and
    `mens_prop_9` is what it buys. -/
theorem mens_pars1_prop28_vacuous :
    ¬ ∃ x : MensThing, Mode x ∧ finitumInSuoGenere x :=
  pars1_prop_28_vacuous_for_modes

/-! ## Sanity checks -/

/-- Prop. II.III applies — everything has an idea. -/
example (x : MensThing) : ∃ i : MensThing, Pars2World.ideaOf i x :=
  prop_2_3_ideaOmnium (Attr := MensAttr) x

/-- Prop. II.III *in Deo* applies — that idea is in God. -/
example (x : MensThing) :
    ∃ i : MensThing, Pars2World.ideaOf i x ∧
      (i = MensThing.deus ∨ InherenceWorld.inheresIn i MensThing.deus) :=
  prop_2_3_ideaInDeo (Attr := MensAttr) MensThing.deus mens_deus_isGod_pars1 x

/-- Prop. II.VII (corollary form) applies. -/
example (c e : MensThing) (h : CausalWorld.Cause c e) :
    ∃ ic ie : MensThing,
      Pars2World.ideaOf ic c ∧ Pars2World.ideaOf ie e ∧
        CausalWorld.Cause ic ie :=
  prop_2_7_cor_ideaePariter (Attr := MensAttr) c e h

/-- Prop. II.VII cor. (the *hoc est* clause) applies. -/
example (x : MensThing) (h : ConsecutioWorld.followsFrom x MensThing.deus) :
    ∃ ix ig : MensThing, Pars2World.ideaOf ix x ∧
      Pars2World.ideaOf ig MensThing.deus ∧ CausalWorld.Cause ig ix :=
  prop_2_7_cor_ordoObjectivus (Attr := MensAttr) MensThing.deus x h

/-- Prop. II.IX cor. (partial) applies. -/
example (n : Int) :
    ∃ i : MensThing, Pars2World.ideaOf i (MensThing.res n) ∧
      (i = MensThing.deus ∨ InherenceWorld.inheresIn i MensThing.deus) ∧
      QuatenusWorld.causeUnder MensThing.deus i MensAttr.cogitatio ∧
      ∀ b : MensAttr, b ≠ MensAttr.cogitatio →
        ¬ QuatenusWorld.causeUnder MensThing.deus i b :=
  prop_2_9_cor_cognitioInDeo MensThing.deus mens_deus_isGod_pars1
    (MensThing.res n) (mens_res_isSingularis n)

/-- Prop. I.XIV still applies — `deus` is the only substance. The
    Pars I layer is entirely intact under this model. -/
example (s : MensThing) (hs : Substance s) : s = MensThing.deus :=
  prop_14_onlyGodIsSubstance MensThing.deus mens_deus_isGod_pars1 s hs

/-- Prop. I.XV still applies — everything is in God. -/
example (x : MensThing) :
    x = MensThing.deus ∨ InherenceWorld.inheresIn x MensThing.deus :=
  prop_15_allInGod MensThing.deus mens_deus_isGod_pars1 x

/-- Prop. I.XXXVI still applies — nothing exists without an effect. -/
example (x : MensThing) : ∃ e : MensThing, CausalWorld.Cause x e :=
  prop_36_nothingWithoutEffect x

end Ethica.Pars2.Models.MensWitness
