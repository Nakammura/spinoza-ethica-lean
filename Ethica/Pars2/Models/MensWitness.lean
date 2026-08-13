/-
  Spinoza, *Ethica* Pars II — consistency witness for the idea layer
  and the *quatenus* layer (batches 1.1 and 1.2).

  Carries a full `QuatenusAxioms` instance on one carrier:
  `Pars1Axioms` (A1–A15) + `CausalAxioms` (A4ₛ, A5ₛ) +
  `InherenceAxioms` (A33–A36) + `ConsecutioAxioms` (A37–A43) +
  `AttrAxioms` (A10′/A12′/A14′/A15′) + `Pars2Axioms` (A45–A50) +
  `QuatenusAxioms` (A51–A55). So neither layer introduces a
  contradiction, and Props. II.I–II.VII are not vacuously true by
  explosion.

  **The carrier has genuine modes.** Batch 1.1's witness was a
  one-element type, which made every mode-conditioned proposition
  vacuous. That is not good enough for batch 1.2: Props. V and VI
  *are* propositions about modes, so a witness whose `Mode` predicate
  is uniformly `False` proves nothing about them. The carrier here is

      inductive MensThing | deus | idea : MensThing → MensThing

  — God, plus the *idea ideae in infinitum* of Prop. II.XXI's
  scholium. `deus` is the unique substance; every `idea x` is a mode.
  This is forced, not decorative: A45 (an idea has a unique ideatum)
  together with A49 (everything has an idea) and A54 (ideas are modes
  of thought, hence distinct from the unique substance) are **jointly
  unsatisfiable on any finite carrier**. Spinoza's own infinite
  regress of ideas is what makes the register consistent.

  **The causal order is not constant.** `mensCause` says: God causes
  every mode and nothing causes God, and the idea of `c` causes the
  idea of `e` exactly when `c` causes `e`. So

  - `mens_cause_irreflexive_deus` — `Cause` is *not* uniformly `True`
    (`¬ Cause deus deus`), hence Prop. VII's biconditional
    (`prop_2_7_ordoEtConnexio_iff`) is not trivially satisfied here;
  - A50 and A55 both discharge on real structure rather than on a
    constant, and A43 (`ax_omnia_effectum`) needs the induction
    `mens_hasEffect` rather than a one-element reflexivity.

  **And it still holds both attribute verdicts at once**, as batch
  1.1's witness did:

  - `mens_pars1_collapse_holds` — no God has two `Thing`-typed
    attributes (`Ethica.Pars1.god_no_two_attributes` applied here,
    valid because `Pars1Axioms` genuinely holds);
  - `mens_duo_attributa` — God *does* have two `Attr`-typed
    attributes, `cogitatio` and `extensio`.

  There is no tension: the `Thing`-typed attribution channel is
  degenerate exactly as the collapse theorem forces (God is its own
  only `Thing`-typed attribute), while the load-bearing attribute
  structure lives in `MensAttr`.
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

namespace Ethica.Pars2.Models.MensWitness

open Ethica.Pars1
open Ethica.Attributum
open Ethica.Pars2

/-- The thing universe: God, and the infinite ladder of ideas above
    him. `idea x` is *the* idea of `x` — including `idea (idea x)`,
    the idea of an idea, which Spinoza insists on (Prop. II.XXI sch.)
    and which A45 + A49 + A54 jointly force any model to contain. -/
inductive MensThing where
  | deus
  | idea : MensThing → MensThing
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

/-- Every thing either is God or is not — by cases on the carrier, so
    A1 and A2 discharge without `Classical.em`. -/
theorem mens_deus_or_not (x : MensThing) :
    x = MensThing.deus ∨ x ≠ MensThing.deus := by
  cases x with
  | deus => exact Or.inl rfl
  | idea y => exact Or.inr (mens_idea_ne_deus y)

/-- The causal order. God causes every mode; nothing causes God; and
    the idea of `c` causes the idea of `e` exactly when `c` causes
    `e`.

    The last clause is Prop. II.VII built into the model by
    construction — which is what makes A50/A55 discharge on structure
    rather than on a constant. -/
def mensCause : MensThing → MensThing → Prop
  | .deus,   .deus   => False
  | .deus,   .idea _ => True
  | .idea _, .deus   => False
  | .idea c, .idea e => mensCause c e

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

/-- Everything has an effect — by induction on the ladder. God's
    effect is the idea of God; the effect of `idea c` is the idea of
    `c`'s effect. This is what discharges A43
    (`ax_omnia_effectum`) **non-vacuously**; a one-element carrier
    gets A43 for free by reflexivity, this one does not. -/
theorem mens_hasEffect (x : MensThing) : ∃ e, mensCause x e := by
  induction x with
  | deus => exact ⟨MensThing.idea MensThing.deus, trivial⟩
  | idea c ih =>
      obtain ⟨e, he⟩ := ih
      exact ⟨MensThing.idea e, he⟩

/-! ## The world -/

/-- The full world instance: Pars I's thirteen primitives, the
    Attributum layer's attribute channel, the causal / inherence /
    consecution relations, Pars II's `ideaOf` with its two named
    attributes, and the three *quatenus* primitives.

    Profile in one line: **`deus` is the unique substance and every
    `idea x` is a mode**, `limitedBy` is empty (so nothing is
    finite-after-its-kind), the `Thing`-typed attribute channel picks
    out `deus` alone, and the `Attr`-typed one gives `deus` both of
    its attributes.

    The three *quatenus* primitives are genuinely selective: only
    `cogitatio` ever appears in them. That is what gives Props. V and
    VI real content in this model — their exclusion clauses are not
    satisfied by an empty relation but by a relation that actually
    refuses `extensio`. -/
instance quatenusWorld : QuatenusWorld MensThing MensAttr where
  -- EthicaWorld (Pars I, `Definitions.lean`)
  inItself                    x     := x = MensThing.deus
  perSeConceived              x     := x = MensThing.deus
  involvesExistence           x     := x = MensThing.deus
  natureRequiresExistence     x     := x = MensThing.deus
  inAnother                   x     := x ≠ MensThing.deus
  conceivedThroughAnother     x     := x ≠ MensThing.deus
  limitedBy                   _ _   := False
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
  modeUnder                   x a   := x ≠ MensThing.deus ∧ a = MensAttr.cogitatio
  causeUnder                  c e a :=
    mensCause c e ∧ e ≠ MensThing.deus ∧ a = MensAttr.cogitatio
  involvesConceptOf           x a   := x ≠ MensThing.deus ∧ a = MensAttr.cogitatio

/-- `deus` is a substance; nothing else is. -/
theorem mens_substance_iff (x : MensThing) :
    Substance x ↔ x = MensThing.deus :=
  ⟨fun h => h.1, fun h => ⟨h, h⟩⟩

/-- Every idea is a mode — the fact that makes Props. V and VI
    non-vacuous here. -/
theorem mens_idea_isMode (x : MensThing) : Mode (MensThing.idea x) :=
  ⟨mens_idea_ne_deus x, mens_idea_ne_deus x⟩

/-- Nothing is finite-after-its-kind: `limitedBy` is empty, and
    `finitumInSuoGenere` requires a limiting witness. -/
theorem mens_not_finite (x : MensThing) : ¬ finitumInSuoGenere x := by
  rintro ⟨_, _, _, hlim⟩
  exact hlim.elim

/-! ## The axioms -/

/-- The full register on one carrier: A1–A15, A4ₛ/A5ₛ, A33–A43,
    A10′–A15′, A45–A50, A51–A55.

    Discharge notes, honestly:

    - **Vacuous**: A5ₛ (`sameNature deus deus` holds, so its
      `¬ sameNature` hypothesis is never met — and it is
      substance-restricted, so `deus` is the only case); A39/A40
      (`followsAbsolutely` is empty); A41 (a mode is never `Eternal`
      here); A42 (nothing is finite-after-its-kind).
    - **Non-vacuous**: A33 (every `idea x` really is a mode and
      really inheres in `deus`), A34/A37/A38 (real causal facts),
      A43 (needs `mens_hasEffect`'s induction), A45 (constructor
      injectivity, not carrier degeneracy), A46/A47 (two *distinct*
      attributes), A48 (a real constructor disequality), A49 (a
      genuine successor witness), A50/A55 (the `mensCause_idea`
      clause), and **A51–A54**, which are the point of batch 1.2:
      `modeUnder`, `causeUnder` and `involvesConceptOf` all refuse
      `extensio`, so Props. V and VI's exclusion clauses hold
      substantively. -/
instance quatenusAxioms : QuatenusAxioms MensThing MensAttr where
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
    | deus => exact absurd rfl hx
    | idea _ => trivial
  ax_mode_not_involvesExistence _ hm := hm.1
  ax_mode_constrained           _ hm := hm.1
  -- ConsecutioAxioms (A37–A43)
  ax_inherence_consecution := by
    intro x y h
    obtain ⟨hx, hy⟩ := h
    subst hy
    cases x with
    | deus => exact absurd rfl hx
    | idea _ => trivial
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
    refine ⟨⟨hxa.1, hxa.2⟩, ?_⟩
    intro b hb hcb
    exact hb (hcb.2.trans hxa.2.symm)
  ax_causeUnder_involvesConcept _ _ _ h := ⟨h.2.1, h.2.2⟩
  ax_cause_refines_to_attribute _ _ _ hc hm := ⟨hc, hm.1, hm.2⟩
  ax_idea_modeUnder_cogitatio := by
    intro i x h
    subst h
    exact ⟨mens_idea_ne_deus x, rfl⟩
  ax_idea_order_reflects := by
    intro ic ie h c e hic hie
    subst hic; subst hie
    exact h

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
    applies, because `Pars1Axioms` genuinely holds.

    Read together with `mens_duo_attributa`, this is the coexistence
    claim: the two attribution channels live side by side, the
    `Thing`-typed one degenerate exactly as the collapse theorem
    forces, the `Attr`-typed one carrying Pars II's structure. -/
theorem mens_pars1_collapse_holds :
    ¬ hasAtLeastNAttributes MensThing.deus 2 :=
  god_no_two_attributes MensThing.deus mens_deus_isGod_pars1

/-- The coexistence, in one statement. -/
theorem mens_coexistence :
    hasAtLeastNAttrs (Attr := MensAttr) MensThing.deus 2 ∧
      ¬ hasAtLeastNAttributes MensThing.deus 2 :=
  ⟨mens_duo_attributa, mens_pars1_collapse_holds⟩

/-! ### Props. V and VI, applied to a real mode

  These are the results batch 1.1's one-element witness could not
  state: `idea deus` is a genuine `Mode`, so Prop. VI's hypotheses are
  actually met, and its exclusion clause actually excludes something. -/

/-- **Prop. II.VI on a real mode.** The idea of God is caused by God
    under `cogitatio` and under no other attribute. -/
theorem mens_prop_6 :
    QuatenusWorld.causeUnder MensThing.deus
        (MensThing.idea MensThing.deus) MensAttr.cogitatio ∧
      ∀ b : MensAttr, b ≠ MensAttr.cogitatio →
        ¬ QuatenusWorld.causeUnder MensThing.deus
            (MensThing.idea MensThing.deus) b :=
  prop_2_6_modiSubSuoAttributo MensThing.deus mens_deus_isGod_pars1
    (MensThing.idea MensThing.deus) (mens_idea_isMode MensThing.deus)
    MensAttr.cogitatio ⟨mens_idea_ne_deus MensThing.deus, rfl⟩

/-- The exclusion clause, cashed out: God does *not* cause the idea of
    God *qua* extended thing. Not vacuous — `causeUnder … extensio`
    is a relation that genuinely fails to hold, not an empty one
    (`mens_prop_6.1` shows the same relation holding under
    `cogitatio`). -/
theorem mens_prop_5_non_extensione :
    ¬ QuatenusWorld.causeUnder MensThing.deus
        (MensThing.idea MensThing.deus) MensAttr.extensio :=
  prop_2_5_cor_nonSubExtensione MensThing.deus mens_deus_isGod_pars1
    (MensThing.idea MensThing.deus) MensThing.deus rfl
    (mens_idea_isMode MensThing.deus)

/-- **Prop. II.VII as a biconditional** (batch 1.2's GAP-27a result),
    instantiated. `mens_cause_irreflexive_deus` shows `Cause` is not
    constant here, so this is a claim with content: the two orders
    coincide because the model is built to make them coincide, not
    because everything causes everything. -/
theorem mens_prop_7_iff (c e : MensThing) :
    mensCause c e ↔ mensCause (MensThing.idea c) (MensThing.idea e) :=
  prop_2_7_ordoEtConnexio_iff (Attr := MensAttr) c e
    (MensThing.idea c) (MensThing.idea e) rfl rfl

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
