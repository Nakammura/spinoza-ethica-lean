/-
  Spinoza, *Ethica* Pars I — multi-world bench for the modal layer.

  `SingleSubstance.lean` provides modal-layer instances on
  `Unit × Unit`, but this triggers the **S5 modal collapse**: with
  one element and one world, every `∀ w, P w` reduces to `P ()`,
  and every bridge axiom (A18, A21) discharges trivially because
  both sides of the iff reduce to the same constant. The collapse
  hides whether the bridge is doing any work.

  This file builds a **multi-world bench** designed to make the
  bridge axioms fire **non-vacuously**. It is intentionally minimal
  — only the structures needed to exercise A18 (`involvesExistence
  ↔ ∀ w, existsAt`) — and does not claim a full `Pars1Axioms` /
  `CausalAxioms` instance.

  ## What this model exercises

  Two things, two worlds:
  - `necessary` — exists at every world (`∀ w, existsAt`).
  - `contingent` — exists at `w0` only.

  A18 then fires non-vacuously:
  - For `necessary`: `involvesExistence necessary = True` and
    `∀ w, existsAt necessary w = True`. Both sides True.
  - For `contingent`: `involvesExistence contingent = False` and
    `∀ w, existsAt contingent w = False` (because
    `existsAt contingent w1 = False`). Both sides False.

  The `False ↔ False` case for `contingent` is the non-trivial
  bite — it is **not** discharged by `Iff.rfl` on a constant; the
  proof must actually use `existsAt contingent w1 = False` to make
  the universal proposition False.

  ## What this model does *not* do

  - Does not claim `Pars1Axioms` / `CausalAxioms` instances. These
    require all 14 fields and the relevant Section III commitments
    (A12, A13, A14, A15) which are tangential to the bridge-bite
    test.
  - Does not exercise A21 (`Cause ↔ ∀ w, causeAt`). A separate
    bench for A21 is a natural follow-up but is not in this
    commit.
  - Does not exercise the modal-layer Section III candidates A16,
    A17 (Prop. I priority asymmetry). Those need
    `ConceptualDepAxioms` instance discharge, also a follow-up.

  This is the **A18 bridge-bite witness**. Multi-bridge benches
  can be added incrementally.
-/
import Ethica.Pars1.Definitions
import Ethica.Pars1.ModalForm

namespace Ethica.Pars1.Models.MultiWorld

open Ethica.Pars1
open EthicaWorld

/-- Two-element thing universe: a *necessary* substance and a
    *contingent* mode. -/
inductive ThingT where
  | necessary : ThingT
  | contingent : ThingT
  deriving DecidableEq

/-- Two-element world type. -/
inductive WorldT where
  | w0 : WorldT
  | w1 : WorldT
  deriving DecidableEq

/-- `EthicaWorld` instance distinguishing the two things. -/
instance ethicaWorld : EthicaWorld ThingT where
  inItself
    | ThingT.necessary => True
    | ThingT.contingent => False
  perSeConceived
    | ThingT.necessary => True
    | ThingT.contingent => False
  involvesExistence
    | ThingT.necessary => True
    | ThingT.contingent => False
  natureRequiresExistence
    | ThingT.necessary => True
    | ThingT.contingent => False
  inAnother
    | ThingT.necessary => False
    | ThingT.contingent => True
  conceivedThroughAnother
    | ThingT.necessary => False
    | ThingT.contingent => True
  limitedBy _ _ := False
  intellectPerceivesAsEssence
    | ThingT.necessary, ThingT.necessary => True
    | _, _ => False
  absolutelyInfinite
    | ThingT.necessary => True
    | ThingT.contingent => False
  expressesEternalEssence
    | ThingT.necessary => True
    | ThingT.contingent => False
  freelyExistent
    | ThingT.necessary => True
    | ThingT.contingent => False
  constrained
    | ThingT.necessary => False
    | ThingT.contingent => True
  eternal
    | ThingT.necessary => True
    | ThingT.contingent => False

/-- `ModalEthicaWorld` instance: `necessary` exists at every world,
    `contingent` only at `w0`. The non-uniform graph is what makes
    A18 fire non-vacuously. -/
instance modalEthicaWorld : Modal.ModalEthicaWorld ThingT WorldT where
  toEthicaWorld := ethicaWorld
  existsAt
    | ThingT.necessary, _ => True
    | ThingT.contingent, WorldT.w0 => True
    | ThingT.contingent, WorldT.w1 => False

/-- A18 holds non-vacuously on this model. The proof must
    case-analyse on `ThingT`: the `necessary` branch is the
    True-↔-True trivial case, the `contingent` branch is the
    False-↔-False *non-trivial* case where the right-hand side's
    universal proposition collapses through the
    `existsAt contingent w1 = False` clause. -/
instance modalEthicaAxioms : Modal.ModalEthicaAxioms ThingT WorldT where
  ax_involvesExistence_iff_necExists x := by
    cases x
    · -- ThingT.necessary: True ↔ ∀ w, True
      constructor
      · intro _ _; trivial
      · intro _; trivial
    · -- ThingT.contingent: False ↔ ∀ w, existsAt contingent w
      -- where existsAt contingent w1 = False, so the universal
      -- proposition is False. Both sides False; the iff is
      -- non-vacuous.
      constructor
      · intro h; exact h.elim
      · intro h
        -- Apply h to w1: existsAt contingent w1 = False.
        exact (h WorldT.w1).elim

/-! ## Witness theorems

  Concrete examples showing A18's non-vacuous bite. -/

/-- `necessary` exists at every world, witnessed via A18 from its
    `involvesExistence`. -/
example : ∀ w : WorldT,
    @Modal.ModalEthicaWorld.existsAt ThingT WorldT modalEthicaWorld
      ThingT.necessary w :=
  (Modal.ModalEthicaAxioms.ax_involvesExistence_iff_necExists
    (Thing := ThingT) (World := WorldT) ThingT.necessary).mp
    trivial

/-- `contingent` does **not** exist at every world. Verified by
    exhibiting a world (`w1`) where it does not exist. This is the
    non-trivial direction of A18 bite — without the bridge, we'd
    have no link between `involvesExistence contingent = False` and
    the contingent-existence pattern. -/
example : ¬ ∀ w : WorldT,
    @Modal.ModalEthicaWorld.existsAt ThingT WorldT modalEthicaWorld
      ThingT.contingent w := by
  intro h
  exact (h WorldT.w1).elim

/-- Sanity: the contrapositive direction of A18 also fires. From
    `¬ ∀ w, existsAt contingent w` we can conclude
    `¬ involvesExistence contingent` via the bridge — which on
    `ThingT` is just `¬ False`, hence trivial, but the reasoning
    chain is non-vacuous. -/
example : ¬ @involvesExistence ThingT ethicaWorld ThingT.contingent := by
  intro h
  -- A18 gives: involvesExistence ↔ ∀ w, existsAt contingent w.
  have hnec : ∀ w : WorldT,
      @Modal.ModalEthicaWorld.existsAt ThingT WorldT modalEthicaWorld
        ThingT.contingent w :=
    (Modal.ModalEthicaAxioms.ax_involvesExistence_iff_necExists
      (Thing := ThingT) (World := WorldT) ThingT.contingent).mp h
  exact (hnec WorldT.w1).elim

end Ethica.Pars1.Models.MultiWorld
