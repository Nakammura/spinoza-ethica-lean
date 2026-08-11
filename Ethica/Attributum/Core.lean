/-
  Spinoza, *Ethica* — Attributum (the re-typed attribute layer).

  **Why this layer exists.** `Ethica/Pars1/Realitas.lean` proves the
  *attribute-collapse theorem*: in any `Pars1Axioms` world containing
  a God, every attribute of every substance is identical to that God
  (`attribute_collapse`), hence God cannot have even two distinct
  attributes (`god_no_two_attributes`) and Def. VI's "*constantem
  infinitis attributis*" clause is outright unsatisfiable
  (`def6_infinitis_attributis_unsatisfiable`).

  That result is not merely a curiosity. It blocks Pars II at its
  first two propositions:

    *PROPOSITIO I: Cogitatio attributum Dei est sive Deus est res
     cogitans.*
    *PROPOSITIO II: Extensio attributum Dei est sive Deus est res
     extensa.*

  Thought and Extension are two *distinct* attributes of God. On the
  Pars I register that pair is inconsistent, so a Pars II built on it
  would be vacuously true by explosion.

  **The five-step collapse chain** (`Realitas.lean:133-149`), for
  reference:

    1. Attributes inhabit `Thing` itself (`Attribute a s` has
       `a : Thing`) — the Prop. X scholium reading.
    2. A10 makes any attribute of a substance per se conceived.
    3. A8 upgrades "per se conceived" to "in itself", so every
       attribute *is itself a substance* (`attribute_is_substance`).
    4. A14 gives that substance-which-is-an-attribute an attribute of
       its own.
    5. A15 hands that further attribute to God and A12 identifies the
       original attribute with God.

  **What this layer does.** It adopts escape route (iii) of GAP-25 —
  type attributes off the `Thing` universe entirely — implemented as
  a *parallel branch*, not as an edit. `AttrWorld` below carries a
  second type parameter `Attr`, and `Attributum a s` has `a : Attr`.
  Step 1 of the chain therefore never gets off the ground: `Substance
  a` does not typecheck for `a : Attr`, so `attribute_is_substance`
  is **inexpressible**, not merely false. The collapse dies at the
  ground floor.

  Note what this does *not* do. Prop. X survives: `perSeConceivedAttr`
  below is the attribute-side analogue of "per se conceived", and A10′
  (`Axioms.lean`) still asserts it of every attribute. What becomes
  inexpressible is the *bridge* — there is no axiom taking
  `perSeConceivedAttr a` to `inItself a`, because `inItself` is a
  predicate on `Thing` and `a : Attr`. This is precisely Bennett's
  position (1984 §16), who declined exactly the A8 coextension when
  the subject is an attribute, treating attributes as "basic and
  irreducible ways of being" rather than as things. Here his reading
  is enforced by the type system rather than by a restriction on an
  axiom.

  **Nothing in `Ethica/Pars1/` is modified.** The v1.0.0 register
  (`Pars1Axioms`, `CausalAxioms`) and the published irreducibility
  results (arXiv:2605.02331) stand untouched; `Bridge.lean` records
  the exact relation between the two regimes, and shows the collapse
  reappears as soon as one takes `Attr := Thing`. See GAP-25.
-/
import Ethica.Pars1.Definitions
import Ethica.Pars1.Axioms

namespace Ethica.Attributum

open Ethica.Pars1
open Ethica.Pars1.EthicaWorld

universe u v

/-- The intrinsic structure of the attribute universe.

    Deliberately parameterised by `Attr` **alone**. The two
    predicates below are properties an attribute has in its own
    right, with no reference whatever to the universe of things —
    which is exactly the content of treating attributes as, in
    Bennett's phrase, "basic and irreducible ways of being" rather
    than as a subspecies of thing. The type signature is the claim.

    Keeping this class separate from `AttrWorld` is not only
    hygiene: it makes it *visible in the signature* that nothing
    about an attribute's per-se-conceivedness depends on the thing
    universe, and therefore that no bridge back to `inItself` is
    being smuggled in. -/
class AttrStructure (Attr : Type v) where
  /-- `perSeConceivedAttr a` : "per se concipitur", said of an
      attribute. The attribute-side analogue of
      `EthicaWorld.perSeConceived`, and the reason Prop. X survives
      the re-typing (see A10′ in `Axioms.lean`).

      **This is where the collapse is blocked.** In Pars I, A8's
      coextension `inItself x ↔ perSeConceived x` applied to
      attributes because attributes *were* things. Here no axiom
      connects `perSeConceivedAttr a` to `inItself`, and none can be
      stated: `inItself : Thing → Prop` while `a : Attr`, and this
      class does not even mention `Thing`. Bennett 1984 §16 declined
      this coextension for attributes on philosophical grounds; the
      type discipline enforces it. -/
  perSeConceivedAttr : Attr → Prop

  /-- `expressesEternalEssenceAttr a` : "*aeternam et infinitam
      essentiam exprimit*", said of an attribute — Def. VI's
      qualifying clause on each of God's attributes. The
      attribute-side analogue of
      `EthicaWorld.expressesEternalEssence`. -/
  expressesEternalEssenceAttr : Attr → Prop

/-- A world with attributes typed *separately* from things.

    `AttrWorld Thing Attr` extends `EthicaWorld Thing` — every
    Pars I primitive (`inItself`, `perSeConceived`, `inAnother`,
    `absolutelyInfinite`, …) is reused verbatim, so `Substance`,
    `Mode`, `causaSui` and the rest keep their Pars I meaning. It
    also extends `AttrStructure Attr`, the intrinsic structure of the
    attribute universe. What changes relative to Pars I is only the
    attribution channel: instead of routing through
    `intellectPerceivesAsEssence : Thing → Thing → Prop`, attribution
    goes through `perceivedAsEssence : Thing → Attr → Prop`.

    The new fields are genuine primitives, not definitions: there is
    deliberately **no map `Attr → Thing`** anywhere in this layer,
    since such a map would reinstate the collapse. -/
class AttrWorld (Thing : Type u) (Attr : Type v)
    extends EthicaWorld Thing, AttrStructure Attr where
  /-- `perceivedAsEssence s a` : the intellect perceives `a : Attr` as
      constituting the essence of the substance `s : Thing`. Def. IV,
      re-typed. Replaces `EthicaWorld.intellectPerceivesAsEssence`,
      which is left untouched but unused by this layer. -/
  perceivedAsEssence : Thing → Attr → Prop

section definitions

variable {Thing : Type u} {Attr : Type v} [AttrWorld Thing Attr]
open AttrWorld AttrStructure

/-! ## Definition IV — *Attributum*, re-typed

  Latin: *Per attributum intelligo id quod intellectus de substantia
         percipit tanquam ejusdem essentiam constituens.*

  Pars I read Spinoza's Prop. X scholium as placing attributes in the
  same universe as substances and modes (`Definitions.lean:149-157`).
  This layer declines that reading — the scholium says an attribute is
  conceived through itself, which A10′ still delivers, but it does not
  require attributes to *be* substances. Under the present typing they
  cannot be, as a matter of grammar. -/

/-- `Attributum a s` : the intellect perceives `a : Attr` as
    constituting the essence of the substance `s : Thing`.

    Compare `Ethica.Pars1.Attribute`, which is the same definition
    with `a : Thing`. The `Substance s` conjunct is retained verbatim
    from Pars I, so `Attributum` still carries substancehood of its
    second argument. -/
def Attributum (a : Attr) (s : Thing) : Prop :=
  Substance s ∧ perceivedAsEssence s a

/-- `sameNatureAttr x y` : `x` and `y` share at least one attribute.
    The re-typed counterpart of `Ethica.Pars1.sameNature`, on Della
    Rocca's constitutive reading of "same nature". -/
def sameNatureAttr (x y : Thing) : Prop :=
  ∃ a : Attr, Attributum a x ∧ Attributum a y

/-- `IsGodAttr g` : the re-typed Def. VI.

    Structurally identical to `Ethica.Pars1.IsGod` — substance,
    absolutely infinite, at least one attribute, and every attribute
    expressing eternal and infinite essence — with the two attribute
    clauses now quantifying over `Attr`. The `∃` clause is retained
    for the same reason Pars I retained it: a bare `∀` would be
    vacuously satisfiable by an attribute-free entity. -/
def IsGodAttr (g : Thing) : Prop :=
  Substance g
  ∧ absolutelyInfinite g
  ∧ (∃ a : Attr, Attributum a g)
  ∧ (∀ a : Attr, Attributum a g → expressesEternalEssenceAttr a)

/-- `hasAtLeastNAttrs s n` : `s` has at least `n` *distinct*
    attributes, encoded cardinality-free via an injection from
    `Fin n`. Re-typed counterpart of
    `Ethica.Pars1.hasAtLeastNAttributes`; the injection now lands in
    `Attr` rather than in `Thing`. No cardinal-arithmetic library is
    needed — `Fin n` and its core lemmas suffice, as in Pars I. -/
def hasAtLeastNAttrs (s : Thing) (n : Nat) : Prop :=
  ∃ f : Fin n → Attr, (∀ i, Attributum (f i) s) ∧ (∀ i j, f i = f j → i = j)

/-- `HasInfiniteAttrs s` : `s` has at least `n` distinct attributes
    for every `n` — Def. VI's "*infinitis attributis*" clause.

    In Pars I the corresponding `HasInfiniteAttributes` was stateable
    but provably unsatisfiable of any God
    (`def6_infinitis_attributis_unsatisfiable`). Here it is satisfied
    by an actual God — see `Models/InfiniteAttribute.lean`. -/
def HasInfiniteAttrs (s : Thing) : Prop :=
  ∀ n, hasAtLeastNAttrs (Attr := Attr) s n

/-- `hasMoreRealityThanAttr x y` : attribute-dominance, the Della
    Rocca constitutive reading of "more reality" (Pars I's
    `hasMoreRealityThan`, re-typed). -/
def hasMoreRealityThanAttr (x y : Thing) : Prop :=
  ∀ a : Attr, Attributum a y → Attributum a x

end definitions

end Ethica.Attributum
