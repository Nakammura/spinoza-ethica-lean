/-
  Spinoza, *Ethica Ordine Geometrico Demonstrata*
  Pars I — De Deo
  Definitiones (Definitions)

  Public-domain sources used throughout this project:
    Latin   : The Latin Library (cltk/lat_text_latin_library, public domain)
    English : Elwes 1883 translation (en.wikisource, public domain)

  The Curley 1985 translation is consulted for interpretive cross-check
  but never copied — references only by section and footnote when
  diverging from Elwes is significant.

  -- Methodological note ----------------------------------------------
  Spinoza's geometric form fixes the *form* of demonstration; it does
  not by itself fix the *underlying logic*. Several formalisations are
  possible:
    (a) classical first-order with primitive predicates Substance/
        Attribute/Mode/etc. and explicit existence claims;
    (b) categorical / topos-theoretic, treating the universe of
        existents as objects in a closed monoidal category;
    (c) modal S5 with `□` for "necessary by virtue of essence" and
        explicit possible-world semantics for *causa sui* etc.

  We adopt (a) as the *base layer*: it is the most legible to readers
  trained in modern analytic philosophy and is what Curley, Garrett,
  and Della Rocca implicitly assume in their commentaries. The modal
  reformulation is implemented as the sibling file `ModalForm.lean`
  (the demote experiments of the irreducibility paper run on it); the
  categorical reformulation (`CategoryForm.lean`) is planned but not
  yet implemented — see `docs/coverage.md` for current status.
-/

namespace Ethica.Pars1

universe u

/-- The universe of `things` (`res`) over which Pars I quantifies.

    Spinoza's "id" / "ea res" / "quod" all refer to elements of this
    universe. We keep it as a `Type u` parameter to avoid baking in any
    cardinality assumption ("there is exactly one substance" is to be
    *proved* (Prop. XIV), not assumed). -/
class EthicaWorld (Thing : Type u) where
  /-- "in se est" : in itself.
      A thing is `inItself` iff it depends on no other thing for its
      conception. The two clauses of Def. III ("in se est" + "per se
      concipitur") are merged here because Spinoza uses them as a
      conjunction throughout the Demonstrationes; we recover the
      separation in `inItself_iff_perSeConceived` below. -/
  inItself : Thing → Prop

  /-- "per se concipitur" : conceived through itself.
      Defn-3 right conjunct, separated for tactic use. -/
  perSeConceived : Thing → Prop

  /-- "involvit existentiam" : involves existence.
      Used in Def. I and recurring in Props. VII, XI. -/
  involvesExistence : Thing → Prop

  /-- "natura non potest concipi nisi existens" : nature cannot be
      conceived except as existent. Def. I right conjunct. -/
  natureRequiresExistence : Thing → Prop

  /-- "in alio est" : exists in another. Def. V left conjunct. -/
  inAnother : Thing → Prop

  /-- "per quod etiam concipitur" : conceived through another.
      Def. V right conjunct. -/
  conceivedThroughAnother : Thing → Prop

  /-- "limitatur" : is limited (by another, of the same kind).
      Def. II — the relation `limitedBy x y` reads "x is limited by y". -/
  limitedBy : Thing → Thing → Prop

  /-- The intellect's apprehension that `a` constitutes the essence of
      `s`. Def. IV: "id quod intellectus de substantia percipit
      tanquam ejusdem essentiam constituens". -/
  intellectPerceivesAsEssence : Thing → Thing → Prop

  /-- "absolute infinitum" : absolutely infinite, in the sense of
      Def. VI ("infinitum simpliciter"). Distinguished from "infinitum
      in suo genere". -/
  absolutelyInfinite : Thing → Prop

  /-- "expressing reality" / "exprimens essentiam aeternam et
      infinitam". Used in Def. VI explanation. -/
  expressesEternalEssence : Thing → Prop

  /-- "liberum" : free in Def. VII's strict sense — exists from the
      necessity of its own nature alone. -/
  freelyExistent : Thing → Prop

  /-- "coactum" : constrained — determined by another to exist or act
      in a fixed way. Def. VII right disjunct (the contrast term). -/
  constrained : Thing → Prop

  /-- "aeternitas" : eternity (Def. VIII), as the "very existence which
      follows necessarily from the definition of an eternal thing". -/
  eternal : Thing → Prop


variable {Thing : Type u} [EthicaWorld Thing]
open EthicaWorld

/-! ## Definition I — *Causa sui*

  Latin: *Per causam sui intelligo id cujus essentia involvit
         existentiam, sive id cujus natura non potest concipi nisi
         existens.*

  Elwes EN: "By that which is *self-caused*, I mean that of which the
            essence involves existence, or that of which the nature is
            only conceivable as existent."

  Curley 1985 differs only stylistically. The disjunction `sive` is
  best read as identifying two equivalent formulations rather than
  introducing a second class — both clauses pick out the same things.
-/

/-- A thing `x` is *causa sui* iff its essence involves existence.

    Spinoza's "sive" between the two clauses of Def. I is read here
    as "id est" (Curley 1985 p. 408): the second clause re-expresses
    the first. We define `causaSui` via the first clause only and
    recover the second via `Pars1Axioms.ax_causaSui_iff` (A11) when
    needed. Defining it via the first clause alone avoids mixing
    definitional conjunction with material biconditional. -/
def causaSui (x : Thing) : Prop :=
  involvesExistence x

/-! ## Definition III — *Substantia*

  Latin: *Per substantiam intelligo id quod in se est et per se
         concipitur, hoc est id cujus conceptus non indiget conceptu
         alterius rei a quo formari debeat.*

  Note on textual order: Spinoza presents Def. II (`finitum in suo
  genere`) before Def. III. We retain his ordering in the source
  comments but place the Lean definitions in *logical* order —
  `Substance` and `Attribute` first, then `sameNature` (derived from
  `Attribute`, per Della Rocca's reading; closes GAP-2), then
  `finitumInSuoGenere` which depends on `sameNature`. -/

/-- `Substance x` : `x` is in itself and conceived through itself. -/
def Substance (x : Thing) : Prop :=
  inItself x ∧ perSeConceived x

/-! ## Definition IV — *Attributum*

  Latin: *Per attributum intelligo id quod intellectus de substantia
         percipit tanquam ejusdem essentiam constituens.*

  We model attributes as relations between things and substances —
  `Attribute a s` reads "a is an attribute of substance s". Spinoza
  treats attributes as themselves things (Prop. X scholium), so they
  inhabit the same universe `Thing`. -/

/-- `Attribute a s` : the intellect perceives `a` as constituting the
    essence of substance `s`. -/
def Attribute (a s : Thing) : Prop :=
  Substance s ∧ intellectPerceivesAsEssence s a

/-! ## *Sameness of nature* (derived; closes GAP-2)

  Della Rocca (*Spinoza* 2008, ch. 2): "same nature" is *constituted*
  by sharing an attribute, not a further primitive relation. We
  adopt that reading: `sameNature x y` ≝ `∃ a, Attribute a x ∧
  Attribute a y`. The bridge from Prop. II's "different attributes"
  hypothesis to "no shared nature" thus becomes analytic. -/

/-- `sameNature x y` : `x` and `y` share at least one attribute.
    Note this implicitly requires both `x` and `y` to be substances
    (since `Attribute a _` carries `Substance _`). For inter-mode
    or mode-vs-substance "same kind" comparisons (Def. II's bodily
    examples), a separate `hasAttribute` relation will be added at
    the modal layer. -/
def sameNature (x y : Thing) : Prop :=
  ∃ a, Attribute a x ∧ Attribute a y

/-! ## Definition II — *Finitum in suo genere*

  Latin: *Ea res dicitur in suo genere finita quae ab alia ejusdem
         naturae terminari potest…*

  Defined here (after `sameNature`) for elaboration order; reads as
  in Spinoza. -/

/-- Finite-after-its-kind : capable of being limited by *another*
    thing of the same nature.

    The `x ≠ y` clause encodes Spinoza's "ab **alia** ejusdem
    naturae" (Def. II: "*by another* of the same nature"). The
    pre-Prop.-VIII draft omitted this clause; it is required for
    the demonstration of Prop. VIII to go through, since A12
    collapses any pair of same-nature substances to identity. -/
def finitumInSuoGenere (x : Thing) : Prop :=
  ∃ y, x ≠ y ∧ sameNature x y ∧ limitedBy x y

/-! ## Definition V — *Modus*

  Latin: *Per modum intelligo substantiae affectiones, sive id quod in
         alio est, per quod etiam concipitur.*
-/

/-- `Mode x` : exists in another and is conceived through another.
    Equivalent to "an affection of substance" via Prop. XIV (after
    we prove there is only one substance). -/
def Mode (x : Thing) : Prop :=
  inAnother x ∧ conceivedThroughAnother x

/-! ## Definition VI — *Deus*

  Latin: *Per Deum intelligo ens absolute infinitum, hoc est
         substantiam constantem infinitis attributis, quorum
         unumquodque aeternam et infinitam essentiam exprimit.*

  This is the structural keystone of Pars I. We do *not* assert God's
  existence here — that is the content of Prop. XI. We only define
  what "God" *means*. -/

/-- `IsGod g` : `g` is a substance that is absolutely infinite, has
    *at least one* attribute, and every attribute it has expresses
    eternal and infinite essence.

    The `∃ a, Attribute a g` clause is required: a bare `∀` would be
    vacuously satisfiable by an attribute-free entity. This still
    falls short of Spinoza's "constantem *infinitis* attributis":
    encoding the infinite-cardinality claim requires a counting
    framework not yet introduced. Tracked as GAP-8. -/
def IsGod (g : Thing) : Prop :=
  Substance g
  ∧ absolutelyInfinite g
  ∧ (∃ a, Attribute a g)
  ∧ (∀ a, Attribute a g → expressesEternalEssence a)

/-! ## Definition VII — *Liberum / Coactum*

  Latin: *Ea res libera dicetur quae ex sola suae naturae necessitate
         existit et a se sola ad agendum determinatur. Necessaria
         autem, vel potius coacta, quae ab alio determinatur ad
         existendum et operandum certa ac determinata ratione.* -/

/-- A thing is *free* in Spinoza's strict sense iff it exists from the
    necessity of its own nature and is determined to act by itself
    alone.

    Currently a thin alias over the `freelyExistent` primitive; the
    second clause of Def. VII ("ad agendum determinatur") requires
    action machinery introduced only in Pars II, so the present
    encoding captures only the existence-clause. Tracked as GAP-9. -/
def Free (x : Thing) : Prop := freelyExistent x

/-- A thing is *constrained* iff some other thing determines it.
    Same caveat as `Free`: thin alias pending Pars II. GAP-9. -/
def Constrained (x : Thing) : Prop := constrained x

/-! ## Definition VIII — *Aeternitas*

  Latin: *Per aeternitatem intelligo ipsam existentiam, quatenus ex
         sola rei aeternae definitione necessario sequi concipitur.* -/

/-- A thing is *eternal* iff its existence follows necessarily from
    its definition alone. We treat `eternal` as primitive at this
    layer; a fuller modal reconstruction is developed in the sibling
    `ModalForm.lean`. -/
def Eternal (x : Thing) : Prop := eternal x

end Ethica.Pars1
