# Spinoza's *Ethica* in Lean 4

[![arXiv](https://img.shields.io/badge/arXiv-2605.02331-b31b1b.svg)](https://arxiv.org/abs/2605.02331)
[![DOI](https://zenodo.org/badge/1227587615.svg)](https://doi.org/10.5281/zenodo.20111520)

> Pars I (De Deo) is mechanised through the load-bearing
> propositions of the substance / attribute / God arc
> (Propositions II, IV, V, VI, VII, X, XIV) and re-derived in a
> modal-S5 layer. Two kernel-level irreducibility results
> establish that axioms A12 (Proposition V's
> identity-from-shared-attribute clause) and A15 (Proposition
> XIV's universality clause) cannot be derived from stated
> axioms plus a Della-Rocca-flavoured PSR augmentation. Per-
> proposition status is tracked in `docs/coverage.md`.
>
> Project lead: Yuki Nakamura.

## What this is

A formal-verification port of Baruch Spinoza's *Ethica Ordine
Geometrico Demonstrata* (1677) into the Lean 4 theorem prover.

Spinoza wrote the *Ethica* "more geometrico" — in the form of
Euclid's *Elements*, with definitions, axioms, propositions, and
demonstrations. He intended his metaphysics to be checked the way
a geometer checks a construction. This repository executes that
intention against a modern dependent-type-theory kernel.

## Texts

Public-domain sources only:

- *Latin*: Spinoza, *Ethica*, from the cltk public-domain corpus.
- *English*: R. H. M. Elwes 1883 translation, via Project
  Gutenberg / en.wikisource.

The Curley 1985 Princeton translation is consulted as
interpretive cross-check; no Curley text is reproduced in source
or comments.

## Organisation

```
Ethica.lean                                -- Top-level umbrella
Ethica/
└── Pars1/
    ├── Definitions.lean                  -- Defs I–VIII + EthicaWorld class
    ├── Axioms.lean                       -- A1–A7 + auxiliary axioms (Section I/II/III)
    ├── Causation.lean                    -- Cause predicate, A3 / A4 substantive
    ├── Propositions.lean                 -- Props I–XIV with full proofs
    ├── ModalForm.lean                    -- S5 modal re-derivation
    └── Models/
        ├── SingleSubstance.lean          -- Unit-instance consistency witness
        ├── TwoSubstance.lean             -- Bennett-line falsifier bench
        ├── MultiWorld.lean               -- Bridge-axiom witness (modal layer)
        └── Counterexamples.lean          -- Kernel-level non-derivation witnesses
texts/
├── ethica1_la.txt … ethica5_la.txt       -- Latin per Pars
└── en_part1_elwes.txt … en_part5_elwes.txt   -- Elwes EN per Pars
docs/
├── gaps.md                               -- GAP-N catalogue
├── coverage.md                           -- Per-proposition status
└── auxiliary_axioms.md                   -- Section I/II/III register
papers/
└── cluster_a_irreducibility/             -- Bennett–Della Rocca paper
```

## Build

Lean 4.13.0 is pinned in `lean-toolchain`. No Mathlib dependency.

```bash
brew install elan-init
cd spinoza-ethica-lean
lake build
```

## Methodology summary

### Three layers

The base layer is classical first-order with primitive predicates
over a `Thing` universe. The modal layer adds S5 with `□` for
"necessary by virtue of essence" and re-derives the same
propositions through Kripke-frame machinery. A categorical layer
(topos / monoidal-closed-category formulation) is planned.

### Section sub-categorisation of auxiliary axioms

Beyond Spinoza's stated A1–A7, the Pars I formalisation requires
auxiliary axioms grouped into three sections:

- **Section I** — definitional bridges making explicit the
  ontological/conceptual co-extensions Spinoza uses without
  comment.
- **Section II** — substantive promotions of stated content into
  forms the kernel can use (e.g. excluded middle on `inItself`,
  bridges between `Cause` and `intelligibleThrough`).
- **Section III** — metaphysical commitments needed to fill gaps
  in Spinoza's *demonstrationes*, partitioned further into base
  axioms (§III.A), demote candidates (§III.B), and modal-layer
  promotions (§III.C).

The sub-categorisation makes commitment cost visible to readers
and supports the demote-experiment methodology described next.

### Demote experiments

For each Section III axiom A, the formalisation can be queried:
*does some weaker commitment Σ derive A from the base layer?*
The procedure declares Σ as a typeclass extending `EthicaWorld`,
attempts a direct proof of A from Σ-augmented base, and on
failure constructs a counter-model in `Models/Counterexamples.lean`
falsifying A while satisfying all of `EthicaWorld + Σ`. The
non-derivation argument runs at kernel level: any Lean derivation
of A from Σ would specialise to the model, contradicting the
constructed falsification.

Outcome patterns observed across Pars I's four demotable Section
III axioms (A12, A13, A14, A15):

| Axiom | Demote Σ | Outcome |
|-------|----------|---------|
| A12 | `PSRSubstance` | Partial reduction; full irreducible |
| A13 | `PSRSelfCause` modulo bridge A18 | Equal-strength translation |
| A14 | `PSREssencePerception` | Trivial redescription |
| A15 | `PSRPlenitude` (plenitude + uniqueness) | Decomposition only |

Universality clauses (A12, A15) resist Della-Rocca-flavoured
PSR-driven reduction; existence clauses (A13, A14) translate at
equal strength. The structural distinction is not made explicit
by the prose commentary on Spinoza and is the subject of the
companion paper.

### Gap policy

Each `sorry` carries a `-- GAP-N` comment and an entry in
[`docs/gaps.md`](docs/gaps.md) recording the philosophical reason
and resolution path. Discharge happens in a dedicated commit that
updates `gaps.md` in the same change. Silent `sorry` is forbidden.

## Companion paper

The `papers/cluster_a_irreducibility/` directory contains a
research paper situating the formalisation in the
Bennett–Della-Rocca debate over Spinoza's Proposition V. The
paper provides the first machine-checked evidence in the debate,
encoding Bennett's reading of Spinoza's stated axioms as a
typeclass and Della-Rocca's substantive PSR as an extension class,
and establishing kernel-level non-derivability through
counter-models for A12 and A15.

## License

Code: MIT. Public-domain texts retain their PD status.

## Citation

**Paper** (arXiv:2605.02331):

```
Nakamura, Y. (2026). Bennett's Conjecture in Lean 4:
Counter-Models for the PSR-Reducibility of Spinoza's
Propositions V and XIV. arXiv:2605.02331.
https://arxiv.org/abs/2605.02331
```

**Software** (Zenodo, this repository):

```
Nakamura, Y. (2026). spinoza-ethica-lean (v1.0.0) [Software].
Zenodo. https://doi.org/10.5281/zenodo.20111521
```

**ORCID**: [0009-0001-7174-6737](https://orcid.org/0009-0001-7174-6737)
