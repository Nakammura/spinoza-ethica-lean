#!/usr/bin/env bash
# Build cluster_a.pdf from the section markdown files.
#
# Requirements:
#   - pandoc (brew install pandoc)
#   - tectonic (brew install tectonic)

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PAPER_DIR="$(cd "$SCRIPT_DIR/.." && pwd)"
cd "$SCRIPT_DIR"

# (1) Concatenate front matter + 9 sections + references into body.md
{
  cat <<'YAML'
---
title: |
  Bennett's Conjecture in Lean 4: Counter-Models for the PSR-Reducibility of Spinoza's Propositions V and XIV
author:
  - Yuki Nakamura
date: \today
abstract: |
YAML
  # Indent abstract.md by two spaces for YAML block scalar
  sed -e 's/^# Abstract$//' -e '/^$/d' -e 's/^/  /' "$PAPER_DIR/abstract.md"
  printf -- '---\n'

  for f in 01_introduction.md 02_debate.md 03_formalisation.md 04_methodology.md \
           05_a12_result.md 06_a15_result.md 07_typology.md 08_scope.md 09_conclusion.md; do
    printf '\n\n'
    cat "$PAPER_DIR/$f"
  done

  printf '\n\n# References\n\n'
  # Manually-formatted Chicago author-date references (one paragraph per entry).
  # references.md is the canonical source; this is the prose-rendered form.
  cat <<'REFS'
Bennett, Jonathan. 1984. *A Study of Spinoza's Ethics*. Indianapolis: Hackett.

Curley, Edwin, ed. and trans. 1985. *The Collected Works of Spinoza*. Vol. 1. Princeton: Princeton University Press.

de Moura, Leonardo, and Sebastian Ullrich. 2021. "The Lean 4 Theorem Prover and Programming Language." In *Automated Deduction — CADE 28*, edited by André Platzer and Geoff Sutcliffe, 625–635. Lecture Notes in Computer Science 12699. Cham: Springer.

Della Rocca, Michael. 2002. "Spinoza's Substance Monism." In *Spinoza: Metaphysical Themes*, edited by Olli Koistinen and John Biro, 11–37. New York: Oxford University Press.

Della Rocca, Michael. 2008. *Spinoza*. Routledge Philosophers. London: Routledge.

Elwes, R. H. M., trans. 1883. *The Chief Works of Benedict de Spinoza*. Vol. 2. London: George Bell and Sons.

Garrett, Don. 1990. "Ethics IP5: Shared Attributes and the Basis of Spinoza's Monism." In *Central Themes in Early Modern Philosophy: Essays Presented to Jonathan Bennett*, edited by J. A. Cover and Mark Kulstad, 69–107. Indianapolis: Hackett.

Garrett, Don. 2018. *Nature and Necessity in Spinoza's Philosophy*. New York: Oxford University Press.

Spinoza, Benedictus de. 1677. *Ethica Ordine Geometrico Demonstrata*. In *B. d. S. Opera Posthuma*, edited by Jarig Jelles. Amsterdam: Jan Rieuwertsz.

Werner, Benjamin. 1997. "Sets in Types, Types in Sets." In *Theoretical Aspects of Computer Software (TACS '97)*, edited by Martín Abadi and Takayasu Ito, 530–546. Lecture Notes in Computer Science 1281. Berlin: Springer.
REFS
} > body.md

# (2) pandoc → LaTeX
pandoc body.md \
  -t latex \
  --standalone \
  --include-in-header=header.tex \
  --variable=documentclass=article \
  --variable=papersize=letter \
  --variable=fontsize=11pt \
  --columns=200 \
  -o cluster_a.tex

# (3) Patch the generated .tex:
#  (a) prepend the engine marker so arXiv auto-detects xelatex;
#  (b) inject the affiliation under the author line (pandoc's YAML
#      escaping converts \\ to \textbackslash, so we fix it here).
# `sed -i.bak` is portable across BSD (macOS) and GNU (Linux); we drop
# the .bak file immediately afterwards.
{ printf '%% !TEX TS-program = xelatex\n'; cat cluster_a.tex; } > cluster_a.tex.new \
  && mv cluster_a.tex.new cluster_a.tex
sed -i.bak \
  -e 's|\\author{Yuki Nakamura}|\\author{Yuki Nakamura\\\\The Open University of Japan}|' \
  -e 's|pdfauthor={Yuki Nakamura}|pdfauthor={Yuki Nakamura, The Open University of Japan}|' \
  cluster_a.tex
rm -f cluster_a.tex.bak

# (4) tectonic → PDF
tectonic cluster_a.tex

echo
echo "Built: $SCRIPT_DIR/cluster_a.pdf"
