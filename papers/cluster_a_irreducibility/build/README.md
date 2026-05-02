# Build directory

Reproducible build for the paper PDF.

## Run

```bash
./build.sh
```

Produces `cluster_a.pdf` (33 pages, ~146 KB) from the section
markdown files in the parent directory.

## Files

- `build.sh` — concatenates abstract + 9 sections + references
  into a single markdown document, runs pandoc to LaTeX, then
  tectonic to PDF.
- `header.tex` — LaTeX preamble injected by pandoc. Provides
  `newunicodechar` substitutions for the Unicode glyphs used in
  Lean code blocks (∀ ∃ ¬ ∧ ∨ → ↔ subscripts ₁ ₂ ₐ ₑ ₛ Σ φ ⟨ ⟩
  etc.) and `fancyvrb` settings for code-block framing.
- `cluster_a.bib` — BibTeX entries for the 12 references, kept
  alongside the prose-style bibliography in `build.sh` in case a
  later stage switches to `pandoc --citeproc`.
- `.gitignore` — ignores generated artefacts (`body.md`,
  `cluster_a.tex`, `cluster_a.pdf`, LaTeX auxiliaries).

## Requirements

- pandoc ≥ 3.0 (`brew install pandoc`)
- tectonic ≥ 0.15 (`brew install tectonic`)

## arXiv submission

For arXiv upload, package `cluster_a.tex` together with the
`fonts/` directory into a tar.gz; arXiv's xelatex build will
produce the PDF server-side. Confirm locally first by running
`./build.sh`.
