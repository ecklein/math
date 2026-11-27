# Paper: Explicit and formally verified spectral bounds for prime Cayley graphs on (Z/qZ)^×

Draft. Sources: `main.tex`, `sections/*.tex`, `references.bib`.

Build (BasicTeX / TeX Live 2026; only standard packages: amsart, lmodern, mathtools, booktabs, hyperref, xcolor):
```sh
pdflatex main && bibtex main && pdflatex main && pdflatex main
```
`latexmk -pdf main.tex` also works where latexmk is installed. The compiled `main.pdf` (15 pages) is
committed. The last build had no errors, no undefined references or citations, and no overfull boxes;
the only BibTeX warning is the missing pages of `cmqr2024`, which are not yet assigned.

Every formal claim names its Lean declaration. Statements are in
`../lean/GRHPseudo/MainTheorems/Unconditional.lean` and `../lean/GRHPseudo/AnalyticNumberTheory/Sharp/`.
Bibliography status: literature entries were checked against Crossref/arXiv. Not yet confirmed: the
volume and pages of `cmqr2024` (published online 2 Dec 2025, volume and pages not yet assigned). Krein's original
paper is not cited; the factorization theorem is cited via Boas–Kac (1945) and Ehm–Gneiting–Richards (2004).
