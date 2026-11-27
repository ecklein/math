# Paper: Explicit and formally verified spectral bounds for prime Cayley graphs on (Z/qZ)^×

Draft. Sources: `main.tex`, `sections/*.tex`, `references.bib`.

Build (any of):
```sh
latexmk -pdf main.tex
tectonic main.tex
pdflatex main && bibtex main && pdflatex main && pdflatex main
```

Not yet compiled: no TeX engine was available in the drafting environment. The source passed static
checks: balanced environments, braces and `$`; every `\ref` has a `\label`; every `\cite` key is in
`references.bib`. A first compile may still surface small issues.

Every formal claim names its Lean declaration. Statements are in
`../lean/GRHPseudo/MainTheorems/Unconditional.lean` and `../lean/GRHPseudo/AnalyticNumberTheory/Sharp/`.
Bibliography status: literature entries were checked against Crossref/arXiv. Not yet confirmed: the
volume and pages of `cmqr2024` (published online 2 Dec 2025, volume and pages not yet assigned). Krein's original
paper is not cited; the factorization theorem is cited via Boas–Kac (1945) and Ehm–Gneiting–Richards (2004).
