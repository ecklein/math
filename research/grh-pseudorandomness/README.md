# GRH-based pseudorandomness over (Z/qZ)^×

Explicit, formally verified spectral bounds for prime Cayley graphs on `G_q = (Z/qZ)^×`. They build
on the Lean proof of GRH for Dirichlet L-functions (Alpöge, with Claude). The paper is in
[`paper/main.pdf`](paper/main.pdf).

**Status (2026-11-27).** All results below are proved in Lean, unconditionally: the GRH and RH
hypotheses are discharged by the GRH proof. Audited axioms: `propext`, `Classical.choice`,
`Quot.sound` only. The paper draft is complete, compiles, and is not yet submitted.

## Results (numbering as in the paper)

| Paper | Lean | Statement |
|---|---|---|
| Thm 2 | `GRHPseudo.Main.primeCharSum` | for every q ≥ 1, χ ≠ χ₀ mod q, N ≥ 3: ‖Σ_{0<n<N} χ(n)Λ(n)(1 − n/N)‖ ≤ (48e/π) log²N √N (π log(2+8q) + J) |
| Cor 3 | `GRHPseudo.Main.bias_primeMeasure` | explicit bias bound for the weights Λ(n)(1 − n/N) on units mod q |
| Thm 4 | `GRHPseudo.Sharp.bias_sharp` | sharp bound from the explicit formula plus positivity (cosh kernel): bias ≤ Num/Den |
| Thm 6 | `GRHPseudo.Main.bias_sharp_closed` | the same, with Num/Den in elementary closed form, for all q, a ≥ 1, y > 2a |
| Cor 7 | `GRHPseudo.Main.bias_le_half_of_le_two_pow_64` | for every q ≤ 2⁶⁴ and χ ≠ χ₀: a fixed measure on prime powers n ≤ 166253 has bias ≤ 1/2 |
| Prop 8 | core: `GRHPseudo.inner_mul_inner_le` | cosh(t/2) is the optimal *positive-definite* kernel, c* = 2/a*² ≈ 1.2236 (L² instance informal) |
| Cor 9 | informal | limit of the method: every kernel has leading constant c ≥ 1 (Prop 15); convolution squares (Prop 14) reach 1 + δ |
| Thm 10 | `GRHPseudo.Main.bias_convSq_closed` | closed-form bias bound for the convolution-square kernel K_A = f_A ⋆ f_A (window [x e^{−2A}, x]), all q, A ≥ 1/32, R > 0, y > 2A |
| Cor 11 | `GRHPseudo.Main.bias_le_half_of_le_two_pow_64_convSq` | for every q ≤ 2⁶⁴ and χ ≠ χ₀: a fixed measure on prime powers n ≤ 48400 has bias ≤ 1/2 (3.4× smaller support than Cor 7) |

**Correction (2026-11-27).** Earlier versions said the cosh kernel is optimal "within the positivity method".
That was wrong: convolution squares f ⋆ f use the same positivity step and do better. See Section 6 of the paper.

Novelty is modest. Prior work and how these results relate to it are discussed in
[`notes/novelty_assessment.md`](notes/novelty_assessment.md) and in Section 3 of the paper. In particular,
the leading term of Theorem 4 is, asymptotically, Lemma 6.1 of Lamzouri–Li–Soundararajan (2015).

## Layout
- [`paper/`](paper/) — LaTeX source (`main.tex`, `sections/`, `references.bib`) and the compiled `main.pdf`.
- [`lean/`](lean/) — Lean 4 project `GRHPseudo` (Lean v4.35.0, Mathlib `56a00585`).
  - `GRHPseudo/GRH/` — hypothesis interface and its discharge by the GRH proof.
  - `GRHPseudo/AnalyticNumberTheory/` — Borel–Carathéodory route (Thm 2) and `Sharp/` (Thms 4, 6, 10; Cors 7, 11).
  - `GRHPseudo/Pseudorandomness/` — bias, Cayley eigenvalues, rank-two inequality, Cor 3.
  - `GRHPseudo/MainTheorems/` — conditional and unconditional statements.
  - `GRHPseudo/Vendor/` — adapted code (see [`ATTRIBUTION.md`](ATTRIBUTION.md)).
  - `Zeta23/` — the Weil explicit formula library (zeta-23-lean), ported to our Mathlib pin.
- [`experiments/`](experiments/) — exact bias computations (FFT over discrete logs) and constant evaluations.
- [`verification/`](verification/) — dependency fetch script, axiom audits, kernel replay logs, port diff.
- [`notes/`](notes/) — research notes: GRH audit, literature review, candidates, novelty assessment,
  proof obligations, failed approaches, research log.
- `vendor/` (git-ignored) — pinned checkout of grh-lean, created by `verification/fetch_deps.sh`.

## Reproduce
Run from this directory (`research/grh-pseudorandomness/`):
```sh
verification/fetch_deps.sh                                              # clones grh-lean @ 72fead10
(cd vendor/grh-lean/grh-compact && lake exe cache get && lake build)    # 1–2 h, ~24 GB RAM
(cd lean && lake build GRHPseudo GRHPseudo.MainTheorems.Unconditional)
(cd lean && lake env lean ../verification/Axioms.lean)                  # axiom audit
python3 -m venv .venv && .venv/bin/pip install numpy sympy scipy
.venv/bin/python experiments/prime_bias.py --qs 10007 100003
(cd paper && pdflatex main && bibtex main && pdflatex main && pdflatex main)
```

## Trust
The unconditional theorems inherit the trust base of the Lean GRH proof (compact edition, see
[`notes/grh_audit.md`](notes/grh_audit.md)). GRH enters only through `GRHPseudo.grh` and
`GRHPseudo.Main.zerosOnLine`; everything else is proved from explicit hypotheses.
