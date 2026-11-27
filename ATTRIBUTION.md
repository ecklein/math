# Attribution

## Mathematical results
- RH and GRH for Dirichlet L-functions: Levent Alpöge, with Claude (https://alpo.ge/remark.pdf).
  We depend on the compact Lean edition, github.com/lsernau/grh-lean @ 72fead10 (Apache-2.0,
  Copyright 2026 Anthropic, PBC). We use it only through `LFunction_ne_zero_of_half_lt_re`.
- Classical inputs: Borel–Carathéodory; partial summation for Dirichlet series; the explicit
  formula and positivity method (Weil; Ankeny 1952; Bach 1990); Jao–Miller–Venkatesan (2009) for
  GRH-based expansion of prime Cayley graphs. See `research/literature_review.md`.

## Code adapted from other projects (all Apache-2.0)
| Our file | Source | Changes |
|---|---|---|
| `lean/GRHPseudo/AnalyticNumberTheory/LogDerivBound.lean` | AIOvernight/rh-prime-error, `RHPrimeError/LogDeriv.lean` (lemmas `borelCaratheodory_closedBall`, `norm_deriv_div_le_of_forall_mem_ball_ne_zero`) | namespace, imports |
| `lean/GRHPseudo/AnalyticNumberTheory/LGrowth.lean` | lsernau/grh-lean @ 72fead10, `grh/src/Lib/Analytic/PrimeNumberTheorem/LFunctionGrowth.lean` | namespace; main lemma specialised to χ ≠ 1 |
| `lean/GRHPseudo/AnalyticNumberTheory/LogDerivGRH.lean`, `norm_LSeries_le_two` | same file, `norm_LSeries_char_le` | generalised to coefficients of norm ≤ 1 |
| `lean/GRHPseudo/Vendor/Schoenfeld/{Perron,Kernel,Weighted}.lean` | AndrewVSutherland/schoenfeld-rh-lean @ 0e52d7b1, `SchoenfeldRH/Lemmas/p6/Perron.lean`, `Explicit/Kernel.lean`, `Explicit/Weighted.lean` | import paths only |
| `lean/GRHPseudo/AnalyticNumberTheory/PrimeCharSum.lean`, `integrable_log_mul_inv_one_add_sq` | amrehan/grh-miller v1.0.0, `GRHMiller/Ankeny.lean` | none |
| `lean/Zeta23/**` (120 modules) | anthropics/zeta-23-lean @ 16a5ce41, `zeta23/Zeta23/` | ported from Mathlib 51e6992e to 56a00585: ~20 local fixes, each marked `-- port (Mathlib 56a00585)`; `autoImplicit = true` for this library as upstream |
| `lean/Zeta23/FromPNTPlus/Tactic/LinearCombinationPrime.lean` | Mathlib @ 51e6992e, `Mathlib/Tactic/LinearCombinationPrime.lean` | removed from Mathlib before 56a00585; `module`/`public` markers dropped |
| `lean/GRHPseudo/Vendor/GRHMiller/{Hypothesis,Ankeny}.lean` | amrehan/grh-miller v1.0.0 (e3e573a) | import paths only |
