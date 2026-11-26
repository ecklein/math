# GRH-based pseudorandomness over (Z/qZ)^×

Research project: explicit, formally verified pseudorandomness guarantees for prime-supported
distributions on `G_q = (Z/qZ)^×`, building on the Lean proof of GRH for Dirichlet L-functions
(Alpöge, with Claude). **Status:** Theorems A and B below are proved in Lean, unconditionally, via the GRH proof.
The sharp-constant result T1(a)/(b) and the paper are in progress.

## Formally verified results (`lean/GRHPseudo/MainTheorems/Unconditional.lean`)
- **Theorem A** `GRHPseudo.Main.primeCharSum`: for every q ≥ 1, every nonprincipal Dirichlet
  character χ mod q, and every N ≥ 3,
  `‖Σ_{0<n<N} χ(n)Λ(n)(1 − n/N)‖ ≤ (48e/π) log²N √N (π log(2+8q) + J)`, `J ≈ 5.626`.
- **Theorem B** `GRHPseudo.Main.bias_primeMeasure`: the sample space {n < N coprime to q} with
  weights Λ(n)(1 − n/N) has bias ≤ `charSumBound q N / massLower q N` against every
  nonprincipal χ mod q. That is an explicit bound on every nontrivial eigenvalue of the weighted
  prime-power Cayley graph on (Z/qZ)^×.

Axioms: `propext, Classical.choice, Quot.sound` only (`verification/axioms.log`). The constants are
weak: certifying bias 1/2 at q = 2⁶⁴ needs N ≈ 10¹⁶ (`experiments/formal_bound_params.py`).

## Layout
- `research/` — audit (`grh_audit.md`), literature review, candidates (`conjectures.md`),
  novelty assessment, proof obligations, failed approaches, research log.
- `lean/` — Lean 4 project `GRHPseudo` (Lean v4.35.0, Mathlib `56a00585`, path dependency on
  grh-lean @ `72fead10`, compact edition).
  - `GRHPseudo/GRH/` — interface (`GRHHyp` = the GRH project's `DirichletLNonvanishingRightOfHalf`)
    and the discharge module (`GRHPseudo.grh`, needs the full GRH build).
  - `GRHPseudo/AnalyticNumberTheory/` — growth of L, Borel–Carathéodory, log-derivative bound.
  - `GRHPseudo/Pseudorandomness/` — bias, Cayley eigenvalue identity, rank-two extremal inequality.
- `experiments/` — exact bias computations via FFT over the discrete-log isomorphism.
- `verification/` — dependency fetch script, axiom audits.
- `paper/` — (not started).

## Reproduce
```sh
verification/fetch_deps.sh
(cd vendor/grh-lean/grh-compact && lake exe cache get && lake build)   # 1–2 h, 24 GB RAM
cd lean && lake build GRHPseudo GRHPseudo.MainTheorems.Unconditional
lake env lean ../verification/Axioms.lean
python3 -m venv .venv && .venv/bin/pip install numpy sympy
.venv/bin/python experiments/prime_bias.py --qs 10007 100003
```

## Trust
Conditional results take `hGRH : GRHHyp` as a hypothesis. Unconditional versions are obtained only
through `GRHPseudo.grh := LFunction_ne_zero_of_half_lt_re` from the compact edition, and inherit
its trust base (see `research/grh_audit.md`). Adapted code is listed in `ATTRIBUTION.md`.
