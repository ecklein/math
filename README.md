# GRH-based pseudorandomness over (Z/qZ)^×

Research project: explicit, formally verified pseudorandomness guarantees for prime-supported
distributions on `G_q = (Z/qZ)^×`, building on the Lean proof of GRH for Dirichlet L-functions
(Alpöge, with Claude). **Status: early; no paper claims yet.**

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
cd lean && lake build GRHPseudo GRHPseudo.AnalyticNumberTheory.LogDerivGRH
lake env lean ../verification/Axioms.lean
python3 -m venv .venv && .venv/bin/pip install numpy sympy
.venv/bin/python experiments/prime_bias.py --qs 10007 100003
```

## Trust
Conditional results take `hGRH : GRHHyp` as a hypothesis. Unconditional versions are obtained only
through `GRHPseudo.grh := LFunction_ne_zero_of_half_lt_re` from the compact edition, and inherit
its trust base (see `research/grh_audit.md`). Adapted code is listed in `ATTRIBUTION.md`.
