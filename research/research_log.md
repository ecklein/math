# Research log

## 2026-11-26 — session 1

**Environment.**
- Installed elan 4.4.0 and Lean v4.35.0 (`eb6cafb7`, matches the pin).
- Cloned grh-lean @ `72fead10` and started a `lake build` of `grh-compact` (log: `vendor/grh-compact-build.log`).
- Created `lean/` with a path dependency on the compact edition. All ten package revisions match the compact edition's manifest exactly.

**Audit.**
- The GRH interface states zero location only (`research/grh_audit.md`).
- No explicit prime/character-sum bound ships with it.

**Literature.**
- See `literature_review.md`. Key findings:
  - JMV is the closest result and has non-explicit constants.
  - SLP squareness (Gaillard–Jindal) is already known under GRH.
  - grh-miller formalizes Bach's constant 2 (one-sided), on the 4.33 toolchain line.
  - zeta-23-lean has the Weil explicit formula (Lean v4.33.0-rc2 / Mathlib `51e6992e`; closure 120 modules / 43k lines).
  - rh-prime-error, schoenfeld-rh-lean and PNT+ `a4fb6989` are all on our exact pin and provide Borel–Carathéodory glue, Perron and contour shift.
- Possible overlap to resolve: rh-prime-error's README cites jonhanke/analytic-number-theory-lean as formalizing a GRH bound in arithmetic progressions. The repository returns 404 (private or removed), so this is **unverified**. It is relevant to the novelty of T1-formal, though not of T1(b). Alpöge's archive reportedly has `riemann_hypothesis_of_power_bound` (a smoothed converse), which bears on T2.

**Experiments.**
- `prime_bias.py`: for typical prime q ≤ 10⁶ primes are as good as random multisets.
- `adversarial_q.py`: on record least-QNR moduli the max over characters is still a generic character.
- `cosh_kernel_check.py`: the T1(a) bound holds in 36/36 cases with ratio 0.50–0.74. The check exposed an error in the small-prime term (it is ≈ e^a, not 2a), now corrected.

**Candidates.**
- See `conjectures.md`.
- Selected T1: an explicit two-sided spectral bound, plus optimality of the cosh kernel within the positivity method.
- First formal target: T1-formal via Borel–Carathéodory, on the pin.

**Lean, done (axioms: propext, Classical.choice, Quot.sound; no sorry):**
- `norm_LFunction_le_linear` (A1).
- `one_half_le_norm_LFunction` (A2).
- `norm_logDeriv_LFunction_le` (A3, conditional on `GRHHyp`).
- `inner_mul_inner_le` (rank-two inequality behind T1(b)).
- `charSum_eq_eigenvalue` and `bias_le_of_bounds`.

**Next.**
- A4 (vendor Schoenfeld's `perron_weighted_mu`), A5 (line shift to Re s = 1/2 + 1/log N), A6 (main term).
- Then the bias theorem and its unconditional form via `GRHPseudo.grh` once the GRH build finishes.
- T1(b) concrete L² instance and its equality case.
- Resolve the Hanke-repository overlap question.
