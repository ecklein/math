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

## 2026-11-26 — session 1, continued

**Lean, done (axioms: propext, Classical.choice, Quot.sound):**
- Vendored Schoenfeld's Mathlib-only weighted Perron formula.
- `integral_vertical_eq`: a vertical line shift from Mathlib's rectangle theorem, self-contained.
- `norm_sum_vonMangoldt_char_le` (Theorem A), conditional on `GRHHyp`: (48e/π) log²N √N (π log(2+8q) + J), uniform in q and in χ ≠ 1.
- `massLower_le_mass`: elementary mass lower bound via `Chebyshev.psi_ge`, plus a non-unit prime-power bound.
- `bias_primeMeasure_le` (Theorem B, T1-formal), conditional.
- `MainTheorems/Conditional.lean` and `MainTheorems/Unconditional.lean`; the latter needs the GRH build.

**Finding.**
- The formal constants are poor: certifying bias 1/2 at q = 2⁶⁴ needs N ≈ 10¹⁶.
- The sharp T1(a) route would need about 8·10⁴. This motivates porting zeta-23-lean's explicit formula, or a sharper log-derivative argument, e.g. Hadamard three-circles in place of the 1/ε² loss.
- J = ∫ log(4+|t|)/(1+t²) ≈ 5.6262 (numerical); π(log 4 + 1/√2) ≈ 6.577 is an easy analytic upper bound, not yet formalized.

## 2026-11-26 — sharpening the constants

**Diagnosis.** The ≈10¹² loss in Theorem B came mostly from Borel–Carathéodory's 1/ε² (a log²N factor), which is intrinsic to the pointwise L'/L route. The fix is the explicit formula with positivity.

**Port.** zeta-23-lean's 120-module explicit-formula closure moved from Mathlib 51e6992e to 56a00585 with about 20 local fixes, across four rebuild rounds:
- the removed `linear_combination'` tactic file (vendored from old Mathlib);
- `fun_prop` and `Nat.floor` measurability;
- `field_simp` normal forms;
- `Finset.prod_le_prod` → `prod_le_prod₀` and `prod_le_one` → `prod_le_one₀`;
- `logDeriv_mul` / `logDeriv_prod` on pointwise lambdas (fold first);
- `positivity` behind `id`;
- `autoImplicit` for this library.

Every fix is marked `-- port (Mathlib 56a00585)`. A whole-environment axiom listing shows only Lean core axioms.

**New formal results.** All are conditional only on zeros-on-line and RH; axioms are the standard three.
- `Sharp.norm_primeSide_twist_le`: two-sided positivity.
- `Sharp.primeSideZeta_twist_eq`: main term from RH.
- `Sharp.GammaBounds`: explicit gamma sides, including a two-sided digamma bound.
- `Sharp.FiniteSums`.
- `Sharp.bias_sharp`.

**Result.** Certified support drops by about 10¹¹ (numerically evaluated constants). A closed-form Layer 2 is still to be formalized.

## 2026-11-26 — Layer 2: closed-form constants and a machine-checked certificate

- **Refactor.** Layer 1 now exports `sharp_charSum_mass` (numerator and mass bounds separately).
- **New modules.**
  - `Sharp/KernelBounds.lean`: grh-miller's decay lemma, vendored. The factorization A = F₊F₋ comes from `paperFT_weilTest` at ∓i/2, and loses only about 2% against the true A, versus 4.4× for a pointwise bound.
  - `Sharp/ConstBounds.lean`.
  - `Sharp/Certificate.lean`: `bias_closed`.
  - `Sharp/Certificate64.lean`: numerics from Mathlib's `exp_one_gt_d9`/`lt_d9`, `pi_gt_d6`/`lt_d6` and `log_two_lt_d9`.
- **Certificate numbers.** numB ≤ 236.6 and denB ≥ 555.8, so bias ≤ 0.4257.
- **Unconditional statements.** `GRHPseudo.Main.bias_sharp_closed` and `GRHPseudo.Main.bias_le_half_of_le_two_pow_64`, discharged by `LFunction_eq_zero_re` and `riemannHypothesis` from the compact edition.
- **Audit.** 23 audited theorems use the standard three axioms only; the environment has no axioms outside Lean core.
