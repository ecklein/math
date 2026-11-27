# CLAUDE.md — grh-pseudorandomness

Project state and working notes. The general process is in `../../CLAUDE.md`. **Update this file
whenever results, statements, commands, status or open tasks change.** Last updated: 2026-11-27
(second external review: certified separation at L = 4, five more fixes; branch `grh-review-2`).

## What this project is
Explicit, formally verified bias bounds (equivalently, second-eigenvalue bounds) for prime Cayley graphs
on `(ℤ/qℤ)^×`, made unconditional by the Lean proof of GRH for Dirichlet L-functions. Results and layout
are in `README.md`; the paper is in `paper/main.pdf`.

## Pins and dependency
- Lean v4.35.0 (`eb6cafb7`), Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`.
- GRH proof: `github.com/lsernau/grh-lean` @ `72fead102f663d5c7a407964a13dc0cf9d977207`, compact edition,
  at `vendor/grh-lean/grh-compact`. It is a path dependency in `lean/lakefile.toml`, fetched by
  `verification/fetch_deps.sh`. Its build takes about 1 h 46 min. Note: `vendor/ext/` holds reference
  clones (zeta-23-lean, grh-miller) and is not a build dependency.
- GRH enters **only** through two declarations:
  - `GRHPseudo.grh := LFunction_ne_zero_of_half_lt_re` (in `GRH/Discharge.lean`);
  - `GRHPseudo.Main.zerosOnLine := LFunction_eq_zero_re`, used with `riemannHypothesis`.
- The dependency proves zero location only. It is not GRH for Hecke L-functions, so the JMV class-group
  expanders stay conditional.

## Module map (`lean/`)
| Module | Role |
|---|---|
| `GRHPseudo/GRH/{Interface,Discharge}` | hypothesis `GRHHyp`; discharge |
| `AnalyticNumberTheory/{LGrowth,LogDerivBound,LogDerivGRH,Contour,PrimeCharSum}` | Borel–Carathéodory route; paper Thm 2 |
| `AnalyticNumberTheory/Sharp/{Twist,TwoSided,MainTerm,GammaBounds,FiniteSums,Assembly}` | explicit formula and positivity; Thm 4 (`bias_sharp`, `sharp_charSum_mass`) |
| `AnalyticNumberTheory/Sharp/{KernelBounds,ConstBounds,Certificate}` | closed form; Thm 6 (`bias_closed`) |
| `AnalyticNumberTheory/Sharp/Certificate64` | Cor 7, q ≤ 2⁶⁴ (`a = 1`, `y150 = 2 log 150`) |
| `AnalyticNumberTheory/Sharp/{Majorant,GammaSharp}` | positivity for any K with ‖K̂‖ = ‖f̂‖² (majorant f ⋆ f̃); sharper gamma bound `Ilog_div_le_sharp` |
| `AnalyticNumberTheory/Sharp/{ConvKernel,ConvAssembly,ConvCertificate}` (namespace `Sharp.Conv`) | conv-square kernel K_A = f_A ⋆ f_A; Thm 10 (`bias_closed`), Cor 11 (`A = 9/4`, `R = 12`, `y220 = 2 log 220`) |
| `Pseudorandomness/{Bias,RankTwo,PrimeMeasure}` | bias, eigenvalue identity, rank-two lemma, Cor 3 |
| `MainTheorems/{Conditional,Unconditional}` | headline statements |
| `Vendor/{Schoenfeld,GRHMiller}` | adapted code (see `ATTRIBUTION.md`) |
| `Zeta23/` (lean_lib) | Weil explicit formula, 120 modules ported from Mathlib `51e6992e`; diff in `verification/zeta23-port.diff` |

## Commands (from this directory)
```sh
export PATH=$HOME/.elan/bin:/Library/TeX/texbin:$PATH
(cd lean && lake build GRHPseudo GRHPseudo.MainTheorems.Unconditional)
(cd lean && lake build --no-build GRHPseudo.MainTheorems.Unconditional)   # staleness check
(cd lean && lake env lean ../verification/Axioms.lean > ../verification/axioms.log)
(cd lean && lake env lean ../verification/EnvAxioms.lean > ../verification/env-axioms.log)
(cd lean && for m in $(find GRHPseudo -name '*.lean' | sed 's#/#.#g; s#\.lean$##' | sort); do \
   lake env leanchecker $m >/dev/null 2>&1; echo "$m: leanchecker exit $?"; done > ../verification/leanchecker.log)
(cd paper && pdflatex main && bibtex main && pdflatex main && pdflatex main)
../../.venv/bin/python experiments/closed_form_params.py
```
Replaying the 120 `Zeta23` modules (loop over `Zeta23/MODULES.txt`) takes much longer than the project modules (not timed; run it in the background); rerun it only after touching `Zeta23/`.

## Invariants to keep in sync
- **Paper ↔ Lean.** `paper/sections/results.tex` restates `sampleSpace`, `wt`, `cutoff`, `sharpNum`/`sharpDen`,
  `numB`/`denB`, `UB`, `Kc`, `Cc` and `y150`, and for the conv-square kernel `Conv.F`, `Conv.K`, `Conv.wt`,
  `Conv.sampleSpace`, `Conv.G`, `Conv.UB`, `Conv.numB`/`denB`, `y220` (Cor 11: numB ≤ 65.7, denB ≥ 143.9,
  bias ≤ 0.4566, support n ≤ 48400). After changing any of these, recheck the statement, the
  numbers in Cor 7 (numB ≤ 236.6, denB ≥ 555.8, bias ≤ 0.4257, support n ≤ 166253) and Table 2 in
  `experiments.tex`.
- **Numbering.** Paper numbering (Thm 2, Cor 3, Thm 4, Thm 6, Cor 7, Prop 8, Cor 9, Thm 10, Cor 11, Props 14–15, Lemma 16, Prop 17; a remark takes number 5) is used in `README.md`. Corrected 2026-11-27: earlier docs said Thm 5/Cor 6/Prop 7/Cor 8.
  Update both if the numbering changes.
- **Audit list.** Every new headline theorem gets a `#print axioms` line in `verification/Axioms.lean`.
  Record the counts in `verification/README.md` (currently: 31 theorems, 32 project modules replayed,
  120 Zeta23 modules replayed).
- **Experiments.** `experiments/closed_form_params.py` mirrors `numB`/`denB` exactly, and
  `experiments/convsq_formal_params.py` / `convsq_certificate_check.py` mirror `Conv.numB`/`denB`; change them together.

## Facts that are easy to get wrong
- **Optimal constant (corrected 2026-11-27, paper fixed).** c* = 2/a*² ≈ 1.2236 is the optimum only among
  *positive-definite* kernels (the cosh kernel). Convolution squares f ⋆ f use the same positivity step and give
  c(L) = 1/(1 − e^{−L/2}) → 1 (Prop 14). c ≥ 1 holds for every kernel (Prop 15, via the identity
  ∫K e^{u/2} = (1/2π)∫K̂(t)(1/2 + it)/(1/2 − it) dt for supp K ⊆ (−∞, 0], with K̂(t) = ∫K e^{itu}); equality for |u|e^{u/2}, i.e. the
  classical weight Λ(n) log(x/n). Novelty of Prop 15: none claimed.
- **Small-prime term.** It is SP(a) ≈ e^a·k(0), not 2a·k(0).
- **Scope of kernel optimality.** Prop 8 holds among positive-definite kernels (k̂ ≥ 0) only.
- **Prior art.** LLS 2015, Lemma 6.1 already gives the leading term of Thm 4 asymptotically, per
  character, with a 1 + o(1) factor. Our claim is fully explicit constants plus the certificate and the
  formalization. Ernvall-Hytönen–Palojärvi 2022 give explicit, q-uniform ψ(x;q,a) bounds; a bias bound
  follows from theirs only with weak constants. Gaillard–Jindal (SLP squareness) is known under GRH, not ours.
- **Non-positive-definite kernels (exploratory, uncertified, `experiments/kernel_lp.py`).** LP solutions give
  c ≈ 1.104, 1.047, 1.025, 1.006, 1.001 at a = 1, a*, 1.5, 2, 3 (truncated quadrature at T = 4000 plus a TV(K′) tail bound
  ≤ 0.0004, end-node slope jumps included; quadrature error unbounded). Never call these "exact" or certified. For a < 1 the discretization is unreliable.
- **Certified separation (computer-assisted, 2026-11-27).** At window length 4 a nonnegative piecewise-linear kernel has
  c ≤ 1.10814 < 1/(1 − e^{−2}) (`experiments/kernel_certificate.py`, mpmath intervals; reviewer's integer certificate gives
  < 1.1377). Key tool: periodization, (1/2π)∫|K̂| = mean |P| exactly for triangle bases. Not Lean; not yet smoothed; priority
  unchecked. Uncertified LP numbers (`kernel_lp.py`) are separate and stay labelled exploratory.
- **Cutoff vs cardinality.** Our barrier and certificates concern the cutoff X = max supp μ, not |supp μ| or seed length.
- **Prop 8 / rank-two lemma (fixed 2026-11-27).** State Prop 8 without dividing (∫k e^{u/2} ≤ (a + sinh a)k(0)); the ratio needs
  ∫k e^{u/2} > 0. The lemma's equality case needs α/‖α‖ ≠ −β/‖β‖, and only the inequality is formal.
- **JMV normalization.** Their Thm 1.1 is unnormalized: O(x^{1/2} log(xq)), degree ≈ 2 li(x).
- **LLS Lemma 6.1** was corrected (arXiv v3; corrigendum Math. Comp. 86 (2017)); cite the corrected version.
- **The formal kernels.** Both use transition width 1/64. Cosh kernel: leading coefficient 1.2626 at a*,
  1.2964 at a = 1. Conv-square kernel: (1 − e^{−A})/(e^{−1/64} − e^{−A+1/64})² = 1.162 at A = 9/4, normalized
  by the top x of its support (which is x itself, not x e^{2a}).
- **Gamma side.** The sharper bound `Ilog_div_le_sharp` (Plancherel + tail split at R) is what makes the conv-square
  certificate small; without it the conv-square closed form would give only ≈ 1.4e5. It is not yet used for the cosh
  closed form.

## Status
- **Formal, unconditional:** Thm 2, Cor 3, Thm 4, Thm 6, Cor 7, Thm 10, Cor 11 (and `bias_convSq_sharp`). Axioms
  are the standard three; the environment has core axioms only; `leanchecker` passes 32/32 project and 120/120
  Zeta23 modules.
- **Formal core only:** Prop 8 (the abstract rank-two inequality `inner_mul_inner_le`).
- **Informal:** the L²[−a,a] instance of Prop 8, the factorization theorem, Props 12–13 (convolution squares, barrier), Cor 9, and the
  sampling/complexity section.
- **Paper:** a complete 20-page draft that compiles cleanly; optimality claims corrected 2026-11-27 (dated note in §6). Author: Ethan Klein. The repository URL
  is not in the paper yet.
- **Git:** merged to `main` via PRs #1–#5 (2026-11-27). PR #3 (merge `e0bfa3d`): optimality correction, conv-square
  certificate, vendored sources, author name, Use of AI statement. PR #5 (merge `114d6b7`): fixes to informal claims after an
  external review (Prop 8, rank-two lemma, Prop 14, LP labels, sampler, Cor 9, JMV normalization, LLS corrigendum).

## Open tasks (most useful first)
See `notes/directions.md` for the ranked research directions.
1. Formalize Prop 8's L² instance (α = e^{t/2}, β = e^{−t/2} on [−a,a]; ‖α‖² = 2 sinh a, ⟨α,β⟩ = 2a)
   and its equality case.
2. Certify more instances, now best done with Thm 10 (conv-square), modelled on `ConvCertificate.lean`:
   q ≤ 2¹⁰²⁴ at ε = 1/2 (A ≈ 3.1, x ≈ 3e6), q ≤ 2⁶⁴ at ε = 0.01 (A ≈ 2.4, x ≈ 5.9e7); parameters from
   `experiments/convsq_formal_params.py`.
3. Tighten the closed forms further: apply `Ilog_div_le_sharp` to the cosh closed form too; a sharper SP bound
   using the actual Λ(n); formalize Props 14–15.
4. Run Comparator against a Mathlib-only statement file; run nanoda/lean4lean replay.
5. Paper: add the repository URL. Fill in CMQR's volume and pages once assigned
   (Math. Comp., doi:10.1090/mcom/4154).
6. Research questions: the optimal nonnegative kernel on a finite window (LP beats conv squares; needs explicit
   zero counting); extend to quotients of G_q and abelian Galois groups; nonabelian groups via zig-zag
   (`notes/directions.md`).
