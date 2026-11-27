# CLAUDE.md — grh-pseudorandomness

Project state and working notes. The general process is in `../../CLAUDE.md`. **Update this file
whenever results, statements, commands, status or open tasks change.** Last updated: 2026-11-27.

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
| `AnalyticNumberTheory/Sharp/{KernelBounds,ConstBounds,Certificate}` | closed form; Thm 5 (`bias_closed`) |
| `AnalyticNumberTheory/Sharp/Certificate64` | Cor 6, q ≤ 2⁶⁴ (`a = 1`, `y150 = 2 log 150`) |
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
  `numB`/`denB`, `UB`, `Kc`, `Cc` and `y150`. After changing any of these, recheck the statement, the
  numbers in Cor 6 (numB ≤ 236.6, denB ≥ 555.8, bias ≤ 0.4257, support n ≤ 166253) and Table 2 in
  `experiments.tex`.
- **Numbering.** Paper numbering (Thm 2, Cor 3, Thm 4, Thm 5, Cor 6, Prop 7, Cor 8) is used in `README.md`.
  Update both if the numbering changes.
- **Audit list.** Every new headline theorem gets a `#print axioms` line in `verification/Axioms.lean`.
  Record the counts in `verification/README.md` (currently: 23 theorems, 27 project modules replayed,
  120 Zeta23 modules replayed).
- **Experiments.** `experiments/closed_form_params.py` mirrors `numB`/`denB` exactly; change both together.

## Facts that are easy to get wrong
- **Optimal constant.** It is c* = 2/a*² ≈ 1.2236 with a* ≈ 1.27846, the root of a = 1 + e^{−a}. It is
  **not 2**: 2 is only the a → ∞ limit. Support needed is ≈ 1.497 log²q/ε².
- **Small-prime term.** It is SP(a) ≈ e^a·k(0), not 2a·k(0).
- **Scope of kernel optimality.** It holds among positive-definite kernels (k̂ ≥ 0). For general kernels in
  the LLS framework the question is open; the trivial bound is ≥ 1/(4 sinh a).
- **Prior art.** LLS 2015, Lemma 6.1 already gives the leading term of Thm 4 asymptotically, per
  character, with a 1 + o(1) factor. Our claim is fully explicit constants plus the certificate and the
  formalization. Ernvall-Hytönen–Palojärvi 2022 give explicit, q-uniform ψ(x;q,a) bounds; a bias bound
  follows from theirs only with weak constants. Gaillard–Jindal (SLP squareness) is known under GRH, not ours.
- **The formal kernel.** It uses grh-miller's smoothed cutoff (transition width 1/64), so its leading
  coefficient is 1.2626 at a*, not c*.

## Status
- **Formal, unconditional:** Thm 2, Cor 3, Thm 4, Thm 5, Cor 6. Axioms are the standard three; the
  environment has core axioms only; `leanchecker` passes 27/27 project and 120/120 Zeta23 modules.
- **Formal core only:** Prop 7 (the abstract rank-two inequality `inner_mul_inner_le`).
- **Informal:** the L²[−a,a] instance of Prop 7, the factorization theorem, Cor 8, and the
  sampling/complexity section.
- **Paper:** a complete 16-page draft that compiles cleanly. Author names are a placeholder
  (`[Author names to be added]`). The repository URL is not in the paper yet.
- **Git:** merged to `main` via PR #1 (2026-11-27). The branch `grh-pseudorandomness` still exists.

## Open tasks (most useful first)
1. Formalize Prop 7's L² instance (α = e^{t/2}, β = e^{−t/2} on [−a,a]; ‖α‖² = 2 sinh a, ⟨α,β⟩ = 2a)
   and its equality case.
2. Certify more instances of Thm 5 (e.g. q ≤ 2¹⁰²⁴ at ε = 1/2, or q ≤ 2⁶⁴ at ε = 0.01), modelled on
   `Certificate64.lean`. Parameters come from `experiments/closed_form_params.py`.
3. Tighten the closed form, which loses about 4× in support against the quadrature constants: a sharper SP
   bound using the actual Λ(n) and k(log n), and sharper Fourier-decay constants. Also try a = a*.
4. Run Comparator against a Mathlib-only statement file; run nanoda/lean4lean replay.
5. Paper: add author names and the repository URL. Fill in CMQR's volume and pages once assigned
   (Math. Comp., doi:10.1090/mcom/4154).
6. Research questions: can non-positive-definite kernels beat c*? Extend to quotients of G_q and abelian
   Galois groups; nonabelian groups via zig-zag.
