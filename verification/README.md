# Verification record

Environment: macOS arm64, Lean v4.35.0 (`eb6cafb7`), Mathlib `56a00585`, grh-lean `72fead10`
(compact edition). Date: 2026-11-26.

| Check | Result | Log |
|---|---|---|
| `lake build` of grh-compact (local reproduction) | 9843/9843 jobs, 0 errors, 1 h 46 min | `vendor/grh-compact-build.log` (not committed) |
| `#print axioms` on the five GRH theorems | `propext, Classical.choice, Quot.sound` | `grh-compact-axioms.log` |
| `lake build GRHPseudo GRHPseudo.MainTheorems.Unconditional` | success | — |
| `#print axioms` on 19 theorems incl. `GRHPseudo.Main.bias_primeMeasure`, `GRHPseudo.Sharp.bias_sharp`, `EF_lit_chi_L` | all `propext, Classical.choice, Quot.sound` | `axioms.log` |
| Whole-environment axiom listing (`EnvAxioms.lean`) | only Lean core (`Init.Prelude`, `Init.Core`) | `env-axioms.log` |
| `leanchecker` replay, every `GRHPseudo` module (23) | all exit 0 | `leanchecker.log` |
| `leanchecker` replay, ported `Zeta23` modules (120) | running (started 2026-11-26; result to be recorded) | `leanchecker-zeta23.log` |
| Port of zeta-23-lean to Mathlib 56a00585 | 4 rebuild rounds, final: 0 errors | `zeta23-port-build-{1..4}.log` |
| Source scan for `sorry`, `admit`, `axiom`, `native_decide`, `implemented_by`, `@[extern]` | none in `GRHPseudo`; in `Zeta23` only inside comments/docstrings (two `axiom` lines are in a docstring code example of the vendored tactic file) | — |

Scope of `leanchecker`: it replays the declarations of the named module. Imported modules,
including the GRH proof, are trusted via their `.olean` files, which were built locally from
source. Kernel replay of the GRH proof itself was done by third parties (see
`research/grh_audit.md`), not here.

Not yet done:
- Comparator run against a Mathlib-only challenge file of our main statements.
- nanoda / lean4lean replay of an export of our modules.

Theorem statements to compare against the paper: `lean/GRHPseudo/MainTheorems/Conditional.lean`
and `Unconditional.lean`.
