# Verification record

Environment: macOS arm64, Lean v4.35.0 (`eb6cafb7`), Mathlib `56a00585`, grh-lean `72fead10`
(compact edition). Date: 2026-11-26.

| Check | Result | Log |
|---|---|---|
| `lake build` of grh-compact (local reproduction) | 9843/9843 jobs, 0 errors, 1 h 46 min | `vendor/grh-compact-build.log` (not committed) |
| `#print axioms` on the five GRH theorems | `propext, Classical.choice, Quot.sound` | `grh-compact-axioms.log` |
| `lake build GRHPseudo GRHPseudo.MainTheorems.Unconditional` | success | — |
| `#print axioms` on 13 project theorems incl. `GRHPseudo.Main.bias_primeMeasure` | all `propext, Classical.choice, Quot.sound` | `axioms.log` |
| `leanchecker` replay, every `GRHPseudo` module (15) | all exit 0 | `leanchecker.log` |
| Source scan for `sorry`, `admit`, `axiom`, `native_decide`, `implemented_by`, `@[extern]` | none | — |

Scope of `leanchecker`: it replays the declarations of the named module. Imported modules,
including the GRH proof, are trusted via their `.olean` files, which were built locally from
source. Kernel replay of the GRH proof itself was done by third parties (see
`research/grh_audit.md`), not here.

Not yet done:
- Comparator run against a Mathlib-only challenge file of our main statements.
- nanoda / lean4lean replay of an export of our modules.

Theorem statements to compare against the paper: `lean/GRHPseudo/MainTheorems/Conditional.lean`
and `Unconditional.lean`.
