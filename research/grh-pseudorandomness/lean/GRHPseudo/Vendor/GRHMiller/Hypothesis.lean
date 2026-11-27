/- Vendored from github.com/amrehan/grh-miller v1.0.0 (commit e3e573a), `GRHMiller/Hypothesis.lean`
   (Apache-2.0). Only import paths changed. See ATTRIBUTION.md. -/
import Mathlib

/-!
# The hypothesis: GRH for Dirichlet L-functions

A verbatim copy of `DirichletLZerosOnLine` from `Statements.lean` in Levent Alpöge's Lean proof of the Riemann
hypothesis (https://github.com/leanprover-community/riemann-hypothesis). Every conditional theorem in this library
takes `hGRH : GRHMiller.DirichletLZerosOnLine`; `Unconditional/Unconditional.lean` checks that Alpöge's
`LFunction_eq_zero_re` proves exactly this proposition.

It concerns Mathlib's Dirichlet L-functions only (no Dedekind zeta or Artin L-functions).
-/

namespace GRHMiller

/-- Every zero of every Dirichlet L-function in the critical strip lies on `Re s = 1/2`. -/
def DirichletLZerosOnLine : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ),
    0 < s.re → s.re < 1 → DirichletCharacter.LFunction χ s = 0 → s.re = 1 / 2

end GRHMiller
