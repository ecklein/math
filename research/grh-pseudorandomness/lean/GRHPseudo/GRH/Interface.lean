import Statements

/-!
# GRH dependency interface

The only analytic input we take from the GRH project is the proposition
`DirichletLNonvanishingRightOfHalf` from its `Statements` module, which imports only Mathlib:

    ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ),
      1 / 2 < s.re → (χ ≠ 1 ∨ s ≠ 1) → DirichletCharacter.LFunction χ s ≠ 0

Everything in `GRHPseudo` except `GRHPseudo.GRH.Discharge` and `GRHPseudo.MainTheorems.*Unconditional`
is proved with this proposition as an explicit hypothesis `hGRH : GRHHyp`. The discharge module
supplies `LFunction_ne_zero_of_half_lt_re` from the compact edition
(github.com/lsernau/grh-lean @ 72fead10, `grh-compact/src/Main.lean`).
-/

namespace GRHPseudo

/-- GRH for Dirichlet L-functions, exactly as stated in the GRH project's `Statements.lean`. -/
abbrev GRHHyp : Prop := DirichletLNonvanishingRightOfHalf

/-- The form in which we use the hypothesis: nonprincipal `L`-functions have no zeros right of
the critical line. -/
theorem LFunction_ne_zero (hGRH : GRHHyp) {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hχ : χ ≠ 1) {s : ℂ} (hs : 1 / 2 < s.re) : χ.LFunction s ≠ 0 :=
  hGRH N χ s hs (Or.inl hχ)

end GRHPseudo
