import GRHPseudo.MainTheorems.Conditional
import GRHPseudo.GRH.Discharge

/-!
# Main theorems, unconditional

The GRH hypothesis is discharged by `GRHPseudo.grh := LFunction_ne_zero_of_half_lt_re`, the
theorem of the compact edition of the Lean proof of GRH (github.com/lsernau/grh-lean @ 72fead10).
-/

namespace GRHPseudo.Main

open ArithmeticFunction

theorem primeCharSum {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) {N : ℕ}
    (hN : 3 ≤ N) :
    ‖∑ n ∈ Finset.Ioo 0 N, χ n * (Λ n : ℂ) * (((1 - (n : ℝ) / N : ℝ)) : ℂ)‖ ≤
      48 * Real.exp 1 / Real.pi * Real.log N ^ 2 * Real.sqrt N *
        (Real.pi * Real.log (2 + 8 * q) + Jconst) :=
  primeCharSum_conditional grh hχ hN

theorem bias_primeMeasure {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) {N : ℕ}
    (hN : 3 ≤ N) (hL : 0 < massLower q N) :
    bias (unitSupport q N) (primeWeight N) χ ≤ charSumBound q N / massLower q N :=
  bias_conditional grh hχ hN hL

end GRHPseudo.Main
