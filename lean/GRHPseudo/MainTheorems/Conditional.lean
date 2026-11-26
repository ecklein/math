import GRHPseudo.Pseudorandomness.PrimeMeasure

/-!
# Main theorems, conditional on GRH for Dirichlet L-functions

Statements are given in full here, so they can be compared with the paper independently of the
proof files.
-/

namespace GRHPseudo.Main

open ArithmeticFunction

/-- **Theorem A (prime character sums).** Under GRH, for every modulus `q ≥ 1`, every
nonprincipal Dirichlet character `χ` mod `q` (primitive or not), and every `N ≥ 3`. -/
theorem primeCharSum_conditional (hGRH : GRHHyp) {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) {N : ℕ} (hN : 3 ≤ N) :
    ‖∑ n ∈ Finset.Ioo 0 N, χ n * (Λ n : ℂ) * (((1 - (n : ℝ) / N : ℝ)) : ℂ)‖ ≤
      48 * Real.exp 1 / Real.pi * Real.log N ^ 2 * Real.sqrt N *
        (Real.pi * Real.log (2 + 8 * q) + Jconst) :=
  norm_sum_vonMangoldt_char_le hGRH hχ hN

/-- **Theorem B (explicit spectral gap of the prime-power Cayley graph on `(ℤ/qℤ)ˣ`).**
Under GRH, the sample space of `n < N` coprime to `q` with weights `Λ(n)(1 − n/N)` has bias
at most `charSumBound q N / massLower q N` against every nonprincipal character mod `q`. By
`charSum_eq_eigenvalue` this bounds every nontrivial eigenvalue of the normalised weighted
Cayley graph. -/
theorem bias_conditional (hGRH : GRHHyp) {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) {N : ℕ} (hN : 3 ≤ N) (hL : 0 < massLower q N) :
    bias (unitSupport q N) (primeWeight N) χ ≤ charSumBound q N / massLower q N :=
  bias_primeMeasure_le hGRH hχ hN hL

end GRHPseudo.Main
