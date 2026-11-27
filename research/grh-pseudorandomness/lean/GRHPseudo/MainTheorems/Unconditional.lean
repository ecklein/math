import GRHPseudo.MainTheorems.Conditional
import GRHPseudo.GRH.Discharge
import GRHPseudo.AnalyticNumberTheory.Sharp.Certificate64
import GRHPseudo.AnalyticNumberTheory.Sharp.ConvCertificate

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


/-- Zeros of Dirichlet L-functions in the critical strip lie on the line, in grh-miller's
(verbatim) formulation; Lean checks it is the compact edition's `LFunction_eq_zero_re`. -/
theorem zerosOnLine : GRHMiller.DirichletLZerosOnLine := LFunction_eq_zero_re

/-- **Theorem C (sharp, closed form), unconditional.** For every modulus `q ≥ 1`, every
nonprincipal Dirichlet character `χ` mod `q`, every `a ≥ 1` and `y > 2a`: if `denB q a y > 0` then
the cosh-kernel prime-power sample space on units mod `q` has bias at most `numB q a y / denB q a y`.
Both are elementary closed-form expressions in `(q, a, y)`. -/
theorem bias_sharp_closed {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) {a y : ℝ}
    (ha : 1 ≤ a) (hy : 2 * a < y) (hden : 0 < Sharp.denB q a y) :
    bias (Sharp.sampleSpace q a y) (Sharp.wt a y) χ ≤ Sharp.numB q a y / Sharp.denB q a y :=
  Sharp.bias_closed zerosOnLine riemannHypothesis hχ ha hy hden

/-- **Certificate, unconditional.** For every modulus `1 ≤ q ≤ 2^64` and every nonprincipal
Dirichlet character `χ` mod `q`, the sample space of integers `n ≤ ⌊22500 e²⌋` coprime to `q`, with
weights `Λ(n) k_1(log n − 2 log 150)/√n`, has bias at most `1/2`. Equivalently, every nontrivial
eigenvalue of the associated weighted Cayley graph on `(ℤ/qℤ)ˣ` has modulus at most `1/2`. -/
theorem bias_le_half_of_le_two_pow_64 {q : ℕ} [NeZero q] (hq : q ≤ 2 ^ 64)
    {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) :
    bias (Sharp.sampleSpace q 1 Sharp.y150) (Sharp.wt 1 Sharp.y150) χ ≤ 1 / 2 :=
  Sharp.bias_le_half_of_le_two_pow_64' zerosOnLine riemannHypothesis hq hχ

/-! ### Convolution-square kernel (`K_A = f_A ⋆ f_A`, window `[x e^{−2A}, x]`) -/

/-- **Sharp bias theorem, convolution-square kernel, unconditional.** -/
theorem bias_convSq_sharp {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) {A y : ℝ}
    (hA : 0 ≤ A) (hy : 2 * A < y) (hden : 0 < Sharp.Conv.sharpDen q A y) :
    bias (Sharp.Conv.sampleSpace q y) (Sharp.Conv.wt A y) χ ≤
      Sharp.Conv.sharpNum q A y / Sharp.Conv.sharpDen q A y :=
  Sharp.Conv.bias_sharp zerosOnLine riemannHypothesis hχ hA hy hden

/-- **Closed form, convolution-square kernel, unconditional.** For every modulus `q ≥ 1`, every
nonprincipal `χ` mod `q`, every `A ≥ 1/32`, `R > 0` and `y > 2A`: if `denB > 0` then the measure
`Λ(n) K_A(log n − y)/√n` on units `n ≤ e^y` has bias at most `numB/denB`. -/
theorem bias_convSq_closed {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1)
    {A y R : ℝ} (hA : 1 / 32 ≤ A) (hR : 0 < R) (hy : 2 * A < y)
    (hden : 0 < Sharp.Conv.denB q A y R) :
    bias (Sharp.Conv.sampleSpace q y) (Sharp.Conv.wt A y) χ ≤
      Sharp.Conv.numB q A y R / Sharp.Conv.denB q A y R :=
  Sharp.Conv.bias_closed zerosOnLine riemannHypothesis hχ hA hR hy hden

/-- **Certificate, convolution-square kernel, unconditional.** For every modulus `1 ≤ q ≤ 2^64`
and every nonprincipal Dirichlet character `χ` mod `q`, the measure on integers `n ≤ 48400`
coprime to `q` with weights `Λ(n) K_{9/4}(log n − 2 log 220)/√n` has bias at most `1/2`. -/
theorem bias_le_half_of_le_two_pow_64_convSq {q : ℕ} [NeZero q] (hq : q ≤ 2 ^ 64)
    {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) :
    bias (Sharp.Conv.sampleSpace q Sharp.Conv.y220) (Sharp.Conv.wt (9 / 4) Sharp.Conv.y220) χ ≤
      1 / 2 :=
  Sharp.Conv.bias_le_half_of_le_two_pow_64' zerosOnLine riemannHypothesis hq hχ

end GRHPseudo.Main
