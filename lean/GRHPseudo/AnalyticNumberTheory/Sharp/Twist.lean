import Zeta23.Defs

/-!
# Twisting a test function (obligation D1)

`paperFT k z = ∫ k(u) e^{izu} du` (zeta-23-lean's convention). Translating the test function by
`y` multiplies its transform by `e^{izy}`. On zeros `ρ = 1/2 + iγ` (GRH) this is the phase
`e^{iγy} = x^{iγ}` with `x = e^y`. The explicit formula applied to the twisted kernel then gives
the prime sum near `x`.
-/

noncomputable section

open Complex MeasureTheory

namespace GRHPseudo.Sharp

/-- `k` translated by `y`. -/
def twist (k : ℝ → ℂ) (y : ℝ) : ℝ → ℂ := fun u ↦ k (u - y)

theorem paperFT_twist (k : ℝ → ℂ) (y : ℝ) (z : ℂ) :
    Zeta23.paperFT (twist k y) z = Complex.exp (I * z * y) * Zeta23.paperFT k z := by
  unfold Zeta23.paperFT twist
  have h : ∀ u : ℝ, k (u - y) * Complex.exp (I * z * (u : ℂ)) =
      (fun v : ℝ ↦ k v * Complex.exp (I * z * ((v : ℂ) + y))) (u - y) := by
    intro u; simp
  simp_rw [h]
  rw [integral_sub_right_eq_self (fun v : ℝ ↦ k v * Complex.exp (I * z * ((v : ℂ) + y))),
    ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun v ↦ ?_)
  simp only [mul_add, Complex.exp_add]
  ring

end GRHPseudo.Sharp
