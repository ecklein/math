import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# The rank-two extremal inequality (Theorem T1(b), abstract form)

In a real inner product space, for all `f, α, β`,

    ⟪f, α⟫ * ⟪f, β⟫ ≤ (‖α‖ * ‖β‖ + ⟪α, β⟫) / 2 * ‖f‖ ^ 2.

In the application, `E = L²[-a, a]`, `α = e^{v/2}`, `β = e^{-v/2}`, so `‖α‖ ‖β‖ = 2 sinh a` and
`⟪α, β⟫ = 2a`. The quantity `⟪f, α⟫ ⟪f, β⟫ / ‖f‖²` equals `∫ k(u) e^{u/2} du / k(0)` for
`k = f ⋆ f̃`, which is the reciprocal of the leading coefficient of the bias bound. Hence no
kernel supported in `[-2a, 2a]` beats `1 / (a + sinh a)`.

Proof: with `u = α/‖α‖`, `v = β/‖β‖`,
`⟪f,u⟫⟪f,v⟫ = (⟪f,u+v⟫² - ⟪f,u-v⟫²)/4 ≤ ‖f‖² ‖u+v‖²/4 = ‖f‖² (1 + ⟪u,v⟫)/2`.
We prove it without normalising: apply the same identity to `‖β‖ • α` and `‖α‖ • β`.
-/

namespace GRHPseudo

open RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Polarisation-type identity: `4 ⟪f,a⟫⟪f,b⟫ = ⟪f,a+b⟫² - ⟪f,a-b⟫²`. -/
theorem four_inner_mul_inner (f a b : E) :
    4 * (⟪f, a⟫ * ⟪f, b⟫) = ⟪f, a + b⟫ ^ 2 - ⟪f, a - b⟫ ^ 2 := by
  rw [inner_add_right, inner_sub_right]
  ring

/-- `⟪f,a⟫⟪f,b⟫ ≤ ‖f‖² ‖a + b‖² / 4`. -/
theorem inner_mul_inner_le_quarter (f a b : E) :
    ⟪f, a⟫ * ⟪f, b⟫ ≤ ‖f‖ ^ 2 * ‖a + b‖ ^ 2 / 4 := by
  have h1 := four_inner_mul_inner f a b
  have h2 : ⟪f, a + b⟫ ^ 2 ≤ (‖f‖ * ‖a + b‖) ^ 2 := by
    have := abs_real_inner_le_norm f (a + b)
    have h0 : 0 ≤ |⟪f, a + b⟫| := abs_nonneg _
    calc ⟪f, a + b⟫ ^ 2 = |⟪f, a + b⟫| ^ 2 := (sq_abs _).symm
      _ ≤ (‖f‖ * ‖a + b‖) ^ 2 := pow_le_pow_left₀ h0 this 2
  nlinarith [sq_nonneg ⟪f, a - b⟫]

/-- `‖α‖ ‖β‖ + ⟪α,β⟫ ≥ 0` (Cauchy–Schwarz). -/
theorem norm_mul_norm_add_inner_nonneg (α β : E) : 0 ≤ ‖α‖ * ‖β‖ + ⟪α, β⟫ := by
  have := abs_real_inner_le_norm α β
  linarith [neg_abs_le ⟪α, β⟫]

/-- **Rank-two extremal inequality.** -/
theorem inner_mul_inner_le (f α β : E) :
    ⟪f, α⟫ * ⟪f, β⟫ ≤ (‖α‖ * ‖β‖ + ⟪α, β⟫) / 2 * ‖f‖ ^ 2 := by
  have hcs := norm_mul_norm_add_inner_nonneg α β
  rcases eq_or_ne α 0 with rfl | hα
  · simp only [inner_zero_right, zero_mul]; positivity
  rcases eq_or_ne β 0 with rfl | hβ
  · simp only [inner_zero_right, mul_zero]; positivity
  have hA : 0 < ‖α‖ := norm_pos_iff.mpr hα
  have hB : 0 < ‖β‖ := norm_pos_iff.mpr hβ
  set A := ‖α‖
  set B := ‖β‖
  have key := inner_mul_inner_le_quarter f (B • α) (A • β)
  rw [inner_smul_right, inner_smul_right] at key
  have hn : ‖B • α + A • β‖ ^ 2 = B ^ 2 * A ^ 2 + 2 * (A * B) * ⟪α, β⟫ + A ^ 2 * B ^ 2 := by
    rw [norm_add_sq_real, norm_smul, norm_smul, inner_smul_left, inner_smul_right]
    simp only [Real.norm_eq_abs, abs_norm, conj_trivial, A, B]
    ring
  rw [hn] at key
  have hAB : 0 < A * B := mul_pos hA hB
  have : (A * B) * (⟪f, α⟫ * ⟪f, β⟫) ≤ (A * B) * ((A * B + ⟪α, β⟫) / 2 * ‖f‖ ^ 2) := by
    nlinarith [key]
  exact le_of_mul_le_mul_left this hAB

end GRHPseudo
