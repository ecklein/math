import GRHPseudo.GRH.Interface
import GRHPseudo.AnalyticNumberTheory.LGrowth
import GRHPseudo.AnalyticNumberTheory.LogDerivBound

/-!
# Log-derivative of nonprincipal Dirichlet L-functions right of the critical line (uses GRH)

For `χ ≠ 1` mod `N`, `0 < ε ≤ 1` and `1/2 + ε ≤ Re s ≤ 2`:

    ‖L'(s, χ) / L(s, χ)‖ ≤ (48 / ε²) · log (2 (1 + 4 N (|Im s| + 4))).

Proof: Borel–Carathéodory (`Vendored.norm_deriv_div_le_of_forall_mem_ball_ne_zero`) on the disc
centred at `c = 2 + i Im s` of radius `3/2 − ε/2`. That disc lies in `Re z > 1/2`, where `L` has
no zeros by GRH. On it `‖L‖ ≤ 1 + 4 N ‖z‖` (`norm_LFunction_le_linear`), and `‖L(c)‖ ≥ 1/2`
because `L(c, χ) L(c, χμ) = 1` with `‖L(c, χμ)‖ ≤ ζ(2) ≤ 2`.

This is proof obligation A3 of `notes/proof_obligations.md`.
-/

noncomputable section

open Complex Metric DirichletCharacter

namespace GRHPseudo

/-- An L-series with coefficients of norm at most `1` has norm at most `2` on `Re s ≥ 2`.
(Adapted from `norm_LSeries_char_le`.) -/
lemma norm_LSeries_le_two {f : ℕ → ℂ} (hf : ∀ n, ‖f n‖ ≤ 1) {s : ℂ} (hs : 2 ≤ s.re) :
    ‖LSeries f s‖ ≤ 2 := by
  have hs_one : 1 < s.re := by linarith
  have h_summable : Summable fun n : ℕ ↦ 1 / (n : ℝ) ^ s.re :=
    Real.summable_one_div_nat_rpow.2 hs_one
  have term_le (n : ℕ) : ‖LSeries.term f s n‖ ≤ 1 / (n : ℝ) ^ s.re := by
    rw [LSeries.norm_term_eq]
    split_ifs
    · positivity
    · exact div_le_div_of_nonneg_right (hf n) (by positivity)
  have zeta_le : ∑' n : ℕ, 1 / (n + 1 : ℝ) ^ s.re ≤ 1 + 1 / (s.re - 1) := by
    have h_nonneg : 0 ≤ s.re * ZetaAsymptotics.termTSum s.re :=
      mul_nonneg (by linarith) (tsum_nonneg fun n ↦ ZetaAsymptotics.term_nonneg _ _)
    linarith [ZetaAsymptotics.zeta_limit_aux1 hs_one]
  calc
    _ ≤ ∑' n : ℕ, 1 / (n : ℝ) ^ s.re := tsum_of_norm_bounded h_summable.hasSum term_le
    _ = ∑' n : ℕ, 1 / (n + 1 : ℝ) ^ s.re := by
      rw [h_summable.tsum_eq_zero_add]
      simp [Real.zero_rpow (one_pos.trans hs_one).ne']
    _ ≤ 1 + 1 / (s.re - 1) := zeta_le
    _ ≤ 2 := by
      have : 1 / (s.re - 1) ≤ 1 := by
        rw [div_le_one (by linarith)]; linarith
      linarith

variable {N : ℕ} [NeZero N]

/-- `‖L(s, χ)‖ ≥ 1/2` on `Re s ≥ 2`, for every Dirichlet character. -/
lemma one_half_le_norm_LFunction (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : 2 ≤ s.re) :
    1 / 2 ≤ ‖χ.LFunction s‖ := by
  have h1 : 1 < s.re := by linarith
  have hmul := LSeries.mul_mu_eq_one χ h1
  rw [← χ.LFunction_eq_LSeries h1] at hmul
  have hcoef : ∀ n, ‖((fun n : ℕ ↦ χ n) * fun n : ℕ ↦ ((ArithmeticFunction.moebius n : ℤ) : ℂ)) n‖
      ≤ 1 := by
    intro n
    simp only [Pi.mul_apply, norm_mul]
    have hχn := χ.norm_le_one n
    have hμ : ‖((ArithmeticFunction.moebius n : ℤ) : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_intCast]
      exact_mod_cast ArithmeticFunction.abs_moebius_le_one
    calc ‖χ n‖ * ‖((ArithmeticFunction.moebius n : ℤ) : ℂ)‖ ≤ 1 * 1 :=
          mul_le_mul hχn hμ (norm_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  have h2 := norm_LSeries_le_two hcoef hs
  have h3 : ‖χ.LFunction s‖ * ‖LSeries ((fun n : ℕ ↦ χ n) *
      fun n : ℕ ↦ ((ArithmeticFunction.moebius n : ℤ) : ℂ)) s‖ = 1 := by
    rw [← norm_mul, hmul, norm_one]
  nlinarith [norm_nonneg (χ.LFunction s)]

/-- **Log-derivative bound under GRH.** -/
theorem norm_logDeriv_LFunction_le (hGRH : GRHHyp) {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) {s : ℂ} (h1 : 1 / 2 + ε ≤ s.re) (h2 : s.re ≤ 2) :
    ‖deriv χ.LFunction s / χ.LFunction s‖ ≤
      48 / ε ^ 2 * Real.log (2 * (1 + 4 * N * (|s.im| + 4))) := by
  set t := s.im
  set c : ℂ := 2 + (t : ℂ) * I
  set r₁ : ℝ := 3 / 2 - ε
  set r₂ : ℝ := 3 / 2 - ε / 2
  set B : ℝ := 1 + 4 * N * (|t| + 4)
  have hr₁ : 0 < r₁ := by simp only [r₁]; linarith
  have h12 : r₁ < r₂ := by simp only [r₁, r₂]; linarith
  have hc_re : c.re = 2 := by simp [c]
  have hc_im : c.im = t := by simp [c]
  have hc_norm : ‖c‖ ≤ 2 + |t| := by
    calc ‖c‖ ≤ ‖(2 : ℂ)‖ + ‖(t : ℂ) * I‖ := norm_add_le _ _
      _ = 2 + |t| := by simp
  -- points of the big disc have real part > 1/2
  have hre_of_mem : ∀ z ∈ ball c r₂, 1 / 2 + ε / 2 < z.re := by
    intro z hz
    have hd : ‖z - c‖ < r₂ := by simpa [dist_eq_norm] using hz
    have := Complex.abs_re_le_norm (z - c)
    simp only [sub_re, hc_re] at this
    have := neg_abs_le (z.re - 2)
    simp only [r₂] at hd
    linarith
  have hf : DifferentiableOn ℂ χ.LFunction (ball c r₂) :=
    (differentiable_LFunction hχ).differentiableOn
  have hne : ∀ z ∈ ball c r₂, χ.LFunction z ≠ 0 := fun z hz ↦
    LFunction_ne_zero hGRH hχ (by linarith [hre_of_mem z hz])
  have hB : ∀ z ∈ ball c r₂, ‖χ.LFunction z‖ ≤ B := by
    intro z hz
    have hz' := hre_of_mem z hz
    have hlin := norm_LFunction_le_linear χ hχ (s := z) (by linarith)
    have hzn : ‖z‖ ≤ |t| + 4 := by
      have hd : ‖z - c‖ < r₂ := by simpa [dist_eq_norm] using hz
      calc ‖z‖ = ‖(z - c) + c‖ := by rw [sub_add_cancel]
        _ ≤ ‖z - c‖ + ‖c‖ := norm_add_le _ _
        _ ≤ r₂ + (2 + |t|) := by linarith
        _ ≤ |t| + 4 := by simp only [r₂]; linarith
    calc ‖χ.LFunction z‖ ≤ 1 + 4 * N * ‖z‖ := hlin
      _ ≤ B := by
        simp only [B]
        gcongr
  have hs_mem : s ∈ closedBall c r₁ := by
    rw [mem_closedBall, dist_eq_norm]
    have hsc : s - c = ((s.re - 2 : ℝ) : ℂ) := by
      apply Complex.ext <;> simp [c, t]
    rw [hsc, Complex.norm_real, Real.norm_eq_abs, abs_le]
    simp only [r₁]
    constructor <;> linarith
  have key := Vendored.norm_deriv_div_le_of_forall_mem_ball_ne_zero hr₁ h12 hf hne hB hs_mem
  have hc_ball : c ∈ ball c r₂ := mem_ball_self (hr₁.trans h12)
  have hLc_lower : 1 / 2 ≤ ‖χ.LFunction c‖ := one_half_le_norm_LFunction χ (by rw [hc_re])
  have hLc_pos : 0 < ‖χ.LFunction c‖ := by linarith
  have hLc_upper : ‖χ.LFunction c‖ ≤ B := hB c hc_ball
  have hB_pos : 0 < B := by simp only [B]; positivity
  have hlog_nonneg : 0 ≤ Real.log (B / ‖χ.LFunction c‖) :=
    Real.log_nonneg ((one_le_div hLc_pos).mpr hLc_upper)
  have hlog_le : Real.log (B / ‖χ.LFunction c‖) ≤ Real.log (2 * B) := by
    apply Real.log_le_log (div_pos hB_pos hLc_pos)
    rw [div_le_iff₀ hLc_pos]
    nlinarith
  have hconst : 8 * r₂ / (r₂ - r₁) ^ 2 ≤ 48 / ε ^ 2 := by
    have hdiff : r₂ - r₁ = ε / 2 := by simp only [r₁, r₂]; ring
    rw [hdiff, div_le_div_iff₀ (by positivity) (by positivity)]
    simp only [r₂]
    nlinarith [sq_nonneg ε]
  calc ‖deriv χ.LFunction s / χ.LFunction s‖
      ≤ 8 * r₂ / (r₂ - r₁) ^ 2 * Real.log (B / ‖χ.LFunction c‖) := key
    _ ≤ 48 / ε ^ 2 * Real.log (2 * B) := by
      apply mul_le_mul hconst hlog_le hlog_nonneg (by positivity)

end GRHPseudo
