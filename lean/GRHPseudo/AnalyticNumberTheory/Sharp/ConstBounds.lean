import GRHPseudo.AnalyticNumberTheory.Sharp.KernelBounds
import GRHPseudo.Pseudorandomness.PrimeMeasure

/-!
# Closed-form bounds for the remaining constants (Layer 2, part 2)

For `a ≥ 1`, with `K(a) = sinh a + a cosh a` and `C(a) = (4 sinh(a/2))² + (2 sinh(a/2) + 2 cosh(a/2))²`:

* `I(B) ≤ C(a) (6 + B π)` for `B ≥ 0`. Uses `|f̂| ≤ 4 sinh(a/2)` and `|f̂(r)| |r| ≤ 2 sinh(a/2) + 2 cosh(a/2)`
  (the derivations are adapted from grh-miller's `ankeny_N_decay4`) and `J ≤ 6` (`Jconst_le_6`).
* `SP(a) ≤ 2 K(a) (2/e) (⌊e^{2a}⌋ + 1)`, via `Λ(n)/√n ≤ log n/√n ≤ 2/e`.
* `U ≤ K(a) e^{a − y/2} log q · log₂ M`: on the support `√n ≥ e^{(y−2a)/2}`, and non-unit prime
  powers carry von Mangoldt mass at most `log q · log₂ M` (`sum_vonMangoldt_nonunit_le`).
-/

noncomputable section

open Complex MeasureTheory Finset Zeta23 Zeta23.EF
open scoped Real ComplexConjugate

namespace GRHPseudo.Sharp

open GRHMiller.Narrow

/-- `K(a) = sinh a + a cosh a`. -/
def Kc (a : ℝ) : ℝ := Real.sinh a + a * Real.cosh a

/-- `C(a) = (4 sinh(a/2))² + (2 sinh(a/2) + 2 cosh(a/2))²`. -/
def Cc (a : ℝ) : ℝ := (4 * Real.sinh (a / 2)) ^ 2 + (2 * Real.sinh (a / 2) + 2 * Real.cosh (a / 2)) ^ 2

lemma Cc_nonneg (a : ℝ) : 0 ≤ Cc a := by unfold Cc; positivity

/-- **`I(B) ≤ C(a)(6 + Bπ)`.** -/
theorem Ilog_le {a B : ℝ} (ha : 1 ≤ a) (hB : 0 ≤ B) : Ilog (testF a) B ≤ Cc a * (6 + B * π) := by
  have ha0 : 0 ≤ a := by linarith
  set f := testF a with hfdef
  have hf : ContDiff ℝ 2 f := contDiff_testF a
  have hfs : HasCompactSupport f := hasCompactSupport_testF a
  have hsupp : ∀ u, f u ≠ 0 → |u| ≤ a := by
    intro u hu
    have : testFN a u ≠ 0 := fun h ↦ hu (by simp [hfdef, testF, testFnN, h])
    exact abs_le.mpr (support_testFN_subset a this)
  have hfi : Integrable f := hf.continuous.integrable_of_hasCompactSupport hfs
  have hcont : Continuous (fun r : ℝ ↦ paperFT f (r : ℂ)) :=
    (WeilEF.differentiable_paperFT hf.continuous hfs).continuous.comp Complex.continuous_ofReal
  have h0 : ∀ r : ℝ, ‖paperFT f (r : ℂ)‖ ≤ 4 * Real.sinh (a / 2) := fun r ↦ by
    have := norm_paperFT_le hfi hsupp (r : ℂ)
    simp only [Complex.ofReal_im, abs_zero, zero_mul, Real.exp_zero, one_mul] at this
    refine this.trans ?_
    have := integral_testFN_le ha0
    simpa [hfdef, testF, testFnN, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (testFN_nonneg a _)] using this
  have h1 : ∀ r : ℝ, ‖paperFT f (r : ℂ)‖ * |r| ≤ 2 * Real.sinh (a / 2) + 2 * Real.cosh (a / 2) :=
    fun r ↦ by
    have := Taper.norm_paperFT_mul_le (hf.of_le (by norm_num)) hsupp (r : ℂ)
    simp only [Complex.ofReal_im, abs_zero, zero_mul, Real.exp_zero, one_mul,
      Complex.norm_real, Real.norm_eq_abs] at this
    refine this.trans ?_
    have hd : ∀ t, deriv f t = ((deriv (testFN a) t : ℝ) : ℂ) := fun t ↦ by
      rw [(hasDerivAt_testFN a t).deriv]
      exact ((hasDerivAt_testFN a t).ofReal_comp).deriv
    simpa [hd, Complex.norm_real, Real.norm_eq_abs] using integral_abs_deriv_testFN_le ha
  have hRHS := GRHMiller.integral_normSq_paperFT_mul_le (A := 1) (B := B) zero_le_one hB hcont h0 h1
  have hJ := GRHMiller.Jconst_le_6
  unfold Ilog
  refine hRHS.trans ?_
  unfold Cc
  have hC : 0 ≤ (4 * Real.sinh (a / 2)) ^ 2 + (2 * Real.sinh (a / 2) + 2 * Real.cosh (a / 2)) ^ 2 := by
    positivity
  exact mul_le_mul_of_nonneg_left (by linarith) hC

/-- `log n / √n ≤ 2/e`. -/
lemma log_div_sqrt_le (n : ℕ) : Real.log n / Real.sqrt n ≤ 2 / Real.exp 1 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp; positivity
  have hs : 0 < Real.sqrt n := Real.sqrt_pos.mpr (by exact_mod_cast hn)
  have he : 0 < Real.exp 1 := Real.exp_pos 1
  -- `log s ≤ s/e` from `log(s/e) ≤ s/e − 1`
  have key : Real.log (Real.sqrt n) ≤ Real.sqrt n / Real.exp 1 := by
    have := Real.log_le_sub_one_of_pos (div_pos hs he)
    rw [Real.log_div hs.ne' he.ne', Real.log_exp] at this
    linarith
  have hlog : Real.log n = 2 * Real.log (Real.sqrt n) := by
    rw [← Real.log_rpow hs, Real.sqrt_eq_rpow, ← Real.rpow_mul (Nat.cast_nonneg n)]
    norm_num
  have key' : Real.log (Real.sqrt n) * Real.exp 1 ≤ Real.sqrt n := (le_div_iff₀ he).mp key
  rw [div_le_div_iff₀ hs he, hlog]
  linarith

/-- **Small-prime sum.** -/
theorem smallPrimes_le {a : ℝ} (ha : 0 ≤ a) :
    smallPrimes a ≤ 2 * Kc a * (2 / Real.exp 1) * (⌊Real.exp (2 * a)⌋₊ + 1) := by
  unfold smallPrimes
  have hterm : ∀ n ∈ range (⌊Real.exp (2 * a)⌋₊ + 1),
      ArithmeticFunction.vonMangoldt n / Real.sqrt n *
        (‖kern a (Real.log n)‖ + ‖kern a (-Real.log n)‖) ≤ 2 * Kc a * (2 / Real.exp 1) := by
    intro n hn
    have hlog : |Real.log n| ≤ 2 * a := by
      rw [abs_of_nonneg (Real.log_natCast_nonneg n)]
      rcases Nat.eq_zero_or_pos n with rfl | hn0
      · simp; linarith
      have hnle : (n : ℝ) ≤ Real.exp (2 * a) := by
        have := mem_range.mp hn
        have h2 : n ≤ ⌊Real.exp (2 * a)⌋₊ := by omega
        exact (Nat.cast_le.mpr h2).trans (Nat.floor_le (Real.exp_pos _).le)
      rw [← Real.log_exp (2 * a)]
      exact Real.log_le_log (by exact_mod_cast hn0) hnle
    have hk1 := norm_kern_le ha hlog
    have hk2 := norm_kern_le ha (u := -Real.log n) (by rw [abs_neg]; exact hlog)
    have hΛ : ArithmeticFunction.vonMangoldt n / Real.sqrt n ≤ 2 / Real.exp 1 :=
      (div_le_div_of_nonneg_right ArithmeticFunction.vonMangoldt_le_log (Real.sqrt_nonneg _)).trans
        (log_div_sqrt_le n)
    have hΛ0 : 0 ≤ ArithmeticFunction.vonMangoldt n / Real.sqrt n :=
      div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _)
    have hK0 : 0 ≤ Kc a := le_trans (norm_nonneg _) hk1
    calc ArithmeticFunction.vonMangoldt n / Real.sqrt n *
          (‖kern a (Real.log n)‖ + ‖kern a (-Real.log n)‖)
        ≤ (2 / Real.exp 1) * (2 * Kc a) :=
          mul_le_mul hΛ (by unfold Kc at hK0 ⊢; linarith) (by positivity) (by positivity)
      _ = 2 * Kc a * (2 / Real.exp 1) := by ring
  refine (sum_le_sum hterm).trans ?_
  rw [sum_const, card_range, nsmul_eq_mul]
  push_cast; ring_nf; rfl

/-- **Non-unit weight.** -/
theorem nonunitWt_le {q : ℕ} [NeZero q] {a y : ℝ} (ha : 0 ≤ a) :
    nonunitWt q a y ≤ Kc a * Real.exp (a - y / 2) * (Real.log q * Nat.log 2 (cutoff a y)) := by
  unfold nonunitWt
  set M := cutoff a y
  have hpt : ∀ n ∈ (range M).filter (fun n ↦ ¬ Nat.Coprime n q),
      |wt a y n| ≤ Kc a * Real.exp (a - y / 2) * ArithmeticFunction.vonMangoldt n := by
    intro n _
    have hΛ0 := ArithmeticFunction.vonMangoldt_nonneg (n := n)
    by_cases hk : kern a (Real.log n - y) = 0
    · simp only [wt, hk, Complex.zero_re, mul_zero, zero_div, abs_zero]
      exact mul_nonneg (mul_nonneg (le_trans (norm_nonneg _) (norm_kern_le ha
        (u := 0) (by simp; linarith))) (Real.exp_pos _).le) hΛ0
    have hu : |Real.log n - y| ≤ 2 * a := by
      by_contra h; push_neg at h; exact hk (kern_eq_zero h)
    rcases Nat.eq_zero_or_pos n with rfl | hn0
    · simp [wt]
    have hnr : (0 : ℝ) < n := by exact_mod_cast hn0
    have hsq : Real.exp (y / 2 - a) ≤ Real.sqrt n := by
      have hlow : y - 2 * a ≤ Real.log n := by linarith [neg_abs_le (Real.log n - y)]
      rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hnr]
      exact Real.exp_le_exp.mpr (by linarith)
    have hsqpos : 0 < Real.sqrt n := Real.sqrt_pos.mpr hnr
    have hinv : 1 / Real.sqrt n ≤ Real.exp (a - y / 2) := by
      rw [div_le_iff₀ hsqpos, show a - y / 2 = -(y / 2 - a) by ring, Real.exp_neg]
      rw [inv_mul_eq_div, le_div_iff₀ (Real.exp_pos _), one_mul]; exact hsq
    have hkK : |(kern a (Real.log n - y)).re| ≤ Kc a :=
      (Complex.abs_re_le_norm _).trans (norm_kern_le ha hu)
    unfold wt
    rw [abs_div, abs_mul, abs_of_nonneg hΛ0, abs_of_pos hsqpos]
    calc ArithmeticFunction.vonMangoldt n * |(kern a (Real.log n - y)).re| / Real.sqrt n
        = ArithmeticFunction.vonMangoldt n * |(kern a (Real.log n - y)).re| * (1 / Real.sqrt n) := by
          ring
      _ ≤ ArithmeticFunction.vonMangoldt n * Kc a * Real.exp (a - y / 2) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hkK hΛ0) hinv (by positivity)
            (mul_nonneg hΛ0 (le_trans (abs_nonneg _) hkK))
      _ = Kc a * Real.exp (a - y / 2) * ArithmeticFunction.vonMangoldt n := by ring
  refine (sum_le_sum hpt).trans ?_
  rw [← mul_sum]
  have hK0 : 0 ≤ Kc a := le_trans (norm_nonneg _) (norm_kern_le ha (u := 0) (by simp; linarith))
  refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hK0 (Real.exp_pos _).le)
  -- range vs Ioo: they differ only at `n = 0`, where `Λ 0 = 0`
  have heq : ∑ n ∈ (range M).filter (fun n ↦ ¬ Nat.Coprime n q), ArithmeticFunction.vonMangoldt n =
      ∑ n ∈ (Ioo 0 M).filter (fun n ↦ ¬ Nat.Coprime n q), ArithmeticFunction.vonMangoldt n := by
    symm
    refine sum_subset (fun n hn ↦ ?_) (fun n hn hn' ↦ ?_)
    · simp only [mem_filter, mem_Ioo, mem_range] at hn ⊢; exact ⟨hn.1.2, hn.2⟩
    · simp only [mem_filter, mem_Ioo, mem_range, not_and] at hn hn'
      have : n = 0 := by by_contra h0; exact hn' ⟨Nat.pos_of_ne_zero h0, hn.1⟩ hn.2
      simp [this]
  rw [heq]
  exact GRHPseudo.sum_vonMangoldt_nonunit_le M

end GRHPseudo.Sharp
