import GRHPseudo.AnalyticNumberTheory.Sharp.GammaBounds

/-!
# Prime sides as finite sums for compactly supported kernels

If `K(u) = 0` for `|u| > L`, then:
* untwisted, the prime side only involves `n ≤ e^L`;
* twisted with `y > L`, the conjugate leg `K(−log n − y)` vanishes for every `n` (including
  `n = 0`, where Lean's `log 0 = 0`), and only `n ≤ e^{y+L}` contribute.
-/

noncomputable section

open Complex Finset
open scoped ComplexConjugate

namespace GRHPseudo.Sharp

variable {K : ℝ → ℂ} {L : ℝ}

lemma log_natCast_nonneg' (n : ℕ) : 0 ≤ Real.log n := Real.log_natCast_nonneg n

lemma log_gt_of_ge_floor_succ {n : ℕ} {t : ℝ} (hn : ⌊Real.exp t⌋₊ + 1 ≤ n) : t < Real.log n := by
  have h1 : Real.exp t < n := by
    have := Nat.lt_floor_add_one (Real.exp t)
    calc Real.exp t < ⌊Real.exp t⌋₊ + 1 := this
      _ ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := lt_trans (Real.exp_pos t) h1
  exact (Real.lt_log_iff_exp_lt hn0).mpr h1

/-- Twisted prime side as a finite sum. -/
theorem primeSide_twist_eq_sum (c : ℕ → ℂ) (hK : ∀ u, L < |u| → K u = 0) {y : ℝ} (hy : L < y) :
    primeSide c (twist K y) = ∑ n ∈ range (⌊Real.exp (y + L)⌋₊ + 1),
      ((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ) * (c n * K (Real.log n - y)) := by
  unfold primeSide twist
  have hleg : ∀ n : ℕ, K (-Real.log n - y) = 0 := by
    intro n
    apply hK
    have := neg_le_abs (-Real.log n - y)
    linarith [log_natCast_nonneg' n]
  simp_rw [hleg, mul_zero, add_zero]
  refine tsum_eq_sum fun n hn ↦ ?_
  rw [mem_range, not_lt] at hn
  have := log_gt_of_ge_floor_succ hn
  have habs := le_abs_self (Real.log n - y)
  rw [hK _ (by linarith), mul_zero, mul_zero]

/-- Untwisted prime side as a finite sum. -/
theorem primeSide_eq_sum (c : ℕ → ℂ) (hK : ∀ u, L < |u| → K u = 0) :
    primeSide c K = ∑ n ∈ range (⌊Real.exp L⌋₊ + 1),
      ((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ)
        * (c n * K (Real.log n) + conj (c n) * K (-Real.log n)) := by
  unfold primeSide
  refine tsum_eq_sum fun n hn ↦ ?_
  rw [mem_range, not_lt] at hn
  have h := log_gt_of_ge_floor_succ hn
  have h1 := le_abs_self (Real.log n)
  have h2 : |(-Real.log n)| = |Real.log n| := abs_neg _
  rw [hK _ (by linarith), hK _ (by rw [h2]; linarith), mul_zero, mul_zero, add_zero, mul_zero]

lemma primeSideZeta_eq (K : ℝ → ℂ) : primeSideZeta K = primeSide (fun _ ↦ 1) K := by
  unfold primeSideZeta primeSide
  congr 1; funext n; simp

end GRHPseudo.Sharp
