import GRHPseudo.AnalyticNumberTheory.Sharp.ConstBounds

/-!
# Closed-form sharp bias theorem and a concrete certificate (Layer 2, part 3)

**Part A** (`bias_closed`). For `a ≥ 1` and `y > 2a`, `bias ≤ numB/denB` whenever `denB > 0`,
where `numB` and `denB` are elementary functions of `(q, a, y)`:

    numB = (sinh a + a) log q + 2K(2/e)(⌊e^{2a}⌋+1) + C(12 + (11/2)π)/(2π) + U_B,
    denB = e^{y/2}(sinh a' + a')² − 2(sinh a + a)² − C(12 + (11/2 + log π)π)/(2π) − U_B,

with `a' = a − 1/64`, `K = sinh a + a cosh a`, `C = (4 sinh(a/2))² + (2 sinh(a/2) + 2 cosh(a/2))²`,
and `U_B = K e^{a−y/2} log q · log₂⌊e^{y+2a}⌋+1`.
-/

noncomputable section

open Complex Finset
open scoped Real

namespace GRHPseudo.Sharp

/-- Closed-form non-unit bound. -/
def UB (q : ℕ) (a y : ℝ) : ℝ := Kc a * Real.exp (a - y / 2) * (Real.log q * Nat.log 2 (cutoff a y))

/-- Closed-form numerator. -/
def numB (q : ℕ) (a y : ℝ) : ℝ :=
  (Real.sinh a + a) * Real.log q + 2 * Kc a * (2 / Real.exp 1) * (⌊Real.exp (2 * a)⌋₊ + 1) +
    (Cc a * (6 + 5 * π) + Cc a * (6 + 1 / 2 * π)) / (2 * π) + UB q a y

/-- Closed-form denominator. -/
def denB (q : ℕ) (a y : ℝ) : ℝ :=
  Real.exp (y / 2) * (Real.sinh (a - 1 / 64) + (a - 1 / 64)) ^ 2 - 2 * (Real.sinh a + a) ^ 2 -
    (Cc a * (6 + (5 + Real.log π) * π) + Cc a * (6 + 1 / 2 * π)) / (2 * π) - UB q a y

variable {q : ℕ} [NeZero q]

lemma sharpNum_le {a y : ℝ} (ha : 1 ≤ a) : sharpNum q a y ≤ numB q a y := by
  have ha0 : 0 ≤ a := by linarith
  unfold sharpNum numB
  have hk0 : (kern a 0).re ≤ Real.sinh a + a := GRHMiller.Narrow.weilTest_testFnN_zero_le ha0
  have hk00 : 0 ≤ (kern a 0).re := kern_re_nonneg a 0
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hlogq : 0 ≤ Real.log q := Real.log_nonneg hq1
  have hlogπ : 0 ≤ Real.log π := Real.log_nonneg (by linarith [Real.pi_gt_three])
  have hlogqπ : Real.log (q / π) ≤ Real.log q := by
    rw [Real.log_div (by positivity) Real.pi_ne_zero]; linarith
  have h1 : (kern a 0).re * Real.log (q / π) ≤ (Real.sinh a + a) * Real.log q :=
    (mul_le_mul_of_nonneg_left hlogqπ hk00).trans (mul_le_mul_of_nonneg_right hk0 hlogq)
  have h2 := smallPrimes_le ha0
  have h3 := Ilog_le ha (by norm_num : (0 : ℝ) ≤ 5)
  have h4 := Ilog_le ha (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have h5 := nonunitWt_le (q := q) (y := y) ha0
  have hdiv : (Ilog (testF a) 5 + Ilog (testF a) (1 / 2)) / (2 * π) ≤
      (Cc a * (6 + 5 * π) + Cc a * (6 + 1 / 2 * π)) / (2 * π) :=
    div_le_div_of_nonneg_right (by linarith) (by positivity)
  unfold UB
  linarith

lemma denB_le {a y : ℝ} (ha : 1 ≤ a) : denB q a y ≤ sharpDen q a y := by
  have ha0 : 0 ≤ a := by linarith
  unfold sharpDen denB
  have hlogπ : 0 ≤ Real.log π := Real.log_nonneg (by linarith [Real.pi_gt_three])
  have h1 := mainA_ge a (by linarith)
  have h2 := poleB_le a (by linarith)
  have h3 := Ilog_le ha (by positivity : (0 : ℝ) ≤ 5 + Real.log π)
  have h4 := Ilog_le ha (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have h5 := nonunitWt_le (q := q) (y := y) ha0
  have hA : Real.exp (y / 2) * (Real.sinh (a - 1 / 64) + (a - 1 / 64)) ^ 2 ≤
      Real.exp (y / 2) * mainA a := mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
  have hdiv : (Ilog (testF a) (5 + Real.log π) + Ilog (testF a) (1 / 2)) / (2 * π) ≤
      (Cc a * (6 + (5 + Real.log π) * π) + Cc a * (6 + 1 / 2 * π)) / (2 * π) :=
    div_le_div_of_nonneg_right (by linarith) (by positivity)
  unfold UB
  linarith

/-- **Closed-form sharp bias theorem.** Conditional on zeros-on-line and RH. -/
theorem bias_closed (hZ : GRHMiller.DirichletLZerosOnLine) (hRH : RiemannHypothesis)
    {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) {a y : ℝ} (ha : 1 ≤ a) (hy : 2 * a < y)
    (hden : 0 < denB q a y) :
    bias (sampleSpace q a y) (wt a y) χ ≤ numB q a y / denB q a y := by
  obtain ⟨hnum, hmass⟩ := sharp_charSum_mass hZ hRH hχ (by linarith) hy
  exact bias_le_of_bounds _ _ _ (hnum.trans (sharpNum_le ha)) hden ((denB_le ha).trans hmass)

end GRHPseudo.Sharp
