import GRHPseudo.AnalyticNumberTheory.Sharp.ConvAssembly
import GRHPseudo.AnalyticNumberTheory.Sharp.GammaSharp
import GRHPseudo.Pseudorandomness.PrimeMeasure

/-!
# Closed form and a certificate for the convolution-square kernel

**Closed form** (`bias_closed`). For `A ≥ 1/32`, `R > 0` and `y > 2A`, `bias ≤ numB/denB` whenever
`denB > 0`, where, with `G(B) = (log(4+R) + B)(1 − e^{−A}) + 36/(πR)` and
`U_B = A e^{−y/2} log q · log₂(⌊e^y⌋ + 1)`,

    numB = (1 − e^{−A}) log q + (2/e)(⌊e^A⌋ + 1) + G(5) + G(1/2) + U_B,
    denB = e^{y/2} (e^{−1/64} − e^{−A+1/64})² − 2A − G(5 + log π) − G(1/2) − U_B.

**Certificate** (`bias_le_half_of_le_two_pow_64'`): `A = 9/4`, `R = 12`, `y = 2 log 220`
(`x = 48400`). For every `q ≤ 2^64`, `numB ≤ 65.7` and `denB ≥ 143.9`, so `bias ≤ 0.4566 < 1/2`.
The weights live on prime powers `n ∈ [48400 e^{−9/2}, 48400] ≈ [538, 48400]`.
-/

noncomputable section

open Complex Finset Zeta23 Zeta23.EF
open scoped Real

namespace GRHPseudo.Sharp.Conv

/-- Gamma-side constant `G(B) = (log(4+R) + B)(1 − e^{−A}) + 36/(πR)`. -/
def G (A R B : ℝ) : ℝ := (Real.log (4 + R) + B) * (1 - Real.exp (-A)) + 36 / (π * R)

/-- Closed-form non-unit bound. -/
def UB (q : ℕ) (A y : ℝ) : ℝ := A * Real.exp (-(y / 2)) * (Real.log q * Nat.log 2 (cutoff y))

/-- Closed-form numerator. -/
def numB (q : ℕ) (A y R : ℝ) : ℝ :=
  (1 - Real.exp (-A)) * Real.log q + 2 / Real.exp 1 * (⌊Real.exp A⌋₊ + 1) +
    G A R 5 + G A R (1 / 2) + UB q A y

/-- Closed-form denominator. -/
def denB (q : ℕ) (A y R : ℝ) : ℝ :=
  Real.exp (y / 2) * (Real.exp (-(1 / 64)) - Real.exp (-A + 1 / 64)) ^ 2 - 2 * A -
    G A R (5 + Real.log π) - G A R (1 / 2) - UB q A y

variable {A R : ℝ}

lemma Ilog_div_le_G (hA : 1 / 64 ≤ A) (hR : 0 < R) {B : ℝ} (hB : 0 ≤ B) :
    Ilog (f A) B / (2 * π) ≤ G A R B := by
  have h := Ilog_div_le_sharp (contDiff_f A) (hasCompactSupport_f A) hR hB
    (norm_paperFT_f_mul_le hA)
  have hM := M_zero_le (A := A) (by linarith)
  have hc : 0 ≤ Real.log (4 + R) + B := add_nonneg (Real.log_nonneg (by linarith)) hB
  have hW : (weilTest (f A) (f A) 0).re = (M A 0).re := rfl
  rw [hW] at h
  have h2 := mul_le_mul_of_nonneg_left hM hc
  have h3 : 4 * (3 : ℝ) ^ 2 / (π * R) = 36 / (π * R) := by norm_num
  unfold G
  linarith

/-- `log n / n ≤ 1/e`. -/
lemma log_div_self_le (n : ℕ) : Real.log n / n ≤ 1 / Real.exp 1 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp; positivity
  have hx : (0 : ℝ) < n := by exact_mod_cast hn
  have he : 0 < Real.exp 1 := Real.exp_pos 1
  have key : Real.log n ≤ n / Real.exp 1 := by
    have := Real.log_le_sub_one_of_pos (div_pos hx he)
    rw [Real.log_div hx.ne' he.ne', Real.log_exp] at this
    linarith
  rw [div_le_div_iff₀ hx he]
  have := (le_div_iff₀ he).mp key
  linarith

/-- **Small-prime sum.** -/
theorem smallPrimes_le (hA : 0 ≤ A) : smallPrimes A ≤ 2 / Real.exp 1 * (⌊Real.exp A⌋₊ + 1) := by
  unfold smallPrimes
  have hterm : ∀ n ∈ range (⌊Real.exp A⌋₊ + 1), ArithmeticFunction.vonMangoldt n / Real.sqrt n *
      (‖M A (Real.log n)‖ + ‖M A (-Real.log n)‖) ≤ 2 / Real.exp 1 := by
    intro n _
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp; positivity
    have hnr : (0 : ℝ) < n := by exact_mod_cast hn
    have hsq : 0 < Real.sqrt n := Real.sqrt_pos.mpr hnr
    have hlog0 : 0 ≤ Real.log n := Real.log_natCast_nonneg n
    have hexp : Real.exp (-(Real.log n / 2)) = 1 / Real.sqrt n := by
      rw [Real.exp_neg, GRHMiller.exp_log_div_two hnr, one_div]
    have hM1 : ‖M A (Real.log n)‖ ≤ 1 / Real.sqrt n := by
      have := norm_M_le hA (Real.log n)
      rwa [abs_of_nonneg hlog0, hexp] at this
    have hM2 : ‖M A (-Real.log n)‖ ≤ 1 / Real.sqrt n := by
      have := norm_M_le hA (-Real.log n)
      rwa [abs_neg, abs_of_nonneg hlog0, hexp] at this
    have hΛ0 := ArithmeticFunction.vonMangoldt_nonneg (n := n)
    have hΛ : ArithmeticFunction.vonMangoldt n ≤ Real.log n := ArithmeticFunction.vonMangoldt_le_log
    have hsum : ‖M A (Real.log n)‖ + ‖M A (-Real.log n)‖ ≤ 2 / Real.sqrt n := by
      have : (2 : ℝ) / Real.sqrt n = 1 / Real.sqrt n + 1 / Real.sqrt n := by ring
      linarith
    calc ArithmeticFunction.vonMangoldt n / Real.sqrt n * (‖M A (Real.log n)‖ + ‖M A (-Real.log n)‖)
        ≤ ArithmeticFunction.vonMangoldt n / Real.sqrt n * (2 / Real.sqrt n) :=
          mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = 2 * (ArithmeticFunction.vonMangoldt n / n) := by
          rw [div_mul_div_comm, Real.mul_self_sqrt hnr.le]; ring
      _ ≤ 2 * (Real.log n / n) := by gcongr
      _ ≤ 2 / Real.exp 1 := by have := log_div_self_le n; rw [div_eq_mul_one_div 2]; linarith
  refine (sum_le_sum hterm).trans ?_
  rw [sum_const, card_range, nsmul_eq_mul]
  push_cast; ring_nf; rfl

/-- **Non-unit weight.** -/
theorem nonunitWt_le {q : ℕ} [NeZero q] {y : ℝ} (hA : 0 ≤ A) :
    nonunitWt q A y ≤ UB q A y := by
  unfold nonunitWt UB
  set Mc := cutoff y
  have hpt : ∀ n ∈ (range Mc).filter (fun n ↦ ¬ Nat.Coprime n q),
      |wt A y n| ≤ A * Real.exp (-(y / 2)) * ArithmeticFunction.vonMangoldt n := by
    intro n _
    have hΛ0 := ArithmeticFunction.vonMangoldt_nonneg (n := n)
    rcases Nat.eq_zero_or_pos n with rfl | hn0
    · simp [wt]
    have hnr : (0 : ℝ) < n := by exact_mod_cast hn0
    have hsq : 0 < Real.sqrt n := Real.sqrt_pos.mpr hnr
    have hK0 := K_re_nonneg A (Real.log n - y)
    have hKle := K_le hA (Real.log n - y)
    have he : Real.exp ((Real.log n - y) / 2) = Real.sqrt n * Real.exp (-(y / 2)) := by
      rw [show (Real.log n - y) / 2 = Real.log n / 2 + -(y / 2) by ring, Real.exp_add,
        GRHMiller.exp_log_div_two hnr]
    rw [he] at hKle
    unfold wt
    rw [abs_of_nonneg (div_nonneg (mul_nonneg hΛ0 hK0) hsq.le), div_le_iff₀ hsq]
    calc ArithmeticFunction.vonMangoldt n * (K A (Real.log n - y)).re
        ≤ ArithmeticFunction.vonMangoldt n * (A * (Real.sqrt n * Real.exp (-(y / 2)))) :=
          mul_le_mul_of_nonneg_left hKle hΛ0
      _ = A * Real.exp (-(y / 2)) * ArithmeticFunction.vonMangoldt n * Real.sqrt n := by ring
  refine (sum_le_sum hpt).trans ?_
  rw [← mul_sum]
  refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hA (Real.exp_pos _).le)
  have heq : ∑ n ∈ (range Mc).filter (fun n ↦ ¬ Nat.Coprime n q), ArithmeticFunction.vonMangoldt n =
      ∑ n ∈ (Ioo 0 Mc).filter (fun n ↦ ¬ Nat.Coprime n q), ArithmeticFunction.vonMangoldt n := by
    symm
    refine sum_subset (fun n hn ↦ ?_) (fun n hn hn' ↦ ?_)
    · simp only [mem_filter, mem_Ioo, mem_range] at hn ⊢; exact ⟨hn.1.2, hn.2⟩
    · simp only [mem_filter, mem_Ioo, mem_range, not_and] at hn hn'
      have : n = 0 := by by_contra h0; exact hn' ⟨Nat.pos_of_ne_zero h0, hn.1⟩ hn.2
      simp [this]
  rw [heq]
  exact GRHPseudo.sum_vonMangoldt_nonunit_le Mc

variable {q : ℕ} [NeZero q]

lemma sharpNum_le {y : ℝ} (hA : 1 / 64 ≤ A) (hR : 0 < R) : sharpNum q A y ≤ numB q A y R := by
  have hA0 : 0 ≤ A := by linarith
  unfold sharpNum numB
  have hk0 : (M A 0).re ≤ 1 - Real.exp (-A) := M_zero_le hA0
  have hk00 : 0 ≤ (M A 0).re := M_re_nonneg A 0
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hlogq : 0 ≤ Real.log q := Real.log_nonneg hq1
  have hlogπ : 0 ≤ Real.log π := Real.log_nonneg (by linarith [Real.pi_gt_three])
  have hlogqπ : Real.log (q / π) ≤ Real.log q := by
    rw [Real.log_div (by positivity) Real.pi_ne_zero]; linarith
  have h1 : (M A 0).re * Real.log (q / π) ≤ (1 - Real.exp (-A)) * Real.log q :=
    (mul_le_mul_of_nonneg_left hlogqπ hk00).trans (mul_le_mul_of_nonneg_right hk0 hlogq)
  have h2 := smallPrimes_le hA0
  have h3 := Ilog_div_le_G hA hR (by norm_num : (0 : ℝ) ≤ 5)
  have h4 := Ilog_div_le_G hA hR (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have h5 := nonunitWt_le (q := q) (y := y) hA0
  have hdiv : (Ilog (f A) 5 + Ilog (f A) (1 / 2)) / (2 * π) =
      Ilog (f A) 5 / (2 * π) + Ilog (f A) (1 / 2) / (2 * π) := add_div _ _ _
  linarith

lemma denB_le {y : ℝ} (hA : 1 / 32 ≤ A) (hR : 0 < R) : denB q A y R ≤ sharpDen q A y := by
  have hA0 : 0 ≤ A := by linarith
  unfold sharpDen denB
  have hlogπ : 0 ≤ Real.log π := Real.log_nonneg (by linarith [Real.pi_gt_three])
  have hlb := Fp_ge hA
  have hlb0 : 0 ≤ Real.exp (-(1 / 64)) - Real.exp (-A + 1 / 64) := by
    have := Real.exp_le_exp.mpr (show -A + 1 / 64 ≤ -(1 / 64) by linarith); linarith
  have hsq := pow_le_pow_left₀ hlb0 hlb 2
  have hmain := mul_le_mul_of_nonneg_left hsq (Real.exp_pos (y / 2)).le
  have hpole : Fp A * Fm A ≤ A := by
    have := mul_le_mul (Fp_le_one hA0) (Fm_le hA0) (Fm_nonneg A) zero_le_one
    linarith
  have h3 := Ilog_div_le_G (A := A) (by linarith) hR (by positivity : (0 : ℝ) ≤ 5 + Real.log π)
  have h4 := Ilog_div_le_G (A := A) (by linarith) hR (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have h5 := nonunitWt_le (q := q) (y := y) hA0
  have hdiv : (Ilog (f A) (5 + Real.log π) + Ilog (f A) (1 / 2)) / (2 * π) =
      Ilog (f A) (5 + Real.log π) / (2 * π) + Ilog (f A) (1 / 2) / (2 * π) := add_div _ _ _
  linarith

/-- **Closed-form sharp bias theorem** for the convolution-square kernel (conditional on
zeros-on-line and RH). -/
theorem bias_closed (hZ : GRHMiller.DirichletLZerosOnLine) (hRH : RiemannHypothesis)
    {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) {y : ℝ} (hA : 1 / 32 ≤ A) (hR : 0 < R)
    (hy : 2 * A < y) (hden : 0 < denB q A y R) :
    bias (sampleSpace q y) (wt A y) χ ≤ numB q A y R / denB q A y R := by
  obtain ⟨hnum, hmass⟩ := sharp_charSum_mass hZ hRH hχ (by linarith) hy
  exact bias_le_of_bounds _ _ _ (hnum.trans (sharpNum_le (by linarith) hR)) hden
    ((denB_le hA hR).trans hmass)

/-! ### The certificate: `A = 9/4`, `R = 12`, `y = 2 log 220` -/

/-- The twist parameter `y = 2 log 220` (`x = 48400`). -/
def y220 : ℝ := 2 * Real.log 220

lemma exp_y220_half : Real.exp (y220 / 2) = 220 := by
  unfold y220; rw [show 2 * Real.log 220 / 2 = Real.log 220 by ring, Real.exp_log (by norm_num)]

lemma exp_y220 : Real.exp y220 = 48400 := by
  unfold y220
  rw [show 2 * Real.log 220 = Real.log 220 + Real.log 220 by ring, Real.exp_add,
    Real.exp_log (by norm_num)]
  norm_num

lemma cutoff_y220 : cutoff y220 = 48401 := by
  unfold cutoff; rw [exp_y220]
  have : ⌊(48400 : ℝ)⌋₊ = 48400 := Nat.floor_ofNat 48400
  rw [this]

lemma natLog_cutoff_y220 : Nat.log 2 (cutoff y220) ≤ 15 := by
  rw [cutoff_y220]
  have := Nat.log_lt_of_lt_pow (b := 2) (by norm_num : 48401 ≠ 0)
    (show 48401 < 2 ^ 16 by norm_num)
  omega

lemma exp_quarter_le : Real.exp (1 / 4) ≤ 1.2841 := by
  set s := Real.exp (1 / 4) with hs
  have hs0 : 0 < s := Real.exp_pos _
  have h4 : s * s * (s * s) = Real.exp 1 := by
    simp only [hs, ← Real.exp_add]; norm_num
  have he := Real.exp_one_lt_d9
  by_contra h
  push Not at h
  have h2 : 1.64891 < s * s := by nlinarith
  have : 2.71890 < s * s * (s * s) := by nlinarith
  linarith

lemma exp_A_le : Real.exp (9 / 4) ≤ 9.4885 := by
  have h : Real.exp (9 / 4) = Real.exp 1 * Real.exp 1 * Real.exp (1 / 4) := by
    rw [← Real.exp_add, ← Real.exp_add]; norm_num
  have he := Real.exp_one_lt_d9
  have he0 := Real.exp_pos 1
  have hq := exp_quarter_le
  have hq0 := Real.exp_pos (1 / 4)
  rw [h]
  have hee : Real.exp 1 * Real.exp 1 ≤ 2.7182818286 * 2.7182818286 :=
    mul_le_mul he.le he.le he0.le (by norm_num)
  calc Real.exp 1 * Real.exp 1 * Real.exp (1 / 4) ≤ (2.7182818286 * 2.7182818286) * 1.2841 :=
        mul_le_mul hee hq hq0.le (by norm_num)
    _ ≤ 9.4885 := by norm_num

lemma one_sub_exp_negA_le : 1 - Real.exp (-(9 / 4)) ≤ 0.89461 := by
  have h := exp_A_le
  have h0 := Real.exp_pos (9 / 4)
  have : (9.4885 : ℝ)⁻¹ ≤ Real.exp (-(9 / 4)) := by
    rw [Real.exp_neg]; exact inv_anti₀ h0 h
  have : (0.10539 : ℝ) ≤ (9.4885 : ℝ)⁻¹ := by norm_num
  linarith

lemma one_sub_exp_negA_nonneg : 0 ≤ 1 - Real.exp (-(9 / 4)) := by
  have := Real.exp_le_one_iff.mpr (show -(9 / 4 : ℝ) ≤ 0 by norm_num); linarith

lemma floor_exp_A_le : ⌊Real.exp (9 / 4)⌋₊ ≤ 9 := by
  have : ⌊Real.exp (9 / 4)⌋₊ < 10 := by
    rw [Nat.floor_lt (Real.exp_pos _).le]; have := exp_A_le; push_cast; linarith
  omega

lemma window_lb : 0.874735 ≤ Real.exp (-(1 / 64)) - Real.exp (-(9 / 4) + 1 / 64) := by
  have h1 : -(1 / 64 : ℝ) + 1 ≤ Real.exp (-(1 / 64)) := Real.add_one_le_exp _
  have hb : Real.exp (143 / 64) = Real.exp 1 * Real.exp 1 * Real.exp (15 / 64) := by
    rw [← Real.exp_add, ← Real.exp_add]; norm_num
  have h15 : (15 / 64 : ℝ) + 1 ≤ Real.exp (15 / 64) := Real.add_one_le_exp _
  have he := Real.exp_one_gt_d9
  have hee : 2.7182818283 * 2.7182818283 ≤ Real.exp 1 * Real.exp 1 :=
    mul_le_mul he.le he.le (by norm_num) (Real.exp_pos 1).le
  have hlow : 9.1208 ≤ Real.exp (143 / 64) := by
    rw [hb]
    calc (9.1208 : ℝ) ≤ (2.7182818283 * 2.7182818283) * (15 / 64 + 1) := by norm_num
      _ ≤ Real.exp 1 * Real.exp 1 * Real.exp (15 / 64) :=
          mul_le_mul hee h15 (by norm_num) (by positivity)
  have hneg : Real.exp (-(9 / 4) + 1 / 64) = (Real.exp (143 / 64))⁻¹ := by
    rw [← Real.exp_neg]; norm_num
  have : (Real.exp (143 / 64))⁻¹ ≤ (9.1208 : ℝ)⁻¹ := inv_anti₀ (by norm_num) hlow
  have : (9.1208 : ℝ)⁻¹ ≤ 0.109640 := by norm_num
  rw [hneg]; linarith

lemma log_four_add_R : Real.log (4 + 12) ≤ 2.7725887232 := by
  rw [show (4 + 12 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]
  have := Real.log_two_lt_d9; push_cast; linarith

lemma log_pi_le : Real.log π ≤ 1.3862943616 := by
  have h : Real.log π ≤ Real.log 4 := Real.log_le_log Real.pi_pos (by linarith [Real.pi_lt_d6])
  rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow] at h
  have := Real.log_two_lt_d9; push_cast at h; linarith

lemma G_le {B : ℝ} (hB : 0 ≤ B) : G (9 / 4) 12 B ≤ (2.7725887232 + B) * 0.89461 + 0.95493 := by
  unfold G
  have h1 := log_four_add_R
  have h2 := one_sub_exp_negA_le
  have h3 := one_sub_exp_negA_nonneg
  have hl0 : 0 ≤ Real.log (4 + 12) + B := add_nonneg (Real.log_nonneg (by norm_num)) hB
  have hm : (Real.log (4 + 12) + B) * (1 - Real.exp (-(9 / 4))) ≤ (2.7725887232 + B) * 0.89461 :=
    mul_le_mul (by linarith) h2 h3 (by linarith)
  have hp : 36 / (π * 12) ≤ 0.95493 := by
    rw [div_le_iff₀ (by positivity)]; nlinarith [Real.pi_gt_d6]
  linarith

lemma log_q_le {q : ℕ} [NeZero q] (hq : q ≤ 2 ^ 64) : Real.log q ≤ 44.3614197 := by
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have h1 : Real.log q ≤ Real.log ((2 : ℝ) ^ 64) :=
    Real.log_le_log (by linarith) (by exact_mod_cast hq)
  rw [Real.log_pow] at h1
  have := Real.log_two_lt_d9
  push_cast at h1; linarith

lemma log_q_nonneg (q : ℕ) [NeZero q] : 0 ≤ Real.log q :=
  Real.log_nonneg (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q))

lemma UB_le (hq : q ≤ 2 ^ 64) : UB q (9 / 4) y220 ≤ 6.8055 := by
  unfold UB
  have he : Real.exp (-(y220 / 2)) = 1 / 220 := by rw [Real.exp_neg, exp_y220_half]; norm_num
  rw [he]
  have hL := log_q_le hq
  have hL0 := log_q_nonneg q
  have hn : ((Nat.log 2 (cutoff y220) : ℕ) : ℝ) ≤ 15 := by exact_mod_cast natLog_cutoff_y220
  have hn0 : (0 : ℝ) ≤ (Nat.log 2 (cutoff y220) : ℕ) := Nat.cast_nonneg _
  have hLn : Real.log q * (Nat.log 2 (cutoff y220) : ℕ) ≤ 44.3614197 * 15 :=
    mul_le_mul hL hn hn0 (by norm_num)
  have hLn0 : 0 ≤ Real.log q * (Nat.log 2 (cutoff y220) : ℕ) := mul_nonneg hL0 hn0
  nlinarith

lemma two_div_e_le : 2 / Real.exp 1 ≤ 0.7357589 := by
  rw [div_le_iff₀ (Real.exp_pos 1)]; have := Real.exp_one_gt_d9; linarith

lemma numB_le (hq : q ≤ 2 ^ 64) : numB q (9 / 4) y220 12 ≤ 65.7 := by
  unfold numB
  have h1 := one_sub_exp_negA_le
  have h1' := one_sub_exp_negA_nonneg
  have hL := log_q_le hq
  have hL0 := log_q_nonneg q
  have hlead : (1 - Real.exp (-(9 / 4))) * Real.log q ≤ 0.89461 * 44.3614197 :=
    mul_le_mul h1 hL hL0 (by norm_num)
  have hfl : ((⌊Real.exp (9 / 4)⌋₊ : ℕ) : ℝ) + 1 ≤ 10 := by
    have := floor_exp_A_le; have : ((⌊Real.exp (9 / 4)⌋₊ : ℕ) : ℝ) ≤ 9 := by exact_mod_cast this
    linarith
  have hsp : 2 / Real.exp 1 * (⌊Real.exp (9 / 4)⌋₊ + 1) ≤ 0.7357589 * 10 :=
    mul_le_mul two_div_e_le hfl (by positivity) (by norm_num)
  have hG5 := G_le (by norm_num : (0 : ℝ) ≤ 5)
  have hGh := G_le (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hU := UB_le hq
  norm_num at hG5 hGh ⊢
  linarith

lemma denB_ge (hq : q ≤ 2 ^ 64) : 143.9 ≤ denB q (9 / 4) y220 12 := by
  unfold denB
  rw [exp_y220_half]
  have hw := window_lb
  have hsq : (0.874735 : ℝ) ^ 2 ≤ (Real.exp (-(1 / 64)) - Real.exp (-(9 / 4) + 1 / 64)) ^ 2 :=
    pow_le_pow_left₀ (by norm_num) hw 2
  have hlogπ := log_pi_le
  have hlogπ0 : 0 ≤ Real.log π := Real.log_nonneg (by linarith [Real.pi_gt_three])
  have hGp := G_le (B := 5 + Real.log π) (by positivity)
  have hGh := G_le (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hU := UB_le hq
  norm_num at hGh hsq ⊢
  nlinarith

/-- **Certificate (conditional form).** -/
theorem bias_le_half_of_le_two_pow_64' (hZ : GRHMiller.DirichletLZerosOnLine)
    (hRH : RiemannHypothesis) (hq : q ≤ 2 ^ 64) {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) :
    bias (sampleSpace q y220) (wt (9 / 4) y220) χ ≤ 1 / 2 := by
  have hden := denB_ge hq
  have hnum := numB_le hq
  have hy : 2 * (9 / 4 : ℝ) < y220 := by
    unfold y220
    have : (9 / 4 : ℝ) < Real.log 220 := by
      rw [Real.lt_log_iff_exp_lt (by norm_num)]; have := exp_A_le; linarith
    linarith
  have h := bias_closed hZ hRH hχ (by norm_num) (by norm_num : (0 : ℝ) < 12) hy
    (by linarith : 0 < denB q (9 / 4) y220 12)
  refine h.trans ?_
  rw [div_le_iff₀ (by linarith)]
  linarith

end GRHPseudo.Sharp.Conv
