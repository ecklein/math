import GRHPseudo.AnalyticNumberTheory.Sharp.Certificate

/-!
# A concrete certificate: bias ≤ 1/2 for every modulus `q ≤ 2^64`

Parameters: `a = 1`, `y = 2 log 150` (so `x = 22500`). The sample space is the prime powers
`n ≤ ⌊22500 e²⌋ ≈ 166254` coprime to `q`, with weights `Λ(n) k_1(log n − y)/√n`; only
`n ∈ [22500 e^{−2}, 22500 e²] ≈ [3045, 166254]` carry weight.

`numB ≤ 236.6` and `denB ≥ 555.8` are derived from Mathlib's certified bounds
`2.7182818283 < e < 2.7182818286`, `3.141592 < π < 3.141593` and `log 2 < 0.6931471808`, so
`bias ≤ 236.6/555.8 < 1/2`.
-/

noncomputable section

open Real

namespace GRHPseudo.Sharp

/-- The twist parameter `y = 2 log 150`. -/
def y150 : ℝ := 2 * Real.log 150

lemma exp_y150_half : Real.exp (y150 / 2) = 150 := by
  unfold y150; rw [show 2 * Real.log 150 / 2 = Real.log 150 by ring, Real.exp_log (by norm_num)]

lemma two_lt_y150 : 2 * 1 < y150 := by
  unfold y150
  have : 1 < Real.log 150 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num)]
    have := Real.exp_one_lt_d9; linarith
  linarith

/-! ### Shared numerical lemmas -/

lemma e_bounds : 2.7182818283 < Real.exp 1 ∧ Real.exp 1 < 2.7182818286 :=
  ⟨Real.exp_one_gt_d9, Real.exp_one_lt_d9⟩

lemma Kc_one : Kc 1 = Real.exp 1 := by
  unfold Kc; rw [Real.sinh_eq, Real.cosh_eq, one_mul]; ring

lemma inv_e_bounds : 0.3678794411 ≤ (Real.exp 1)⁻¹ ∧ (Real.exp 1)⁻¹ ≤ 0.3678794413 := by
  obtain ⟨h1, h2⟩ := e_bounds
  have h0 : 0 < Real.exp 1 := Real.exp_pos 1
  exact ⟨by rw [le_inv_comm₀ (by norm_num) h0]; linarith,
    by rw [inv_le_comm₀ h0 (by norm_num)]; linarith⟩

lemma sinh_one_add_one_le : Real.sinh 1 + 1 ≤ 2.1752012 := by
  rw [Real.sinh_eq, Real.exp_neg]
  have := e_bounds.2; have := inv_e_bounds.1; linarith

lemma sinh_one_add_one_nonneg : 0 ≤ Real.sinh 1 + 1 := by
  have := Real.sinh_nonneg_iff.mpr (zero_le_one : (0 : ℝ) ≤ 1); linarith

lemma Cc_one_le : Cc 1 ≤ 15.219 := by
  set s := Real.exp (1 / 2) with hsdef
  have hs0 : 0 < s := Real.exp_pos _
  have hss : s * s = Real.exp 1 := by rw [hsdef, ← Real.exp_add]; norm_num
  obtain ⟨hE1, hE2⟩ := e_bounds
  have hs1 : s < 1.6488 := by nlinarith
  have hs2 : 1 < s := by nlinarith
  have hsinv : 0.6065 ≤ s⁻¹ := by rw [le_inv_comm₀ (by norm_num) hs0]; linarith
  have hsinv' : s⁻¹ < 1 := inv_lt_one_of_one_lt₀ hs2
  unfold Cc
  rw [Real.sinh_eq, Real.cosh_eq, Real.exp_neg, ← hsdef]
  have hd : 0 ≤ s - s⁻¹ := by linarith
  have hd2 : s - s⁻¹ ≤ 1.0423 := by linarith
  have e1 : (4 * ((s - s⁻¹) / 2)) ^ 2 + (2 * ((s - s⁻¹) / 2) + 2 * ((s + s⁻¹) / 2)) ^ 2 =
      4 * (s - s⁻¹) ^ 2 + 4 * (s * s) := by ring
  rw [e1, hss]
  have hsq : (s - s⁻¹) ^ 2 ≤ 1.0423 ^ 2 := pow_le_pow_left₀ hd hd2 2
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

lemma natLog_cutoff_le : Nat.log 2 (cutoff 1 y150) ≤ 17 := by
  have hxe : Real.exp (y150 + 2 * 1) = 150 * 150 * (Real.exp 1 * Real.exp 1) := by
    unfold y150
    rw [show 2 * Real.log 150 + 2 * 1 = Real.log 150 + Real.log 150 + (1 + 1) by ring,
      Real.exp_add, Real.exp_add, Real.exp_add, Real.exp_log (by norm_num)]
  have hE2 := e_bounds.2
  have hE0 : 0 < Real.exp 1 := Real.exp_pos 1
  have hEE : Real.exp 1 * Real.exp 1 < 7.39 := by nlinarith
  have hfl : ⌊Real.exp (y150 + 2 * 1)⌋₊ < 262143 := by
    rw [Nat.floor_lt (Real.exp_pos _).le, hxe]; push_cast; linarith
  have hc : cutoff 1 y150 < 2 ^ 18 := by
    rw [show (2 : ℕ) ^ 18 = 262144 by norm_num]; unfold cutoff; omega
  have := Nat.log_lt_of_lt_pow (by unfold cutoff; omega) hc
  omega

lemma UB_le {q : ℕ} [NeZero q] (hq : q ≤ 2 ^ 64) : UB q 1 y150 ≤ 37.15 := by
  unfold UB
  rw [Kc_one]
  have hexp : Real.exp (1 - y150 / 2) = Real.exp 1 / 150 := by
    rw [Real.exp_sub, exp_y150_half]
  rw [hexp]
  have hE2 := e_bounds.2
  have hE0 : 0 < Real.exp 1 := Real.exp_pos 1
  have hL := log_q_le hq
  have hL0 := log_q_nonneg q
  have hn : ((Nat.log 2 (cutoff 1 y150) : ℕ) : ℝ) ≤ 17 := by exact_mod_cast natLog_cutoff_le
  have hn0 : (0 : ℝ) ≤ (Nat.log 2 (cutoff 1 y150) : ℕ) := Nat.cast_nonneg _
  have hLn : Real.log q * (Nat.log 2 (cutoff 1 y150) : ℕ) ≤ 44.3614197 * 17 :=
    mul_le_mul hL hn hn0 (by norm_num)
  have hLn0 : 0 ≤ Real.log q * (Nat.log 2 (cutoff 1 y150) : ℕ) := mul_nonneg hL0 hn0
  have hEE : Real.exp 1 * (Real.exp 1 / 150) ≤ 2.7182818286 * (2.7182818286 / 150) :=
    mul_le_mul hE2.le (by linarith) (by positivity) (by norm_num)
  calc Real.exp 1 * (Real.exp 1 / 150) * (Real.log q * (Nat.log 2 (cutoff 1 y150) : ℕ))
      ≤ (2.7182818286 * (2.7182818286 / 150)) * (44.3614197 * 17) :=
        mul_le_mul hEE hLn hLn0 (by norm_num)
    _ ≤ 37.15 := by norm_num

lemma pi_six_div_le : 6 / π ≤ 1.90986 := by
  rw [div_le_iff₀ Real.pi_pos]; have := Real.pi_gt_d6; linarith

/-! ### The two bounds -/

variable {q : ℕ} [NeZero q]

theorem numB_le (hq : q ≤ 2 ^ 64) : numB q 1 y150 ≤ 236.6 := by
  have hT1 : (Real.sinh 1 + 1) * Real.log q ≤ 2.1752012 * 44.3614197 :=
    mul_le_mul sinh_one_add_one_le (log_q_le hq) (log_q_nonneg q) (by norm_num)
  have hfl : (⌊Real.exp (2 * 1)⌋₊ : ℝ) + 1 ≤ 8 := by
    have he2 : Real.exp (2 * 1) = Real.exp 1 * Real.exp 1 := by
      rw [show (2 : ℝ) * 1 = 1 + 1 by ring, Real.exp_add]
    have hE2 := e_bounds.2
    have hE0 : 0 < Real.exp 1 := Real.exp_pos 1
    have hlt : ⌊Real.exp (2 * 1)⌋₊ < 8 := by
      rw [Nat.floor_lt (Real.exp_pos _).le, he2]; push_cast; nlinarith
    have : (⌊Real.exp (2 * 1)⌋₊ : ℝ) ≤ 7 := by exact_mod_cast Nat.lt_succ_iff.mp hlt
    linarith
  have hT2 : 2 * Kc 1 * (2 / Real.exp 1) * (⌊Real.exp (2 * 1)⌋₊ + 1) ≤ 32 := by
    rw [Kc_one, show 2 * Real.exp 1 * (2 / Real.exp 1) = 4 by
      field_simp [(Real.exp_pos 1).ne']; ring]
    linarith
  have hT3 : (Cc 1 * (6 + 5 * π) + Cc 1 * (6 + 1 / 2 * π)) / (2 * π) ≤ 70.92 := by
    have e : (Cc 1 * (6 + 5 * π) + Cc 1 * (6 + 1 / 2 * π)) / (2 * π) =
        Cc 1 * (6 / π + 11 / 4) := by field_simp; ring
    rw [e]
    have hin : 6 / π + 11 / 4 ≤ 4.65986 := by have := pi_six_div_le; linarith
    have hin0 : 0 ≤ 6 / π + 11 / 4 := by positivity
    calc Cc 1 * (6 / π + 11 / 4) ≤ 15.219 * 4.65986 :=
          mul_le_mul Cc_one_le hin hin0 (by norm_num)
      _ ≤ 70.92 := by norm_num
  have hT4 := UB_le hq
  unfold numB
  have : (2.1752012 : ℝ) * 44.3614197 ≤ 96.4951 := by norm_num
  linarith

theorem denB_ge (hq : q ≤ 2 ^ 64) : 555.8 ≤ denB q 1 y150 := by
  obtain ⟨hE1, hE2⟩ := e_bounds
  obtain ⟨hinv1, hinv2⟩ := inv_e_bounds
  have hE0 : 0 < Real.exp 1 := Real.exp_pos 1
  have h64a : Real.exp (-(1 / 64)) ≥ 63 / 64 := by
    have := Real.add_one_le_exp (-(1 / 64 : ℝ)); linarith
  have h64b : Real.exp (1 / 64) ≤ 64 / 63 := by
    have hpos : 0 < Real.exp (-(1 / 64)) := Real.exp_pos _
    have hprod : Real.exp (1 / 64) * Real.exp (-(1 / 64)) = 1 := by
      rw [← Real.exp_add]; norm_num
    rw [show (64 / 63 : ℝ) = 1 / (63 / 64) by norm_num, le_div_iff₀ (by norm_num)]
    nlinarith
  have ht : Real.exp (1 - 1 / 64) ≥ Real.exp 1 * (63 / 64) := by
    rw [sub_eq_add_neg, Real.exp_add]
    exact mul_le_mul_of_nonneg_left h64a hE0.le
  have htinv : Real.exp (-(1 - 1 / 64)) ≤ (64 / 63) * (Real.exp 1)⁻¹ := by
    rw [show -(1 - 1 / 64 : ℝ) = 1 / 64 + -1 by ring, Real.exp_add, Real.exp_neg]
    exact mul_le_mul_of_nonneg_right h64b (inv_nonneg.mpr hE0.le)
  have hsh : Real.sinh (1 - 1 / 64) + (1 - 1 / 64) ≥ 2.1354 := by
    rw [Real.sinh_eq]; linarith
  have hA : (Real.sinh (1 - 1 / 64) + (1 - 1 / 64)) ^ 2 ≥ 4.5599 := by nlinarith
  have hT1 : Real.exp (y150 / 2) * (Real.sinh (1 - 1 / 64) + (1 - 1 / 64)) ^ 2 ≥ 683.98 := by
    rw [exp_y150_half]; linarith
  have hT2 : 2 * (Real.sinh 1 + 1) ^ 2 ≤ 9.4631 := by
    have h := sinh_one_add_one_le; have h0 := sinh_one_add_one_nonneg
    have : (Real.sinh 1 + 1) ^ 2 ≤ 2.1752012 ^ 2 := pow_le_pow_left₀ h0 h 2
    linarith
  have hπ0 : 0 < π := Real.pi_pos
  have hlogπ : Real.log π ≤ 1.3862944 := by
    have h4 : Real.log π ≤ Real.log 4 := Real.log_le_log hπ0 (by linarith [Real.pi_lt_d6])
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow] at h4
    have := Real.log_two_lt_d9; push_cast at h4; linarith
  have hlogπ0 : 0 ≤ Real.log π := Real.log_nonneg (by linarith [Real.pi_gt_d6])
  have hT3 : (Cc 1 * (6 + (5 + Real.log π) * π) + Cc 1 * (6 + 1 / 2 * π)) / (2 * π) ≤ 81.47 := by
    have e : (Cc 1 * (6 + (5 + Real.log π) * π) + Cc 1 * (6 + 1 / 2 * π)) / (2 * π) =
        Cc 1 * (6 / π + (11 / 2 + Real.log π) / 2) := by field_simp; ring
    rw [e]
    have hin : 6 / π + (11 / 2 + Real.log π) / 2 ≤ 5.35301 := by
      have := pi_six_div_le; linarith
    have hin0 : 0 ≤ 6 / π + (11 / 2 + Real.log π) / 2 := by positivity
    calc Cc 1 * (6 / π + (11 / 2 + Real.log π) / 2) ≤ 15.219 * 5.35301 :=
          mul_le_mul Cc_one_le hin hin0 (by norm_num)
      _ ≤ 81.47 := by norm_num
  have hT4 := UB_le hq
  unfold denB
  linarith

/-- **Certificate (conditional form).** -/
theorem bias_le_half_of_le_two_pow_64' (hZ : GRHMiller.DirichletLZerosOnLine)
    (hRH : RiemannHypothesis) (hq : q ≤ 2 ^ 64) {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) :
    bias (sampleSpace q 1 y150) (wt 1 y150) χ ≤ 1 / 2 := by
  have hD := denB_ge hq
  have hN := numB_le hq
  have hpos : 0 < denB q 1 y150 := by linarith
  refine (bias_closed hZ hRH hχ le_rfl two_lt_y150 hpos).trans ?_
  rw [div_le_iff₀ hpos]
  linarith

end GRHPseudo.Sharp
