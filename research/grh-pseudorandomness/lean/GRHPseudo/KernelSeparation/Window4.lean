import GRHPseudo.KernelSeparation.Kernel
import GRHPseudo.KernelSeparation.Data

/-!
# Window-4 kernel separation (paper Prop. 17(1), with the constant 9/8)

The witness `kernel4 u = ∑ⱼ kⱼ Λ((u − uⱼ)/h)`, `h = 1/20`, `uⱼ = −2 + (j+1)/20` (`j = 0, …, 78`), node values
`kData` (the `a = 1` LP kernel rounded to integers). It is continuous, nonnegative, supported in `[−2, 2]`, and

  `e^{T/2} (1/2π) ∫ |K̂| ≤ (9/8) ∫ K(u) e^{u/2} du`  with `T = 2`, and `9/8 < 1/(1 − e^{−2})`,

the optimum of the positivity method over convolution squares on windows of length 4 (paper Prop. 14, informal).
The informal certificate (`experiments/kernel_certificate.py`) gives the sharper `1.1082`; here the bound comes from the
majorant `|R|²/D ≥ |P|` (`certOK_data`) and is `≤ 1.1238` before rounding to `9/8`.

The same certificate is the instance of paper Prop. 18: `|K̂(t)| ≤ (h/D) Λ̂(ht) |R(e^{iht})|²`, the transform of the
positive-definite piecewise-linear majorant with node values `acf rData / D`, of degree 100.
-/

namespace GRHPseudo.KernelSeparation

open Complex MeasureTheory Real Set
open Zeta23 (paperFT)

/-- The witness kernel on `[−2, 2]`. -/
noncomputable def kernel4 : ℝ → ℝ := pwl (1 / 20) (-39 / 20) kData

lemma kData_length : kData.length = 79 := by decide +kernel

lemma kData_nonneg : ∀ x ∈ kData, 0 ≤ x := by decide +kernel

lemma hd_acf_rData : hd (acf rData) = 131068564 := by decide +kernel

lemma evR_nonneg {k : List ℤ} (hk : ∀ x ∈ k, 0 ≤ x) {x : ℝ} (hx : 0 ≤ x) : 0 ≤ evR k x := by
  induction k with
  | nil => exact le_rfl
  | cons a as ih =>
    have ha : (0 : ℝ) ≤ a := by exact_mod_cast hk a (by simp)
    exact add_nonneg ha (mul_nonneg hx (ih fun y hy => hk y (by simp [hy])))

lemma evR_mono {k : List ℤ} (hk : ∀ x ∈ k, 0 ≤ x) {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    evR k x ≤ evR k y := by
  induction k with
  | nil => exact le_rfl
  | cons a as ih =>
    have hk' : ∀ z ∈ as, 0 ≤ z := fun z hz => hk z (by simp [hz])
    simp only [evR]
    have := ih hk'
    have h0 := evR_nonneg hk' hx
    nlinarith

lemma evR_kData_lower : (2.7182818286 : ℝ) ^ 2 * (40 / 41) * (131068564 / 100)
    ≤ 9 / 160 * evR kData (3281 / 3200) := by
  simp only [kData, evR]
  norm_num

lemma continuous_kernel4 : Continuous kernel4 := continuous_pwl _ _ _

lemma kernel4_nonneg (u : ℝ) : 0 ≤ kernel4 u := pwl_nonneg _ _ _ kData_nonneg u

lemma kernel4_support {u : ℝ} (hu : kernel4 u ≠ 0) : u ∈ Icc (-2 : ℝ) 2 := by
  by_contra h
  rw [mem_Icc, not_and_or, not_le, not_le] at h
  apply hu
  refine pwl_eq_zero (by norm_num) _ _ ?_
  rw [kData_length]
  rcases h with h | h
  · left; linarith
  · right; push_cast; linarith

/-- Lemma 16 (second identity) for the witness: the mass with the exact correction factor. -/
lemma integral_kernel4_mul_exp :
    ∫ u : ℝ, kernel4 u * Real.exp (u / 2)
      = 1 / 20 * (Real.sinh (1 / 80) / (1 / 80)) ^ 2
          * (Real.exp (-39 / 40) * evR kData (Real.exp (1 / 40))) := by
  have := integral_pwl_mul_exp (h := 1 / 20) (by norm_num) (-39 / 20) kData
  simp only [kernel4]
  rw [this]; norm_num

lemma mass_kernel4_lower :
    1 / 20 * (Real.exp (-39 / 40) * evR kData (3281 / 3200))
      ≤ ∫ u : ℝ, kernel4 u * Real.exp (u / 2) := by
  rw [integral_kernel4_mul_exp]
  have hs : 1 ≤ (Real.sinh (1 / 80) / (1 / 80)) ^ 2 := by
    have : (1 / 80 : ℝ) ≤ Real.sinh (1 / 80) := Real.self_le_sinh_iff.2 (by norm_num)
    have h1 : 1 ≤ Real.sinh (1 / 80) / (1 / 80) := by rw [le_div_iff₀ (by norm_num)]; linarith
    nlinarith
  have hL : (3281 / 3200 : ℝ) ≤ Real.exp (1 / 40) := by
    have := Real.quadratic_le_exp_of_nonneg (x := 1 / 40) (by norm_num); norm_num at this ⊢; linarith
  have hm := evR_mono kData_nonneg (by norm_num) hL
  have h0 := evR_nonneg kData_nonneg (x := 3281 / 3200) (by norm_num)
  have he := Real.exp_pos (-39 / 40)
  have hA : 0 ≤ Real.exp (-39 / 40) * evR kData (3281 / 3200) := by positivity
  calc 1 / 20 * (Real.exp (-39 / 40) * evR kData (3281 / 3200))
      ≤ 1 / 20 * (Real.exp (-39 / 40) * evR kData (Real.exp (1 / 40))) := by gcongr
    _ ≤ 1 / 20 * (Real.sinh (1 / 80) / (1 / 80)) ^ 2
          * (Real.exp (-39 / 40) * evR kData (Real.exp (1 / 40))) := by
        have : 0 ≤ 1 / 20 * (Real.exp (-39 / 40) * evR kData (Real.exp (1 / 40))) := by
          have := evR_nonneg kData_nonneg (Real.exp_pos (1 / 40)).le; positivity
        nlinarith

/-- `(1/2π) ∫ |K̂| ≤ ∑ rⱼ²/D = 1310685.64` (the majorant bound with the verified certificate). -/
lemma kernel4_FT_bound :
    Integrable (fun t : ℝ => ‖paperFT (fun u => (kernel4 u : ℂ)) t‖) ∧
      (2 * π)⁻¹ * ∫ t : ℝ, ‖paperFT (fun u => (kernel4 u : ℂ)) t‖ ≤ 131068564 / 100 := by
  have hcert : ∀ w : ℂ, ‖w‖ = 1 → ((dData : ℤ) : ℝ) * ‖evC kData w‖ ≤ ‖evC rData w‖ ^ 2 :=
    fun w hw => certOK_sound (by decide) certOK_data hw
  obtain ⟨hi, hb⟩ := integral_norm_paperFT_pwl_le (h := 1 / 20) (by norm_num) (-39 / 20)
    (D := dData) (by decide) hcert
  refine ⟨hi, ?_⟩
  have hfun : (fun u => (kernel4 u : ℂ)) = pwlC (1 / 20) (-39 / 20) kData := rfl
  rw [hfun]
  rw [hd_acf_rData] at hb
  have hπ : 0 < 2 * π := by positivity
  rw [inv_mul_le_iff₀ hπ]
  calc ∫ t : ℝ, ‖paperFT (pwlC (1 / 20) (-39 / 20) kData) t‖ ≤ 2 * π * ((131068564 : ℤ) : ℝ) / dData := hb
    _ = 2 * π * (131068564 / 100) := by simp [dData]; ring

/-- The numerical core: `e · q₀ ≤ (9/8) ∫ K e^{u/2}` with `q₀ = ∑ rⱼ²/D = 1310685.64`. -/
lemma exp_mul_q0_le_mass :
    Real.exp (2 / 2) * (131068564 / 100) ≤ 9 / 8 * ∫ u : ℝ, kernel4 u * Real.exp (u / 2) := by
  have hm := mass_kernel4_lower
  have h0 := evR_nonneg kData_nonneg (x := 3281 / 3200) (by norm_num)
  have hnum := evR_kData_lower
  have he1 : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  have hsplit : Real.exp 1 = Real.exp (-39 / 40) * (Real.exp 2 * Real.exp (-1 / 40)) := by
    rw [← Real.exp_add, ← Real.exp_add]; norm_num
  have h41 : Real.exp (-1 / 40) ≤ 40 / 41 := by
    have := Real.add_one_le_exp (1 / 40 : ℝ)
    rw [show (-1 / 40 : ℝ) = -(1 / 40) by norm_num, Real.exp_neg, inv_le_comm₀ (Real.exp_pos _)
      (by norm_num)]
    norm_num at this ⊢; linarith
  have h2 : Real.exp 2 ≤ 2.7182818286 ^ 2 := by
    rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add, ← sq]
    exact pow_le_pow_left₀ (Real.exp_pos 1).le he1.le 2
  have hc : Real.exp 2 * Real.exp (-1 / 40) ≤ 2.7182818286 ^ 2 * (40 / 41) :=
    mul_le_mul h2 h41 (Real.exp_pos _).le (by positivity)
  have hE := Real.exp_pos (-39 / 40)
  rw [show (2 / 2 : ℝ) = 1 by norm_num, hsplit]
  calc Real.exp (-39 / 40) * (Real.exp 2 * Real.exp (-1 / 40)) * (131068564 / 100)
      ≤ Real.exp (-39 / 40) * (2.7182818286 ^ 2 * (40 / 41)) * (131068564 / 100) := by
        gcongr
    _ ≤ Real.exp (-39 / 40) * (9 / 160 * evR kData (3281 / 3200)) := by
        rw [mul_assoc]; gcongr
    _ = 9 / 8 * (1 / 20 * (Real.exp (-39 / 40) * evR kData (3281 / 3200))) := by ring
    _ ≤ 9 / 8 * ∫ u : ℝ, kernel4 u * Real.exp (u / 2) := by gcongr

/-- **Window-4 separation (paper Prop. 17(1), constant 9/8).** The kernel `kernel4` is continuous,
nonnegative, supported in `[−2, 2]` (top `T = 2`), `|K̂|` is integrable, `∫ K e^{u/2} > 0`, and
`e^{T/2} (1/2π) ∫ |K̂| ≤ (9/8) ∫ K(u) e^{u/2} du`. -/
theorem kernel4_separation :
    Continuous kernel4 ∧ (∀ u, 0 ≤ kernel4 u) ∧ (∀ u, kernel4 u ≠ 0 → u ∈ Icc (-2 : ℝ) 2) ∧
      Integrable (fun t : ℝ => ‖paperFT (fun u => (kernel4 u : ℂ)) t‖) ∧
      0 < ∫ u : ℝ, kernel4 u * Real.exp (u / 2) ∧
      Real.exp (2 / 2) * ((2 * π)⁻¹ * ∫ t : ℝ, ‖paperFT (fun u => (kernel4 u : ℂ)) t‖)
        ≤ 9 / 8 * ∫ u : ℝ, kernel4 u * Real.exp (u / 2) := by
  obtain ⟨hi, hb⟩ := kernel4_FT_bound
  have hm := mass_kernel4_lower
  have h0 := evR_nonneg kData_nonneg (x := 3281 / 3200) (by norm_num)
  have hnum := evR_kData_lower
  have hEpos : 0 < evR kData (3281 / 3200) := by
    have : (0 : ℝ) < 2.7182818286 ^ 2 * (40 / 41) * (131068564 / 100) := by norm_num
    linarith
  refine ⟨continuous_kernel4, kernel4_nonneg, fun u => kernel4_support, hi, ?_, ?_⟩
  · have := Real.exp_pos (-39 / 40); nlinarith
  calc Real.exp (2 / 2) * ((2 * π)⁻¹ * ∫ t : ℝ, ‖paperFT (fun u => (kernel4 u : ℂ)) t‖)
      ≤ Real.exp (2 / 2) * (131068564 / 100) := by gcongr
    _ ≤ _ := exp_mul_q0_le_mass

/-- `9/8 < 1/(1 − e^{−2})`, the convolution-square optimum on windows of length `L = 4`
(`1/(1 − e^{−L/2})`, paper Prop. 14). Equivalent to `e² < 9`. -/
theorem nine_eighths_lt_convSq_window4 : (9 / 8 : ℝ) < 1 / (1 - Real.exp (-(4 / 2))) := by
  have he : Real.exp 1 < 3 := lt_trans Real.exp_one_lt_d9 (by norm_num)
  have h2 : Real.exp 2 < 9 := by
    rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
    nlinarith [Real.exp_pos 1]
  have hn : Real.exp (-(4 / 2)) = (Real.exp 2)⁻¹ := by rw [← Real.exp_neg]; norm_num
  have hpos := Real.exp_pos 2
  have h1 : 1 < Real.exp 2 := by
    have := Real.add_one_le_exp (2 : ℝ); linarith
  rw [hn, lt_div_iff₀ (by rw [sub_pos]; exact inv_lt_one_of_one_lt₀ h1)]
  rw [mul_sub, mul_one, ← div_eq_mul_inv]
  have : 9 / 8 / Real.exp 2 > 1 / 8 := by rw [gt_iff_lt, lt_div_iff₀ hpos]; linarith
  linarith

/-- **Paper Prop. 17(1), formal variant.** There is a continuous nonnegative kernel supported in an interval of
length 4 whose support-normalized constant is at most `9/8 < 1/(1 − e^{−2})`. -/
theorem window4_kernel_beats_convSq :
    ∃ K : ℝ → ℝ, Continuous K ∧ (∀ u, 0 ≤ K u) ∧ (∀ u, K u ≠ 0 → u ∈ Icc (-2 : ℝ) 2) ∧
      Integrable (fun t : ℝ => ‖paperFT (fun u => (K u : ℂ)) t‖) ∧
      0 < ∫ u : ℝ, K u * Real.exp (u / 2) ∧
      Real.exp (2 / 2) * ((2 * π)⁻¹ * ∫ t : ℝ, ‖paperFT (fun u => (K u : ℂ)) t‖)
        ≤ 9 / 8 * ∫ u : ℝ, K u * Real.exp (u / 2) ∧
      (9 / 8 : ℝ) < 1 / (1 - Real.exp (-(4 / 2))) :=
  ⟨kernel4, kernel4_separation.1, kernel4_separation.2.1, kernel4_separation.2.2.1,
    kernel4_separation.2.2.2.1, kernel4_separation.2.2.2.2.1, kernel4_separation.2.2.2.2.2,
    nine_eighths_lt_convSq_window4⟩

end GRHPseudo.KernelSeparation
