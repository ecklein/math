import GRHPseudo.KernelSeparation.Poly
import Zeta23.Poisson.PaperFT

/-!
# The triangle function and piecewise-linear kernels

`tri s = max 0 (1 − |s|)`. Its transform in the paper convention (`Zeta23.paperFT`,
`f̂(z) = ∫ f(u) e^{izu} du`) is `(2 − e^{iz} − e^{−iz})/z²` for `z ≠ 0` (`paperFT_tri`), so on the real
line it is `triFT t = (2 − 2 cos t)/t²` (for `t ≠ 0`). Fourier inversion at the integers gives
`∫ triFT(τ) e^{imτ} dτ = 2π [m = 0]` (`integral_triFT_mul_exp`).
-/

namespace GRHPseudo.KernelSeparation

open Complex MeasureTheory Real Set Filter
open Zeta23 (paperFT)
open scoped FourierTransform

/-- The triangle function `Λ(s) = max(0, 1 − |s|)`. -/
noncomputable def tri (s : ℝ) : ℝ := max 0 (1 - |s|)

lemma tri_nonneg (s : ℝ) : 0 ≤ tri s := le_max_left _ _

lemma continuous_tri : Continuous tri := by unfold tri; fun_prop

lemma tri_eq_zero {s : ℝ} (hs : 1 ≤ |s|) : tri s = 0 := by
  unfold tri; exact max_eq_left (by linarith)

lemma tri_of_nonneg {s : ℝ} (h0 : 0 ≤ s) (h1 : s ≤ 1) : tri s = 1 - s := by
  unfold tri; rw [abs_of_nonneg h0]; exact max_eq_right (by linarith)

lemma tri_of_nonpos {s : ℝ} (h0 : s ≤ 0) (h1 : -1 ≤ s) : tri s = 1 + s := by
  unfold tri; rw [abs_of_nonpos h0, max_eq_right (by linarith)]; ring

lemma tri_natCast (n : ℕ) : tri (n : ℝ) = if n = 0 then 1 else 0 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [tri]
  · rw [ite_eq_right_iff.mpr (fun h => absurd h (Nat.pos_iff_ne_zero.mp hn)), tri_eq_zero]
    rw [abs_of_nonneg (by positivity)]; exact_mod_cast hn

lemma tri_neg_natCast (n : ℕ) : tri (-(n : ℝ)) = if n = 0 then 1 else 0 := by
  rw [← tri_natCast]; unfold tri; rw [abs_neg]

/-- The complexified triangle function. -/
noncomputable def triC (s : ℝ) : ℂ := (tri s : ℂ)

lemma continuous_triC : Continuous triC := continuous_ofReal.comp continuous_tri

lemma triC_eq_zero_of_not_mem {s : ℝ} (hs : s ∉ Icc (-1 : ℝ) 1) : triC s = 0 := by
  unfold triC; rw [tri_eq_zero]; · simp
  rw [mem_Icc, not_and_or, not_le, not_le] at hs
  rcases hs with hs | hs
  · rw [abs_of_neg (by linarith)]; linarith
  · rw [abs_of_pos (by linarith)]; linarith

lemma hasCompactSupport_triC : HasCompactSupport triC :=
  HasCompactSupport.intro isCompact_Icc fun _ hs => triC_eq_zero_of_not_mem hs

/-- Integrability of `g · e^{i z u}` for continuous compactly supported `g`. -/
lemma integrable_mul_cexp {g : ℝ → ℂ} (hg : Continuous g) (hgs : HasCompactSupport g) (z : ℂ) :
    Integrable (fun u : ℝ => g u * cexp (I * z * u)) :=
  (hg.mul (by fun_prop)).integrable_of_hasCompactSupport hgs.mul_right

/-! ### Closed form of the transform -/

private lemma hasDerivAt_right (c : ℂ) (hc : c ≠ 0) (u : ℝ) :
    HasDerivAt (fun u : ℝ => cexp (c * u) * ((1 - u) / c + 1 / c ^ 2))
      ((1 - u) * cexp (c * u)) u := by
  have h1 : HasDerivAt (fun u : ℝ => cexp (c * u)) (cexp (c * u) * c) u := by
    have := ((hasDerivAt_id (u : ℂ)).const_mul c).cexp
    simpa using this.comp_ofReal
  have h2 : HasDerivAt (fun u : ℝ => (1 - (u : ℂ)) / c + 1 / c ^ 2) (-1 / c) u := by
    have := (((hasDerivAt_id (u : ℂ)).const_sub 1).div_const c).add_const (1 / c ^ 2)
    simpa using this.comp_ofReal
  convert h1.mul h2 using 1
  field_simp
  ring

private lemma hasDerivAt_left (c : ℂ) (hc : c ≠ 0) (u : ℝ) :
    HasDerivAt (fun u : ℝ => cexp (c * u) * ((1 + u) / c - 1 / c ^ 2))
      ((1 + u) * cexp (c * u)) u := by
  have h1 : HasDerivAt (fun u : ℝ => cexp (c * u)) (cexp (c * u) * c) u := by
    have := ((hasDerivAt_id (u : ℂ)).const_mul c).cexp
    simpa using this.comp_ofReal
  have h2 : HasDerivAt (fun u : ℝ => (1 + (u : ℂ)) / c - 1 / c ^ 2) (1 / c) u := by
    have := (((hasDerivAt_id (u : ℂ)).const_add 1).div_const c).sub_const (1 / c ^ 2)
    simpa using this.comp_ofReal
  convert h1.mul h2 using 1
  field_simp
  ring

lemma paperFT_triC_eq_interval (z : ℂ) :
    paperFT triC z = ∫ u in (-1 : ℝ)..1, triC u * cexp (I * z * u) := by
  rw [Zeta23.paperFT_def, intervalIntegral.integral_of_le (by norm_num),
    ← integral_Icc_eq_integral_Ioc, setIntegral_eq_integral_of_forall_compl_eq_zero]
  intro u hu; rw [triC_eq_zero_of_not_mem hu, zero_mul]

/-- **Transform of the triangle function**: `Λ̂(z) = (2 − e^{iz} − e^{−iz})/z²` for `z ≠ 0`. -/
theorem paperFT_tri {z : ℂ} (hz : z ≠ 0) :
    paperFT triC z = (2 - cexp (I * z) - cexp (-(I * z))) / z ^ 2 := by
  have hcont : Continuous fun u : ℝ => triC u * cexp (I * z * u) :=
    continuous_triC.mul (by fun_prop)
  rw [paperFT_triC_eq_interval, ← intervalIntegral.integral_add_adjacent_intervals (b := 0)
      (hcont.intervalIntegrable _ _) (hcont.intervalIntegrable _ _)]
  set c := I * z with hcdef
  have hc : c ≠ 0 := mul_ne_zero I_ne_zero hz
  have hL : ∫ u in (-1 : ℝ)..0, triC u * cexp (I * z * u) =
      ∫ u in (-1 : ℝ)..0, (1 + (u : ℂ)) * cexp (c * u) := by
    refine intervalIntegral.integral_congr fun u hu => ?_
    rw [uIcc_of_le (by norm_num)] at hu
    simp only [triC, tri_of_nonpos hu.2 hu.1, hcdef]; push_cast; ring
  have hR : ∫ u in (0 : ℝ)..1, triC u * cexp (I * z * u) =
      ∫ u in (0 : ℝ)..1, (1 - (u : ℂ)) * cexp (c * u) := by
    refine intervalIntegral.integral_congr fun u hu => ?_
    rw [uIcc_of_le (by norm_num)] at hu
    simp only [triC, tri_of_nonneg hu.1 hu.2, hcdef]; push_cast; ring
  rw [hL, hR,
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hasDerivAt_left c hc u)
      ((by fun_prop : Continuous fun u : ℝ => (1 + (u : ℂ)) * cexp (c * u)).intervalIntegrable _ _),
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hasDerivAt_right c hc u)
      ((by fun_prop : Continuous fun u : ℝ => (1 - (u : ℂ)) * cexp (c * u)).intervalIntegrable _ _)]
  have hc2 : c ^ 2 = -z ^ 2 := by rw [hcdef, mul_pow, I_sq]; ring
  have hz2 : z ^ 2 ≠ 0 := pow_ne_zero 2 hz
  push_cast
  simp only [mul_zero, Complex.exp_zero, mul_one, mul_neg]
  field_simp
  rw [hc2]
  ring

/-- The real transform `(2 − 2 cos t)/t²` (equal to `Λ̂(t)` for `t ≠ 0`). -/
noncomputable def triFT (t : ℝ) : ℝ := (2 - 2 * Real.cos t) / t ^ 2

lemma paperFT_tri_real {t : ℝ} (ht : t ≠ 0) : paperFT triC t = (triFT t : ℂ) := by
  rw [paperFT_tri (by exact_mod_cast ht), triFT]
  have : 2 * Complex.cos t = cexp (I * t) + cexp (-(I * t)) := by
    rw [Complex.cos, mul_comm (t : ℂ) I, neg_mul]; ring_nf
  push_cast
  rw [this]; ring

lemma triFT_nonneg (t : ℝ) : 0 ≤ triFT t := by
  unfold triFT; apply div_nonneg _ (sq_nonneg _); linarith [Real.cos_le_one t]

lemma triFT_le (t : ℝ) : triFT t ≤ 8 / (1 + t ^ 2) := by
  rcases eq_or_ne t 0 with rfl | ht
  · simp [triFT]
  have ht2 : 0 < t ^ 2 := by positivity
  unfold triFT
  rw [div_le_div_iff₀ ht2 (by positivity)]
  rcases le_or_gt (t ^ 2) 1 with h | h
  · have := Real.one_sub_sq_div_two_le_cos (x := t)
    nlinarith
  · nlinarith [Real.neg_one_le_cos t]

lemma measurable_triFT : Measurable triFT := by unfold triFT; fun_prop

lemma integrable_triFT : Integrable triFT := by
  refine Integrable.mono' (integrable_inv_one_add_sq.const_mul 8) measurable_triFT.aestronglyMeasurable
    (Eventually.of_forall fun t => ?_)
  rw [Real.norm_of_nonneg (triFT_nonneg t), ← div_eq_mul_inv]; exact triFT_le t

lemma paperFT_triC_ae : (fun t : ℝ => paperFT triC t) =ᵐ[volume] fun t => (triFT t : ℂ) := by
  have : ∀ᵐ t : ℝ ∂volume, t ≠ 0 := by
    simp [ae_iff]
  filter_upwards [this] with t ht using paperFT_tri_real ht

/-! ### Fourier inversion in the paper convention -/

/-- Fourier inversion in the paper convention: `∫ f̂(τ) e^{−iτx} dτ = 2π f(x)`. -/
theorem integral_paperFT_mul_cexp {f : ℝ → ℂ} (hc : Continuous f) (hf : Integrable f)
    (hF : Integrable fun τ : ℝ => paperFT f τ) (x : ℝ) :
    ∫ τ : ℝ, paperFT f τ * cexp (-(I * τ * x)) = 2 * π * f x := by
  have hFm : Integrable (𝓕 f) := by
    have := hF.comp_mul_left' (R := -(2 * π)) (by simp [Real.pi_ne_zero])
    refine this.congr (Eventually.of_forall fun v => ?_)
    simp only [Zeta23.fourier_eq_paperFT]; congr 1; push_cast; ring
  have hinv := congrFun (hc.fourierInv_fourier_eq hf hFm) x
  rw [Real.fourierInv_eq'] at hinv
  set φ : ℝ → ℂ := fun τ => paperFT f τ * cexp (-(I * τ * x))
  have hφ : ∀ v : ℝ, cexp (↑(2 * π * inner ℝ v x) * I) • 𝓕 f v = φ (-(2 * π) * v) := by
    intro v
    simp only [φ, smul_eq_mul, Zeta23.fourier_eq_paperFT, RCLike.inner_apply, conj_trivial]
    rw [mul_comm]; congr 2 <;> push_cast <;> ring_nf
  simp_rw [hφ] at hinv
  rw [Measure.integral_comp_mul_left φ (-(2 * π))] at hinv
  have h2π : (0 : ℝ) < 2 * π := by positivity
  rw [abs_inv, abs_neg, abs_of_pos h2π, Complex.real_smul] at hinv
  rw [← hinv]
  push_cast
  field_simp

lemma integrable_triC : Integrable triC :=
  continuous_triC.integrable_of_hasCompactSupport hasCompactSupport_triC

lemma integrable_paperFT_triC : Integrable fun τ : ℝ => paperFT triC τ :=
  (integrable_triFT.ofReal).congr paperFT_triC_ae.symm

/-- `∫ Λ̂(τ) e^{inτ} dτ = 2π [n = 0]` for natural `n`. -/
theorem integral_triFT_mul_exp (n : ℕ) :
    ∫ τ : ℝ, (triFT τ : ℂ) * cexp (I * τ) ^ n = 2 * π * (if n = 0 then 1 else 0) := by
  have h := integral_paperFT_mul_cexp continuous_triC integrable_triC integrable_paperFT_triC (-(n : ℝ))
  rw [triC, tri_neg_natCast] at h
  have hc : ((if n = 0 then (1 : ℝ) else 0 : ℝ) : ℂ) = if n = 0 then 1 else 0 := by
    split_ifs <;> simp
  rw [hc] at h
  rw [← h]
  refine (integral_congr_ae ?_)
  filter_upwards [paperFT_triC_ae] with τ hτ
  rw [hτ, ← Complex.exp_nat_mul]; congr 2; push_cast; ring

end GRHPseudo.KernelSeparation
