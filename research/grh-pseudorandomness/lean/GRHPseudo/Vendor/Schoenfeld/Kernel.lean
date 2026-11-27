/- Vendored from github.com/AndrewVSutherland/schoenfeld-rh-lean @ 0e52d7b1,
   `SchoenfeldRH/Explicit/Kernel.lean` (Apache-2.0). Only import paths changed. See ATTRIBUTION.md. -/
import Mathlib
import GRHPseudo.Vendor.Schoenfeld.Perron

/-!
# Vertical-line integrals for the kernel `μ y^s / (s (s + μ))`

Statements only were specified; the proofs are to be written from Mathlib.
All integrals are over `s = c + t i`, `t : ℝ`; `(1/2π) ∫ … dt` is `(1/2πi) ∫_{(c)} … ds`.
-/

open Complex MeasureTheory Set

namespace SchoenfeldRH.Explicit

open SchoenfeldRH.Lemmas.p6

lemma integrable_kappa {c μ : ℝ} (hc : 0 < c) (hμ : 1 < c + μ) :
    Integrable fun t : ℝ => 1 / ((c : ℂ) + t * I) - 1 / ((c : ℂ) + t * I + μ) := by
  have := integrable_diff (σ := c) (a := 0) (b := (μ : ℂ)) (by simpa using hc)
    (by simp only [ofReal_re]; linarith)
  simpa only [add_zero] using this

theorem perron_kernel (y c μ : ℝ) (hy : 0 < y) (hc : 0 < c) (hμ : 1 < c + μ) :
    (1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ, (y : ℂ) ^ ((c : ℂ) + t * I) *
        (1 / ((c : ℂ) + t * I) - 1 / ((c : ℂ) + t * I + μ))
      = if 1 ≤ y then ((1 - y ^ (-μ) : ℝ) : ℂ) else 0 := by
  have key := perron_diff (σ := c) (a := 0) (b := (μ : ℂ)) (by simpa using hc)
    (by simp only [ofReal_re]; linarith) hy
  simp only [add_zero] at key
  rw [key]
  split_ifs with h
  · rw [neg_zero, cpow_zero, ofReal_sub, ofReal_one, ofReal_cpow hy.le, ofReal_neg]
  · rfl

noncomputable def pairK (x c μ : ℝ) (w : ℂ) (t : ℝ) : ℂ :=
  (x : ℂ) ^ ((c : ℂ) + t * I) * ((μ : ℂ) / (w * ((c : ℂ) + t * I - w) * ((c : ℂ) + t * I + μ)))

noncomputable def pairE (x μ : ℝ) (w : ℂ) : ℂ :=
  μ * ((x : ℂ) ^ w - (x : ℂ) ^ (-(μ : ℂ))) / (w * (w + μ))

lemma pair_mul_kappa {x c μ : ℝ} (hc : 0 < c) (hμ : 0 < c + μ) {w : ℂ} (hw : w.re < c) (hw0 : w ≠ 0)
    (t : ℝ) :
    (1 / ((c : ℂ) + t * I - w) + 1 / w) * ((x : ℂ) ^ ((c : ℂ) + t * I) *
        (1 / ((c : ℂ) + t * I) - 1 / ((c : ℂ) + t * I + μ))) = pairK x c μ w t := by
  have hs0 : (c : ℂ) + t * I ≠ 0 := fun h => by
    have := congrArg Complex.re h; simp at this; linarith
  have hsw : (c : ℂ) + t * I - w ≠ 0 := fun h => by
    have := congrArg Complex.re h; simp at this; linarith
  have hsm : (c : ℂ) + t * I + μ ≠ 0 := fun h => by
    have := congrArg Complex.re h; simp at this; linarith
  unfold pairK
  field_simp
  ring

theorem integral_pairK (x c μ : ℝ) (hx : 1 ≤ x) (hc : 0 < c) (hμ : 1 < c + μ) (w : ℂ)
    (hw : w.re < c) (hw0 : w ≠ 0) (hwμ : w + μ ≠ 0) :
    ∫ t : ℝ, pairK x c μ w t = 2 * Real.pi * pairE x μ w := by
  have hpt : ∀ t : ℝ, pairK x c μ w t = ((μ : ℂ) / (w * (w + μ))) *
      ((x : ℂ) ^ ((c : ℂ) + t * I) *
        (1 / ((c : ℂ) + t * I + -w) - 1 / ((c : ℂ) + t * I + (μ : ℂ)))) := by
    intro t
    have hsw : (c : ℂ) + t * I + -w ≠ 0 := fun h => by
      have := congrArg Complex.re h; simp at this; linarith
    have hsw' : (c : ℂ) + t * I - w ≠ 0 := by rwa [← sub_eq_add_neg] at hsw
    have hsm : (c : ℂ) + t * I + μ ≠ 0 := fun h => by
      have := congrArg Complex.re h; simp at this; linarith
    unfold pairK
    field_simp
    ring
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt), integral_const_mul]
  have key := perron_diff (σ := c) (a := -w) (b := (μ : ℂ)) (by simp only [neg_re]; linarith)
    (by simp only [ofReal_re]; linarith) (by linarith : (0 : ℝ) < x)
  simp only [hx, ↓reduceIte, neg_neg] at key
  set J := ∫ t : ℝ, (x : ℂ) ^ ((c : ℂ) + t * I) *
        (1 / ((c : ℂ) + t * I + -w) - 1 / ((c : ℂ) + t * I + (μ : ℂ))) with hJdef
  have hπ : (Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have hJ : J = 2 * Real.pi * ((x : ℂ) ^ w - (x : ℂ) ^ (-(μ : ℂ))) := by
    rw [← key]; field_simp
  rw [hJ]
  unfold pairE
  field_simp

theorem integral_norm_pairK_le {δ : ℝ} (hδ : 0 < δ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x c μ : ℝ, 0 < x → 1 < c + μ → ∀ w : ℂ, w ≠ 0 → w.re ≤ c - δ →
      Integrable (pairK x c μ w) ∧
      ∫ t : ℝ, ‖pairK x c μ w t‖
        ≤ K * x ^ c * |μ| * (1 + |μ - 1|) ^ (1 / 2 : ℝ) * ‖w‖ ^ (-(3 / 2 : ℝ)) := by
  set m := min δ 1 with hm
  have hm0 : 0 < m := lt_min hδ one_pos
  have hm1 : m ≤ 1 := min_le_right _ _
  have hmδ : m ≤ δ := min_le_left _ _
  set J0 := ∫ t : ℝ, (1 + |t|) ^ (-(3 / 2 : ℝ)) with hJ0
  have hJ0nn : 0 ≤ J0 := integral_nonneg fun t => by positivity
  set C := (1 + 1 / √m) * (m / 2) ^ (-(3 / 2 : ℝ)) with hC
  have hCnn : 0 ≤ C := by positivity
  refine ⟨C * (2 * J0), by positivity, ?_⟩
  intro x c μ hx hcμ w hw0 hwc
  set R := (1 + |μ - 1|) ^ (1 / 2 : ℝ) with hR
  set N := ‖w‖ with hNdef
  have hN : 0 < N := norm_pos_iff.mpr hw0
  set D := x ^ c * |μ| * R * N ^ (-(3 / 2 : ℝ)) * C with hD
  have hFint : Integrable fun t : ℝ =>
      D * ((1 + |t - w.im|) ^ (-(3 / 2 : ℝ)) + (1 + |t - 0|) ^ (-(3 / 2 : ℝ))) :=
    ((integrable_rpow_sub w.im _ (by norm_num)).add
      (integrable_rpow_sub 0 _ (by norm_num))).const_mul D
  have hpt : ∀ t : ℝ, ‖pairK x c μ w t‖ ≤
      D * ((1 + |t - w.im|) ^ (-(3 / 2 : ℝ)) + (1 + |t - 0|) ^ (-(3 / 2 : ℝ))) := by
    intro t
    obtain ⟨s, hs⟩ : ∃ s : ℂ, s = (c : ℂ) + t * I := ⟨_, rfl⟩
    have hsre : s.re = c := by rw [hs]; simp
    have hsw_re : (s - w).re = c - w.re := by rw [sub_re, hsre]
    have hsw_im : (s - w).im = t - w.im := by rw [hs]; simp
    have hsm_re : (s + μ).re = c + μ := by rw [add_re, hsre]; simp
    have hsm_im : (s + μ).im = t := by rw [hs]; simp
    have hA := norm_lb (s - w) hm1 (by rw [hsw_re]; linarith)
    have hB := norm_lb (s + μ) hm1 (by rw [hsm_re]; linarith)
    rw [hsw_im] at hA
    rw [hsm_im] at hB
    have hAm : m ≤ ‖s - w‖ := le_trans (by rw [hsw_re]; linarith) (Complex.re_le_norm _)
    have hBm : m ≤ ‖s + μ‖ := le_trans (by rw [hsm_re]; linarith) (Complex.re_le_norm _)
    have hNle : N ≤ ‖s - w‖ + ‖s + μ‖ + (1 + |μ - 1|) := by
      have e : w = (s + μ) - (s - w) - (μ : ℂ) := by ring
      have h1 : ‖w‖ ≤ ‖s + μ‖ + ‖s - w‖ + ‖(μ : ℂ)‖ := by
        calc ‖w‖ = ‖(s + μ) - (s - w) - (μ : ℂ)‖ := by rw [← e]
          _ ≤ ‖(s + μ) - (s - w)‖ + ‖(μ : ℂ)‖ := norm_sub_le _ _
          _ ≤ ‖s + μ‖ + ‖s - w‖ + ‖(μ : ℂ)‖ := by gcongr; exact norm_sub_le _ _
      have h2 : ‖(μ : ℂ)‖ = |μ| := by rw [Complex.norm_real, Real.norm_eq_abs]
      have h3 : |μ| ≤ 1 + |μ - 1| := by
        have := abs_sub_abs_le_abs_sub μ 1; rw [abs_one] at this; linarith
      rw [hNdef]; linarith
    have hnorm : ‖pairK x c μ w t‖ = x ^ c * |μ| * (1 / (N * ‖s - w‖ * ‖s + μ‖)) := by
      have : pairK x c μ w t = (x : ℂ) ^ s * ((μ : ℂ) / (w * (s - w) * (s + μ))) := by
        rw [hs]; rfl
      rw [this, norm_mul, norm_cpow_eq_rpow_re_of_pos hx, norm_div, norm_mul, norm_mul,
        Complex.norm_real, Real.norm_eq_abs, hsre]
      ring
    have hk := key_ineq hm0 hAm hBm hN (by linarith [abs_nonneg (μ - 1)]) hNle
    have hsq : √(1 + |μ - 1|) = R := by rw [Real.sqrt_eq_rpow]
    rw [hsq] at hk
    have hA' : ‖s - w‖ ^ (-(3 / 2 : ℝ)) ≤
        (m / 2) ^ (-(3 / 2 : ℝ)) * (1 + |t - w.im|) ^ (-(3 / 2 : ℝ)) := by
      rw [← Real.mul_rpow (by positivity) (by positivity)]
      exact Real.rpow_le_rpow_of_nonpos (by positivity) hA (by norm_num)
    have hB' : ‖s + μ‖ ^ (-(3 / 2 : ℝ)) ≤
        (m / 2) ^ (-(3 / 2 : ℝ)) * (1 + |t - 0|) ^ (-(3 / 2 : ℝ)) := by
      rw [sub_zero, ← Real.mul_rpow (by positivity) (by positivity)]
      exact Real.rpow_le_rpow_of_nonpos (by positivity) hB (by norm_num)
    rw [hnorm]
    calc x ^ c * |μ| * (1 / (N * ‖s - w‖ * ‖s + μ‖))
        ≤ x ^ c * |μ| * ((1 + 1 / √m) * R * (N ^ (-(3 / 2 : ℝ)) *
            (‖s - w‖ ^ (-(3 / 2 : ℝ)) + ‖s + μ‖ ^ (-(3 / 2 : ℝ))))) :=
          mul_le_mul_of_nonneg_left hk (by positivity)
      _ ≤ x ^ c * |μ| * ((1 + 1 / √m) * R * (N ^ (-(3 / 2 : ℝ)) *
            ((m / 2) ^ (-(3 / 2 : ℝ)) * (1 + |t - w.im|) ^ (-(3 / 2 : ℝ)) +
              (m / 2) ^ (-(3 / 2 : ℝ)) * (1 + |t - 0|) ^ (-(3 / 2 : ℝ))))) := by
          gcongr
      _ = D * ((1 + |t - w.im|) ^ (-(3 / 2 : ℝ)) + (1 + |t - 0|) ^ (-(3 / 2 : ℝ))) := by
          rw [hD, hC]; ring
  have hmeas : Measurable (pairK x c μ w) := by
    show Measurable (fun t : ℝ => (x : ℂ) ^ ((c : ℂ) + t * I) *
      ((μ : ℂ) / (w * ((c : ℂ) + t * I - w) * ((c : ℂ) + t * I + μ))))
    fun_prop
  have hInt : Integrable (pairK x c μ w) :=
    hFint.mono' hmeas.aestronglyMeasurable (Filter.Eventually.of_forall hpt)
  refine ⟨hInt, ?_⟩
  calc ∫ t : ℝ, ‖pairK x c μ w t‖
      ≤ ∫ t : ℝ, D * ((1 + |t - w.im|) ^ (-(3 / 2 : ℝ)) + (1 + |t - 0|) ^ (-(3 / 2 : ℝ))) :=
        integral_mono hInt.norm hFint hpt
    _ = D * (J0 + J0) := by
        rw [integral_const_mul, integral_add (integrable_rpow_sub w.im _ (by norm_num))
          (integrable_rpow_sub 0 _ (by norm_num)), integral_rpow_sub, integral_rpow_sub]
    _ = C * (2 * J0) * x ^ c * |μ| * R * N ^ (-(3 / 2 : ℝ)) := by rw [hD]; ring

end SchoenfeldRH.Explicit
-- stamp: 2
