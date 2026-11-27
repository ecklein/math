import Mathlib

/-!
# Shifting a vertical line of integration

If `f` is holomorphic on the closed strip `σ ≤ Re s ≤ σ'`, integrable on both boundary lines,
and its horizontal integrals across the strip tend to `0` at height `±∞`, then the two vertical
line integrals agree. Proof: Cauchy's theorem for the rectangle `[σ, σ'] × [-T, T]`
(`Complex.integral_boundary_rect_eq_zero_of_differentiableOn`), then `T → ∞`.
-/

noncomputable section

open Complex Filter Topology MeasureTheory Set
open scoped Interval

namespace GRHPseudo

theorem integral_vertical_eq {f : ℂ → ℂ} {σ σ' : ℝ}
    (hf : DifferentiableOn ℂ f ([[σ, σ']] ×ℂ univ))
    (hσ : Integrable fun t : ℝ ↦ f (σ + t * I))
    (hσ' : Integrable fun t : ℝ ↦ f (σ' + t * I))
    (htop : Tendsto (fun T : ℝ ↦ ∫ x in σ..σ', f (x + T * I)) atTop (𝓝 0))
    (hbot : Tendsto (fun T : ℝ ↦ ∫ x in σ..σ', f (x + T * I)) atBot (𝓝 0)) :
    ∫ t : ℝ, f (σ + t * I) = ∫ t : ℝ, f (σ' + t * I) := by
  -- the rectangle identity at height T
  have rect : ∀ T : ℝ,
      (∫ x in σ..σ', f (x + (-T : ℝ) * I)) - (∫ x in σ..σ', f (x + T * I))
        + I • (∫ y in (-T)..T, f (σ' + y * I)) - I • (∫ y in (-T)..T, f (σ + y * I)) = 0 := by
    intro T
    have h := Complex.integral_boundary_rect_eq_zero_of_differentiableOn f
      (⟨σ, -T⟩ : ℂ) (⟨σ', T⟩ : ℂ)
      (hf.mono (reProdIm_subset_iff'.mpr (Or.inl ⟨subset_refl _, subset_univ _⟩)))
    simpa using h
  have hbot' : Tendsto (fun T : ℝ ↦ ∫ x in σ..σ', f (x + (-T : ℝ) * I)) atTop (𝓝 0) :=
    hbot.comp tendsto_neg_atTop_atBot
  have hL : Tendsto (fun T : ℝ ↦ ∫ y in (-T)..T, f (σ + y * I)) atTop
      (𝓝 (∫ t : ℝ, f (σ + t * I))) :=
    intervalIntegral_tendsto_integral hσ tendsto_neg_atTop_atBot tendsto_id
  have hR : Tendsto (fun T : ℝ ↦ ∫ y in (-T)..T, f (σ' + y * I)) atTop
      (𝓝 (∫ t : ℝ, f (σ' + t * I))) :=
    intervalIntegral_tendsto_integral hσ' tendsto_neg_atTop_atBot tendsto_id
  have hlim := ((hbot'.sub htop).add (hR.const_smul I)).sub (hL.const_smul I)
  have hzero : Tendsto (fun T : ℝ ↦
      (∫ x in σ..σ', f (x + (-T : ℝ) * I)) - (∫ x in σ..σ', f (x + T * I))
        + I • (∫ y in (-T)..T, f (σ' + y * I)) - I • (∫ y in (-T)..T, f (σ + y * I)))
      atTop (𝓝 0) := by
    simp_rw [rect]; exact tendsto_const_nhds
  have heq := tendsto_nhds_unique hlim hzero
  simp only [sub_zero, smul_eq_mul] at heq
  have : I * ((∫ t : ℝ, f (σ' + t * I)) - ∫ t : ℝ, f (σ + t * I)) = 0 := by
    rw [mul_sub]; linear_combination heq
  rcases mul_eq_zero.mp this with h | h
  · exact absurd h I_ne_zero
  · exact (sub_eq_zero.mp h).symm

end GRHPseudo
