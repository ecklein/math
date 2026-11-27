import GRHPseudo.AnalyticNumberTheory.Sharp.GammaBounds

/-!
# A sharper bound for the gamma-side integrals

For `f ∈ C_c²` with `‖f̂(r)‖ |r| ≤ C` and any `R > 0`, `B ≥ 0`:

    I(B) / (2π) ≤ (log(4 + R) + B) · Re (f ⋆ f̃)(0) + 4 C² / (π R).

Proof: on `|r| ≤ R` bound `log(4+|r|) ≤ log(4+R)` and use Plancherel,
`(1/2π) ∫ ‖f̂‖² = Re (f ⋆ f̃)(0)`. On `|r| > R`, `log(4+|r|) − log(4+R) ≤ log(|r|/R) ≤ 2 (|r|/R)^{1/2}`
and `‖f̂(r)‖² ≤ C²/r²`, so the excess is at most `2 C² R^{−1/2} |r|^{−3/2}`, whose integral over
`|r| > R` is `8 C²/R`. The constant part of `I(B)` thus enters with the sharp factor `(f ⋆ f̃)(0)`.
-/

noncomputable section

open Complex MeasureTheory Set Zeta23 Zeta23.EF
open scoped Real

namespace GRHPseudo.Sharp

/-- The tail profile `x ↦ x^{−3/2}` on `(R, ∞)`. -/
def tailProfile (R : ℝ) : ℝ → ℝ := (Ioi R).indicator fun x ↦ x ^ (-(3 / 2 : ℝ))

lemma tailProfile_nonneg (R x : ℝ) (hR : 0 ≤ R) : 0 ≤ tailProfile R x := by
  unfold tailProfile
  by_cases hx : x ∈ Ioi R
  · rw [indicator_of_mem hx]; exact Real.rpow_nonneg (by linarith [mem_Ioi.mp hx]) _
  · rw [indicator_of_notMem hx]

lemma integrable_tailProfile {R : ℝ} (hR : 0 < R) : Integrable (tailProfile R) :=
  (integrableOn_Ioi_rpow_of_lt (by norm_num) hR).integrable_indicator measurableSet_Ioi

lemma integral_tailProfile {R : ℝ} (hR : 0 < R) :
    ∫ x, tailProfile R x = 2 * R ^ (-(1 / 2 : ℝ)) := by
  unfold tailProfile
  rw [integral_indicator measurableSet_Ioi, integral_Ioi_rpow_of_lt (by norm_num) hR]
  norm_num
  ring

/-- Pointwise tail estimate: for `s > R > 0` and `F ≤ C²/s²`,
`F · log(s/R) ≤ 2 C² R^{−1/2} s^{−3/2}`. -/
lemma tail_pointwise {R s F C : ℝ} (hR : 0 < R) (hs : R < s) (hF0 : 0 ≤ F)
    (hF : F ≤ C ^ 2 / s ^ 2) :
    F * Real.log (s / R) ≤ 2 * C ^ 2 * R ^ (-(1 / 2 : ℝ)) * s ^ (-(3 / 2 : ℝ)) := by
  have hs0 : 0 < s := hR.trans hs
  have hlog := Real.log_le_rpow_div (x := s / R) (div_pos hs0 hR).le (by norm_num : (0 : ℝ) < 1 / 2)
  have hlog0 : 0 ≤ Real.log (s / R) := Real.log_nonneg (by rw [le_div_iff₀ hR]; linarith)
  have key : (C ^ 2 / s ^ 2) * ((s / R) ^ (1 / 2 : ℝ) / (1 / 2)) =
      2 * C ^ 2 * R ^ (-(1 / 2 : ℝ)) * s ^ (-(3 / 2 : ℝ)) := by
    have h1 : s ^ (1 / 2 : ℝ) = s ^ (-(3 / 2 : ℝ)) * s ^ 2 := by
      rw [← Real.rpow_natCast, ← Real.rpow_add hs0]; norm_num
    rw [Real.div_rpow hs0.le hR.le, Real.rpow_neg hR.le, h1]
    have : 0 < R ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hR _
    field_simp
  calc F * Real.log (s / R) ≤ (C ^ 2 / s ^ 2) * ((s / R) ^ (1 / 2 : ℝ) / (1 / 2)) :=
        mul_le_mul hF hlog hlog0 (by positivity)
    _ = _ := key

variable {f : ℝ → ℂ}

/-- **Sharper gamma-side bound.** -/
theorem Ilog_div_le_sharp (hf : ContDiff ℝ 2 f) (hfs : HasCompactSupport f) {C R B : ℝ}
    (hR : 0 < R) (hB : 0 ≤ B) (h1 : ∀ r : ℝ, ‖paperFT f (r : ℂ)‖ * |r| ≤ C) :
    Ilog f B / (2 * π) ≤ (Real.log (4 + R) + B) * (weilTest f f 0).re + 4 * C ^ 2 / (π * R) := by
  set F : ℝ → ℝ := fun r ↦ ‖paperFT f (r : ℂ)‖ ^ 2 with hFdef
  set c : ℝ := 2 * C ^ 2 * R ^ (-(1 / 2 : ℝ))
  set g : ℝ → ℝ := fun r ↦ F r * (Real.log (4 + R) + B) + c * (tailProfile R r + tailProfile R (-r))
  have hFi : Integrable F := integrable_normSq_paperFT hf hfs
  have hT := integrable_tailProfile hR
  have hTneg : Integrable fun r ↦ tailProfile R (-r) := hT.comp_neg
  have hgi : Integrable g := (hFi.mul_const _).add ((hT.add hTneg).const_mul c)
  have hLi := GRHMiller.integrable_normSq_paperFT_mul_log hf hfs 1 B
  have hc0 : 0 ≤ c := by positivity
  have hpt : ∀ r, F r * (1 * Real.log (4 + |r|) + B) ≤ g r := by
    intro r
    have hF0 : 0 ≤ F r := by positivity
    have hT0 := tailProfile_nonneg R r hR.le
    have hT0' := tailProfile_nonneg R (-r) hR.le
    simp only [g, one_mul]
    by_cases hr : |r| ≤ R
    · have : Real.log (4 + |r|) ≤ Real.log (4 + R) :=
        Real.log_le_log (by positivity) (by linarith)
      nlinarith [mul_nonneg hc0 (add_nonneg hT0 hT0')]
    · push_neg at hr
      set s := |r|
      have hs0 : 0 < s := hR.trans hr
      -- `‖f̂(r)‖² ≤ C²/s²`
      have hFs : F r ≤ C ^ 2 / s ^ 2 := by
        have hn := h1 r
        have hn0 := norm_nonneg (paperFT f (r : ℂ))
        rw [le_div_iff₀ (by positivity)]
        have hC0 : 0 ≤ C := le_trans (by positivity) hn
        have := pow_le_pow_left₀ (by positivity) hn 2
        simp only [F]; nlinarith [this]
      -- `log(4+s) − log(4+R) ≤ log(s/R)`
      have hlog : Real.log (4 + s) - Real.log (4 + R) ≤ Real.log (s / R) := by
        rw [← Real.log_div (by positivity) (by positivity)]
        exact Real.log_le_log (by positivity) (by
          rw [div_le_div_iff₀ (by positivity) hR]; nlinarith)
      have htail := tail_pointwise hR hr hF0 hFs
      -- the relevant leg of the profile equals `s^{−3/2}`
      have hleg : s ^ (-(3 / 2 : ℝ)) ≤ tailProfile R r + tailProfile R (-r) := by
        rcases le_or_gt 0 r with h | h
        · have hs : s = r := abs_of_nonneg h
          have hm : r ∈ Ioi R := by rw [← hs]; exact hr
          have : tailProfile R r = s ^ (-(3 / 2 : ℝ)) := by
            unfold tailProfile; rw [indicator_of_mem hm, hs]
          linarith
        · have hs : s = -r := abs_of_neg h
          have hm : -r ∈ Ioi R := by rw [← hs]; exact hr
          have : tailProfile R (-r) = s ^ (-(3 / 2 : ℝ)) := by
            unfold tailProfile; rw [indicator_of_mem hm, hs]
          linarith
      have hFlog : F r * Real.log (s / R) ≥ F r * (Real.log (4 + s) - Real.log (4 + R)) :=
        mul_le_mul_of_nonneg_left hlog hF0
      have : c * s ^ (-(3 / 2 : ℝ)) ≤ c * (tailProfile R r + tailProfile R (-r)) :=
        mul_le_mul_of_nonneg_left hleg hc0
      nlinarith
  have hI : Ilog f B ≤ ∫ r, g r := integral_mono hLi hgi hpt
  have e1 : ∫ r, g r = (∫ r, F r * (Real.log (4 + R) + B)) +
      ∫ r, c * (tailProfile R r + tailProfile R (-r)) :=
    integral_add (hFi.mul_const _) ((hT.add hTneg).const_mul c)
  have e2 : ∫ r, c * (tailProfile R r + tailProfile R (-r)) =
      c * ((∫ r, tailProfile R r) + ∫ r, tailProfile R (-r)) := by
    rw [integral_const_mul, integral_add hT hTneg]
  have e3 : ∫ r, tailProfile R (-r) = ∫ r, tailProfile R r :=
    integral_neg_eq_self (fun r ↦ tailProfile R r) volume
  have hpl := GRHMiller.re_weilTest_zero' hf hfs hFi
  have hFint : ∫ r, F r = 2 * π * (weilTest f f 0).re := by
    rw [hpl]; field_simp; rfl
  have hgint : ∫ r, g r = (Real.log (4 + R) + B) * (2 * π * (weilTest f f 0).re) +
      c * (4 * R ^ (-(1 / 2 : ℝ))) := by
    rw [e1, e2, e3, integral_mul_const, hFint, integral_tailProfile hR]
    ring
  have hRR : R ^ (-(1 / 2 : ℝ)) * R ^ (-(1 / 2 : ℝ)) = R⁻¹ := by
    rw [← Real.rpow_add hR]; norm_num; exact Real.rpow_neg_one R
  have hpi : 0 < 2 * π := by positivity
  rw [div_le_iff₀ hpi]
  calc Ilog f B ≤ ∫ r, g r := hI
    _ = (Real.log (4 + R) + B) * (2 * π * (weilTest f f 0).re) + 8 * C ^ 2 *
          (R ^ (-(1 / 2 : ℝ)) * R ^ (-(1 / 2 : ℝ))) := by rw [hgint]; ring
    _ = ((Real.log (4 + R) + B) * (weilTest f f 0).re + 4 * C ^ 2 / (π * R)) * (2 * π) := by
        rw [hRR]; field_simp; ring

end GRHPseudo.Sharp
