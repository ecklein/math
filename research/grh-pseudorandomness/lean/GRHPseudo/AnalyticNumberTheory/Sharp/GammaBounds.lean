import GRHPseudo.AnalyticNumberTheory.Sharp.MainTerm

/-!
# Explicit bounds for the gamma sides (obligation D3)

For `k = f ⋆ f̃` with `f ∈ C_c²`, writing `F(r) = ‖f̂(r)‖²` and `I(B) = ∫ F(r)(log(4+|r|) + B) dr`:

* `|Re ψ(1/4 + κ/2 + ir/2)| ≤ log(4+|r|) + 5` for `κ ∈ {0,1}`. The upper side is grh-miller's
  `re_digamma_gammaFactor_le_half`. The lower side comes from zeta-23's series
  `re_digamma_vertical`, all of whose terms are nonnegative.
* Twisted χ gamma side: if `k(−y) = 0` then `‖Γ(k_y)‖ ≤ I(5)/(2π)`. The `log(q/π)` part vanishes
  by Fourier inversion at `−y`. This keeps the leading coefficient of `log q` at `k(0)`.
* Untwisted χ gamma side: `Re Γ(k) ≤ Re k(0) · log(q/π) + I(1/2)/(2π)`, using Plancherel.
* ζ gamma sides: `‖Γ_ζ(k_y)‖ ≤ I(5 + log π)/(2π)` and `Re Γ_ζ(k) ≤ I(1/2)/(2π)`.
-/

noncomputable section

open Complex MeasureTheory Zeta23 Zeta23.EF Zeta23.ThmE
open scoped Real ComplexConjugate

namespace GRHPseudo.Sharp

/-! ### Digamma on the relevant vertical lines -/

theorem neg_five_le_re_digamma (κ : ℕ) (hκ : κ ≤ 1) (r : ℝ) :
    -5 ≤ (Complex.digamma (1 / 4 + (κ : ℂ) / 2 + I * r / 2)).re := by
  set a : ℝ := 1 / 4 + κ / 2 with hadef
  have hκr : (κ : ℝ) ≤ 1 := by exact_mod_cast hκ
  have ha0 : 0 < a := by positivity
  have ha1 : a < 1 := by linarith
  have harg : (1 / 4 + (κ : ℂ) / 2 + I * r / 2) = (a : ℂ) + I * ((r / 2 : ℝ) : ℂ) := by
    rw [hadef]; push_cast; ring
  rw [harg, Zeta23.MuFields.re_digamma_vertical ha0 ha1]
  set t : ℝ := r / 2
  have hterm : ∀ n : ℕ, 0 ≤ 1 / ((n : ℝ) + 1) - ((n : ℝ) + 1 + a) / (((n : ℝ) + 1 + a) ^ 2 + t ^ 2) := by
    intro n
    have h1 : ((n : ℝ) + 1 + a) / (((n : ℝ) + 1 + a) ^ 2 + t ^ 2) ≤ 1 / ((n : ℝ) + 1 + a) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [sq_nonneg t]
    have h2 : 1 / ((n : ℝ) + 1 + a) ≤ 1 / ((n : ℝ) + 1) :=
      one_div_le_one_div_of_le (by positivity) (by linarith)
    linarith
  have hsum : 0 ≤ ∑' n : ℕ, (1 / ((n : ℝ) + 1) - ((n : ℝ) + 1 + a) / (((n : ℝ) + 1 + a) ^ 2 + t ^ 2)) :=
    tsum_nonneg hterm
  have hfrac : a / (a ^ 2 + t ^ 2) ≤ 4 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith [sq_nonneg t]
  have hγ := Real.eulerMascheroniConstant_lt_two_thirds
  linarith

theorem abs_re_digamma_le (κ : ℕ) (hκ : κ ≤ 1) (r : ℝ) :
    |(Complex.digamma (1 / 4 + (κ : ℂ) / 2 + I * r / 2)).re| ≤ Real.log (4 + |r|) + 5 := by
  have hlo := neg_five_le_re_digamma κ hκ r
  have hhi := GRHMiller.re_digamma_gammaFactor_le_half κ hκ r
  have hlog : 0 ≤ Real.log (4 + |r|) := Real.log_nonneg (by linarith [abs_nonneg r])
  rw [abs_le]; constructor <;> linarith

/-! ### Fourier facts for `k = f ⋆ f̃` -/

variable {f : ℝ → ℂ}

lemma paperFT_weilTest_real (hf : ContDiff ℝ 2 f) (hfs : HasCompactSupport f) (r : ℝ) :
    paperFT (weilTest f f) (r : ℂ) = ((‖paperFT f (r : ℂ)‖ ^ 2 : ℝ) : ℂ) := by
  rw [paperFT_weilTest hf.continuous hf.continuous hfs hfs, Complex.conj_ofReal,
    Complex.mul_conj, Complex.normSq_eq_norm_sq]

lemma integrable_normSq_paperFT (hf : ContDiff ℝ 2 f) (hfs : HasCompactSupport f) :
    Integrable (fun r : ℝ ↦ ‖paperFT f (r : ℂ)‖ ^ 2) := by
  have := GRHMiller.integrable_normSq_paperFT_mul_log hf hfs 0 1
  simpa using this

/-- Fourier inversion at `−y`: `(1/2π) ∫ e^{iry} ‖f̂(r)‖² dr = k(−y)`. -/
lemma integral_paperFT_twist (hf : ContDiff ℝ 2 f) (hfs : HasCompactSupport f) (y : ℝ) :
    (1 / (2 * π) : ℂ) * ∫ r : ℝ, paperFT (twist (weilTest f f) y) (r : ℂ) = weilTest f f (-y) := by
  set k := weilTest f f
  have hkc : ContDiff ℝ 2 k := weilTest_contDiff hf hf.continuous hfs
  have hks : HasCompactSupport k := weilTest_hasCompactSupport hfs hfs
  have hki : Integrable k := hkc.continuous.integrable_of_hasCompactSupport hks
  have hPi : Integrable (fun r : ℝ ↦ paperFT k (r : ℂ)) := by
    exact (integrable_normSq_paperFT hf hfs).ofReal.congr
      (Filter.Eventually.of_forall fun r ↦ (paperFT_weilTest_real hf hfs r).symm)
  have hFk : Integrable (FourierTransform.fourier k) := by
    have h := hPi.comp_mul_left' (show (-(2 * π) : ℝ) ≠ 0 by have := Real.pi_pos; linarith)
    refine h.congr (Filter.Eventually.of_forall fun w ↦ ?_)
    show paperFT k ((-(2 * π) * w : ℝ) : ℂ) = _
    rw [EF.paperFT_ofReal_eq_fourier]
    congr 1
    field_simp
  have hpt : ∀ r : ℝ, paperFT (twist k y) (r : ℂ) =
      paperFT k (r : ℂ) * Complex.exp (-I * (r : ℂ) * ((-y : ℝ) : ℂ)) := by
    intro r; rw [paperFT_twist, mul_comm]; congr 2; push_cast; ring
  simp_rw [hpt]
  exact (paper_inversion hkc.continuous hki hFk (-y)).symm

/-! ### Gamma sides -/

/-- Integral `I(B) = ∫ ‖f̂(r)‖² (log(4+|r|) + B) dr`. -/
def Ilog (f : ℝ → ℂ) (B : ℝ) : ℝ :=
  ∫ r : ℝ, ‖paperFT f (r : ℂ)‖ ^ 2 * (1 * Real.log (4 + |r|) + B)

lemma norm_paperFT_twist (hf : ContDiff ℝ 2 f) (hfs : HasCompactSupport f) (y r : ℝ) :
    ‖paperFT (twist (weilTest f f) y) (r : ℂ)‖ = ‖paperFT f (r : ℂ)‖ ^ 2 := by
  rw [paperFT_twist, norm_mul, paperFT_weilTest_real hf hfs, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have : ‖Complex.exp (I * (r : ℂ) * (y : ℂ))‖ = 1 := by rw [Complex.norm_exp]; simp
  rw [this, one_mul]

/-- **Twisted χ gamma side.** -/
theorem norm_gammaSide_twist_le (hf : ContDiff ℝ 2 f) (hfs : HasCompactSupport f) {κ q : ℕ}
    (hκ : κ ≤ 1) {y : ℝ} (hy : weilTest f f (-y) = 0) :
    ‖gammaSide κ q (twist (weilTest f f) y)‖ ≤ Ilog f 5 / (2 * π) := by
  set P : ℝ → ℂ := fun r ↦ paperFT (twist (weilTest f f) y) (r : ℂ)
  set ψ : ℝ → ℝ := fun r ↦ (Complex.digamma (1 / 4 + (κ : ℂ) / 2 + I * r / 2)).re
  set L : ℝ := Real.log (q / π)
  have hPn : ∀ r, ‖P r‖ = ‖paperFT f (r : ℂ)‖ ^ 2 := norm_paperFT_twist hf hfs y
  have hmeasP : AEStronglyMeasurable P := by
    have hc : Continuous fun r : ℝ ↦ paperFT (twist (weilTest f f) y) (r : ℂ) := by
      have := (WeilEF.differentiable_paperFT
        ((weilTest_contDiff hf hf.continuous hfs).continuous.comp (continuous_id.sub
          continuous_const)) (hasCompactSupport_twist (weilTest_hasCompactSupport hfs hfs) y))
      exact this.continuous.comp Complex.continuous_ofReal
    exact hc.aestronglyMeasurable
  have hPint : Integrable P :=
    (integrable_normSq_paperFT hf hfs).mono' hmeasP
      (Filter.Eventually.of_forall fun r ↦ (hPn r).le)
  have hdom := GRHMiller.integrable_normSq_paperFT_mul_log hf hfs 1 5
  have hψcont : Continuous fun r : ℝ ↦ ((ψ r : ℝ) : ℂ) := by
    have := GRHMiller.continuous_gammaDensity κ q
    have h2 : Continuous ψ :=
      (this.sub (continuous_const (y := Real.log (q / π)))).congr fun r ↦ by
        simp only [Pi.sub_apply, GRHMiller.gammaDensity, ψ]; ring
    exact Complex.continuous_ofReal.comp h2
  have hPψ : Integrable fun r ↦ P r * ((ψ r : ℝ) : ℂ) := by
    refine hdom.mono' (hmeasP.mul hψcont.aestronglyMeasurable)
      (Filter.Eventually.of_forall fun r ↦ ?_)
    rw [norm_mul, hPn, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (by rw [one_mul]; exact abs_re_digamma_le κ hκ r) (by positivity)
  have hsplit : (∫ r : ℝ, P r * (((ψ r + L : ℝ)) : ℂ)) =
      (∫ r : ℝ, P r * ((ψ r : ℝ) : ℂ)) + (L : ℂ) * ∫ r : ℝ, P r := by
    rw [← integral_const_mul, ← integral_add hPψ (hPint.const_mul _)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun r ↦ ?_)
    simp only [Complex.ofReal_add]; ring
  have hzero : (∫ r : ℝ, P r) = 0 := by
    have h := integral_paperFT_twist hf hfs y
    rw [hy] at h
    have hpi : (1 / (2 * π) : ℂ) ≠ 0 := by
      have := Real.pi_pos; simp only [ne_eq, one_div, inv_eq_zero, mul_eq_zero, OfNat.ofNat_ne_zero,
        Complex.ofReal_eq_zero, false_or]; exact this.ne'
    exact (mul_eq_zero.mp h).resolve_left hpi
  unfold gammaSide
  change ‖(1 / (2 * π) : ℂ) * ∫ r : ℝ, P r * (((ψ r + L : ℝ)) : ℂ)‖ ≤ _
  rw [hsplit, hzero, mul_zero, add_zero, norm_mul]
  have hc : ‖(1 / (2 * π) : ℂ)‖ = 1 / (2 * π) := by
    rw [norm_div, norm_one, norm_mul, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos Real.pi_pos]
  rw [hc, div_eq_mul_one_div (Ilog f 5), mul_comm (Ilog f 5)]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine norm_integral_le_of_norm_le hdom (Filter.Eventually.of_forall fun r ↦ ?_)
  rw [norm_mul, hPn, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (by rw [one_mul]; exact abs_re_digamma_le κ hκ r) (by positivity)

/-- **Untwisted χ gamma side.** -/
theorem re_gammaSide_le (hf : ContDiff ℝ 2 f) (hfs : HasCompactSupport f) {κ q : ℕ}
    (hκ : κ ≤ 1) :
    (gammaSide κ q (weilTest f f)).re ≤
      (weilTest f f 0).re * Real.log (q / π) + Ilog f (1 / 2) / (2 * π) := by
  set F : ℝ → ℝ := fun r ↦ ‖paperFT f (r : ℂ)‖ ^ 2
  set L : ℝ := Real.log (q / π)
  have hG := GRHMiller.gammaTerm_weilTest_self hf.continuous hfs κ q
  unfold gammaSide
  rw [hG, Complex.ofReal_re]
  have hB : Integrable F := integrable_normSq_paperFT hf hfs
  have hD := GRHMiller.integrable_normSq_paperFT_mul_log hf hfs 1 (1 / 2)
  have hpl := GRHMiller.re_weilTest_zero' hf hfs hB
  have hFcont : Continuous F := by
    have := (WeilEF.differentiable_paperFT hf.continuous hfs).continuous.comp
      Complex.continuous_ofReal
    exact this.norm.pow 2
  have hLHS : Integrable fun r ↦ F r * GRHMiller.gammaDensity κ q r := by
    refine (GRHMiller.integrable_normSq_paperFT_mul_log hf hfs 1 (5 + |L|)).mono'
      (hFcont.mul (GRHMiller.continuous_gammaDensity κ q)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun r ↦ ?_)
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ F r)]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    unfold GRHMiller.gammaDensity
    have := abs_re_digamma_le κ hκ r
    calc |(Complex.digamma (1 / 4 + (κ : ℂ) / 2 + I * r / 2)).re + L|
        ≤ |(Complex.digamma (1 / 4 + (κ : ℂ) / 2 + I * r / 2)).re| + |L| := abs_add_le _ _
      _ ≤ 1 * Real.log (4 + |r|) + (5 + |L|) := by linarith
  have hle : ∫ r : ℝ, F r * GRHMiller.gammaDensity κ q r ≤
      ∫ r : ℝ, (F r * (1 * Real.log (4 + |r|) + 1 / 2) + L * F r) := by
    refine integral_mono hLHS (hD.add (hB.const_mul L)) fun r ↦ ?_
    unfold GRHMiller.gammaDensity
    have := GRHMiller.re_digamma_gammaFactor_le_half κ hκ r
    have hF0 : 0 ≤ F r := by positivity
    nlinarith
  rw [integral_add hD (hB.const_mul L), integral_const_mul] at hle
  have hpi : 0 < 2 * π := by positivity
  have hk0 : (weilTest f f 0).re * (2 * π) = ∫ r : ℝ, F r := by
    have hπ : π ≠ 0 := Real.pi_ne_zero
    rw [hpl]; field_simp
    rfl
  unfold Ilog
  calc 1 / (2 * π) * ∫ r : ℝ, F r * GRHMiller.gammaDensity κ q r
      ≤ 1 / (2 * π) * ((∫ r : ℝ, F r * (1 * Real.log (4 + |r|) + 1 / 2)) + L * ∫ r : ℝ, F r) :=
        mul_le_mul_of_nonneg_left hle (by positivity)
    _ = (weilTest f f 0).re * L + (∫ r : ℝ, F r * (1 * Real.log (4 + |r|) + 1 / 2)) / (2 * π) := by
        rw [← hk0]; field_simp; ring


/-- `|gammaBracket r| ≤ log(4+|r|) + 5 + log π`. -/
lemma abs_gammaBracket_le (r : ℝ) : |gammaBracket r| ≤ Real.log (4 + |r|) + (5 + Real.log π) := by
  have h := abs_re_digamma_le 0 (by norm_num) r
  have harg : (1 / 4 + ((0 : ℕ) : ℂ) / 2 + I * r / 2) = 1 / 4 + I * r / 2 := by push_cast; ring
  rw [harg] at h
  have hπ : 0 ≤ Real.log π := Real.log_nonneg (by linarith [Real.pi_gt_three])
  unfold gammaBracket
  calc |(Complex.digamma (1 / 4 + I * r / 2)).re - Real.log π|
      ≤ |(Complex.digamma (1 / 4 + I * r / 2)).re| + |Real.log π| := abs_sub _ _
    _ ≤ _ := by rw [abs_of_nonneg hπ]; linarith

lemma gammaBracket_eq : gammaBracket = GRHMiller.gammaDensity 0 1 := by
  funext r
  unfold gammaBracket GRHMiller.gammaDensity
  have harg : (1 / 4 + ((0 : ℕ) : ℂ) / 2 + I * r / 2) = 1 / 4 + I * r / 2 := by push_cast; ring
  rw [harg, Nat.cast_one, Real.log_div one_ne_zero Real.pi_ne_zero, Real.log_one]
  ring

lemma continuous_gammaBracket : Continuous gammaBracket :=
  gammaBracket_eq ▸ GRHMiller.continuous_gammaDensity 0 1

/-- **Twisted ζ gamma side.** -/
theorem norm_gammaSideZeta_twist_le (hf : ContDiff ℝ 2 f) (hfs : HasCompactSupport f) (y : ℝ) :
    ‖gammaSideZeta (twist (weilTest f f) y)‖ ≤ Ilog f (5 + Real.log π) / (2 * π) := by
  have hPn := norm_paperFT_twist hf hfs y
  have hdom := GRHMiller.integrable_normSq_paperFT_mul_log hf hfs 1 (5 + Real.log π)
  unfold gammaSideZeta
  rw [norm_mul]
  have hc : ‖(1 / (2 * π) : ℂ)‖ = 1 / (2 * π) := by
    rw [norm_div, norm_one, norm_mul, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos Real.pi_pos]
  rw [hc, div_eq_mul_one_div (Ilog f _), mul_comm (Ilog f _)]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine norm_integral_le_of_norm_le hdom (Filter.Eventually.of_forall fun r ↦ ?_)
  rw [norm_mul, hPn, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (by rw [one_mul]; exact abs_gammaBracket_le r) (by positivity)

/-- **Untwisted ζ gamma side.** -/
theorem re_gammaSideZeta_le (hf : ContDiff ℝ 2 f) (hfs : HasCompactSupport f) :
    (gammaSideZeta (weilTest f f)).re ≤ Ilog f (1 / 2) / (2 * π) := by
  set F : ℝ → ℝ := fun r ↦ ‖paperFT f (r : ℂ)‖ ^ 2
  have hD := GRHMiller.integrable_normSq_paperFT_mul_log hf hfs 1 (1 / 2)
  have hFcont : Continuous F := by
    have := (WeilEF.differentiable_paperFT hf.continuous hfs).continuous.comp
      Complex.continuous_ofReal
    exact this.norm.pow 2
  have hint : Integrable fun r ↦ F r * gammaBracket r := by
    refine (GRHMiller.integrable_normSq_paperFT_mul_log hf hfs 1 (5 + Real.log π)).mono'
      (hFcont.mul continuous_gammaBracket).aestronglyMeasurable
      (Filter.Eventually.of_forall fun r ↦ ?_)
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ F r)]
    exact mul_le_mul_of_nonneg_left (by rw [one_mul]; exact abs_gammaBracket_le r) (by positivity)
  have heq : gammaSideZeta (weilTest f f) =
      (((1 / (2 * π)) * ∫ r : ℝ, F r * gammaBracket r : ℝ) : ℂ) := by
    unfold gammaSideZeta
    simp_rw [paperFT_weilTest_real hf hfs]
    rw [Complex.ofReal_mul, ← integral_complex_ofReal]
    congr 1
    · push_cast; ring
    · refine integral_congr_ae (Filter.Eventually.of_forall fun r ↦ ?_)
      simp only [F]; push_cast; ring
  rw [heq, Complex.ofReal_re, div_eq_mul_one_div (Ilog f _), mul_comm (Ilog f _)]
  refine mul_le_mul_of_nonneg_left (integral_mono hint hD fun r ↦ ?_) (by positivity)
  have hψ := GRHMiller.re_digamma_gammaFactor_le_half 0 (by norm_num) r
  have harg : (1 / 4 + ((0 : ℕ) : ℂ) / 2 + I * r / 2) = 1 / 4 + I * r / 2 := by push_cast; ring
  rw [harg] at hψ
  have hπ : 0 ≤ Real.log π := Real.log_nonneg (by linarith [Real.pi_gt_three])
  have hF0 : 0 ≤ F r := by positivity
  unfold gammaBracket
  nlinarith

end GRHPseudo.Sharp
