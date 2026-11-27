/- Vendored from github.com/amrehan/grh-miller v1.0.0 (commit e3e573a), `GRHMiller/Ankeny.lean`
   (Apache-2.0). Only import paths changed. See ATTRIBUTION.md. -/
import GRHPseudo.Vendor.GRHMiller.Hypothesis
import Zeta23.ThmE.MainChi
import Zeta23.XiPrime.ExplicitFormula.ZeroFree
import Zeta23.Poisson.PaperFT
import Zeta23.Taper.Decay
import Zeta23.GammaFacts.Mu
import Zeta23.GammaFacts.StirlingVert

/-!
# GRH ⇒ an explicit Ankeny-type inequality; Miller–Rabin witness theory

GRH enters only through `DirichletLZerosOnLine` (`GRHMiller/Hypothesis.lean`, a verbatim copy of Alpöge's statement).
Analytic input: the Weil explicit formula `Zeta23.ThmE.EF_lit_chi_L` (anthropics/zeta-23-lean). The explicit
constant is assembled in `GRHMiller/Explicit.lean`.
-/

noncomputable section

open Complex Zeta23 Zeta23.EF Zeta23.ThmE
open scoped Real

set_option autoImplicit false

namespace GRHMiller

section CoreSection
open MeasureTheory (Integrable)


/-- On the critical line the ordinate `γ = (ρ - 1/2)/i` is the real number `Im ρ`. -/
theorem gammaOf_eq_im_of_re {ρ : ℂ} (h : ρ.re = 1 / 2) : gammaOf ρ = ((ρ.im : ℝ) : ℂ) := by
  apply Complex.ext <;> simp [gammaOf, h]

/-- At real points, the Fourier transform of `f ⋆ f̃` is `|f̂|²`. -/
theorem paperFT_weilTest_self_ofReal {f : ℝ → ℂ} (hf : Continuous f) (hfs : HasCompactSupport f)
    (t : ℝ) : paperFT (weilTest f f) (t : ℂ) = ((‖paperFT f (t : ℂ)‖ ^ 2 : ℝ) : ℂ) := by
  rw [paperFT_weilTest hf hf hfs hfs, Complex.conj_ofReal, Complex.mul_conj,
    Complex.normSq_eq_norm_sq]

variable {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}

/-- **Lemma 1.** Under GRH, the zero side of the explicit formula for `k = f ⋆ f̃` is the real
number `Σ_ρ m_ρ |f̂(γ_ρ)|²`, which is nonnegative. -/
theorem zeroSide_eq_ofReal_nonneg (hGRH : DirichletLZerosOnLine) (hq : 1 < q)
    (hprim : χ.IsPrimitive) {f : ℝ → ℂ} (hf : Continuous f) (hfs : HasCompactSupport f) :
    ∃ S : ℝ, 0 ≤ S ∧
      ∑' ρ : (LZeros (LSeam_of hq hprim)).carrier,
        ((LZeros (LSeam_of hq hprim)).mult ρ : ℂ) * paperFT (weilTest f f) (gammaOf ρ) =
      (S : ℂ) := by
  set Z := LZeros (LSeam_of hq hprim)
  have hterm : ∀ ρ : Z.carrier,
      (Z.mult ρ : ℂ) * paperFT (weilTest f f) (gammaOf ρ) =
        (((Z.mult ρ : ℝ) * ‖paperFT f (((ρ : ℂ).im : ℝ) : ℂ)‖ ^ 2 : ℝ) : ℂ) := by
    rintro ⟨ρ, hρ⟩
    have hz : IsNontrivialZeroL χ ρ := hρ
    have hre : ρ.re = 1 / 2 := hGRH q χ ρ hz.2.1 hz.2.2 hz.1
    rw [gammaOf_eq_im_of_re hre, paperFT_weilTest_self_ofReal hf hfs]
    push_cast
    rfl
  refine ⟨∑' ρ : Z.carrier, (Z.mult ρ : ℝ) * ‖paperFT f (((ρ : ℂ).im : ℝ) : ℂ)‖ ^ 2,
    tsum_nonneg fun ρ ↦ by positivity, ?_⟩
  rw [tsum_congr hterm, Complex.ofReal_tsum]

/-- **Master inequality.** Under GRH, for primitive `χ` mod `q > 1` and every `f ∈ C_c²(ℝ)`, the
right-hand side of the explicit formula for `k = f ⋆ f̃` has nonnegative real part:
`Re[ −Σ Λ(n)n^{-1/2}(χ(n)k(log n) + conj χ(n) k(−log n)) + Γ-term ] ≥ 0`,
i.e. the prime side is at most the Gamma side. -/
theorem master_inequality (hGRH : DirichletLZerosOnLine) (hq : 1 < q) (hprim : χ.IsPrimitive)
    {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f) (hfs : HasCompactSupport f) :
    0 ≤ (literatureRHSchi (parity χ) q (coeff χ) (weilTest f f)).re := by
  obtain ⟨-, heq⟩ := EF_lit_chi_L hq hprim (weilTest f f)
    (weilTest_contDiff hf hf.continuous hfs) (weilTest_hasCompactSupport hfs hfs)
  obtain ⟨S, hS, hSeq⟩ := zeroSide_eq_ofReal_nonneg hGRH hq hprim hf.continuous hfs
  rw [← heq, hSeq, Complex.ofReal_re]
  exact hS


/-! ## Lemma 3b: the Gamma side, and the combined bound -/

/-- The Gamma-factor density appearing in the explicit formula. -/
def gammaDensity (κ q : ℕ) (r : ℝ) : ℝ :=
  (Complex.digamma (1 / 4 + (κ : ℂ) / 2 + I * r / 2)).re + Real.log (q / π)

/-- For `k = f ⋆ f̃`, the Gamma term of the explicit formula is the real number
`(1/2π) ∫ |f̂(r)|² · gammaDensity(r) dr`. -/
theorem gammaTerm_weilTest_self {f : ℝ → ℂ} (hf : Continuous f) (hfs : HasCompactSupport f)
    (κ q : ℕ) :
    (1 / (2 * π) : ℂ) * ∫ r : ℝ, paperFT (weilTest f f) r
        * ((((Complex.digamma (1 / 4 + (κ : ℂ) / 2 + I * r / 2)).re + Real.log (q / π) : ℝ)) : ℂ)
      = (((1 / (2 * π)) * ∫ r : ℝ, ‖paperFT f (r : ℂ)‖ ^ 2 * gammaDensity κ q r : ℝ) : ℂ) := by
  simp_rw [paperFT_weilTest_self_ofReal hf hfs, ← Complex.ofReal_mul]
  rw [integral_complex_ofReal]
  push_cast
  rfl

/-! ## Lemma 2a: the prime side when χ is trivial on small units -/

/-- `k = f ⋆ f̃` is Hermitian: `k(−u) = conj k(u)` (substitute `t ↦ t + u`). -/
theorem weilTest_self_neg (f : ℝ → ℂ) (u : ℝ) :
    weilTest f f (-u) = (starRingEnd ℂ) (weilTest f f u) := by
  simp only [weilTest, MeasureTheory.convolution_def, ContinuousLinearMap.mul_apply', tilde]
  rw [← integral_conj, ← MeasureTheory.integral_add_right_eq_self
    (μ := MeasureTheory.volume)
    (fun t ↦ (starRingEnd ℂ) (f t * (starRingEnd ℂ) (f (-(u - t))))) u]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun t ↦ ?_)
  simp only [map_mul, Complex.conj_conj]
  rw [mul_comm]
  congr 3 <;> ring

/-! ## The conditional Ankeny inequality -/

/-- Algebra: from `a ≤ C₀`, `a t² ≤ C₂`, the quantity `a²(1+t²)(1+t)` is bounded. -/
theorem sq_mul_poly_le {a t C₀ C₂ : ℝ} (ha : 0 ≤ a) (ht : 0 ≤ t) (h0 : a ≤ C₀) (h2 : a * t ^ 2 ≤ C₂) :
    a ^ 2 * ((1 + t ^ 2) * (1 + t)) ≤
      C₀ ^ 2 + C₀ * (C₀ + C₂) + C₀ * C₂ + C₂ * (C₀ + C₂) := by
  have hC₀ : 0 ≤ C₀ := ha.trans h0
  have hC₂ : 0 ≤ C₂ := (by positivity : 0 ≤ a * t ^ 2).trans h2
  have h1 : a * t ≤ C₀ + C₂ := by
    have : t ≤ 1 + t ^ 2 := by nlinarith [sq_nonneg (t - 1)]
    nlinarith
  have hat : 0 ≤ a * t := by positivity
  have e1 : a ^ 2 ≤ C₀ ^ 2 := by nlinarith
  have e2 : a ^ 2 * t ≤ C₀ * (C₀ + C₂) := by
    have := mul_le_mul h0 h1 hat hC₀; nlinarith
  have e3 : a ^ 2 * t ^ 2 ≤ C₀ * C₂ := by
    have := mul_le_mul h0 h2 (by positivity) hC₀; nlinarith
  have e4 : a ^ 2 * t ^ 3 ≤ C₂ * (C₀ + C₂) := by
    have := mul_le_mul h2 h1 hat hC₂; nlinarith
  nlinarith

/-- For `f ∈ C_c²`, `r ↦ |f̂(r)|² (A log(4+|r|) + B)` is integrable. -/
theorem integrable_normSq_paperFT_mul_log {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f)
    (hfs : HasCompactSupport f) (A B : ℝ) :
    MeasureTheory.Integrable (fun r : ℝ ↦ ‖paperFT f (r : ℂ)‖ ^ 2 * (A * Real.log (4 + |r|) + B)) := by
  obtain ⟨Λ, hΛ⟩ : ∃ Λ : ℝ, ∀ u, f u ≠ 0 → |u| ≤ Λ := by
    obtain ⟨R, hR⟩ := hfs.isCompact.isBounded.subset_closedBall 0
    exact ⟨R, fun u hu ↦ by
      have := hR (subset_tsupport f (Function.mem_support.mpr hu))
      simpa [Metric.mem_closedBall, Real.dist_eq] using this⟩
  have hfi : Integrable f := hf.continuous.integrable_of_hasCompactSupport hfs
  set C₀ : ℝ := ∫ u, ‖f u‖
  set C₂ : ℝ := ∫ u, ‖deriv (deriv f) u‖
  have hG0 : ∀ r : ℝ, ‖paperFT f r‖ ≤ C₀ := fun r ↦ by
    simpa using norm_paperFT_le hfi hΛ (r : ℂ)
  have hG2 : ∀ r : ℝ, ‖paperFT f r‖ * |r| ^ 2 ≤ C₂ := fun r ↦ by
    simpa [Complex.norm_real, Real.norm_eq_abs] using norm_paperFT_mul_sq_le hf hΛ (r : ℂ)
  have hcont : Continuous (fun r : ℝ ↦ paperFT f (r : ℂ)) :=
    (WeilEF.differentiable_paperFT hf.continuous hfs).continuous.comp Complex.continuous_ofReal
  set M : ℝ := 4 * |A| + |B|
  refine MeasureTheory.Integrable.mono' ((integrable_inv_one_add_sq).const_mul
      (M * (C₀ ^ 2 + C₀ * (C₀ + C₂) + C₀ * C₂ + C₂ * (C₀ + C₂))))
    ((hcont.norm.pow 2).mul ((continuous_const.mul ((by fun_prop : Continuous
      (fun r : ℝ ↦ 4 + |r|)).log fun r ↦ by positivity)).add continuous_const)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun r ↦ ?_)
  have ht : 0 ≤ |r| := abs_nonneg r
  have hlog : |A * Real.log (4 + |r|) + B| ≤ M * (1 + |r|) := by
    have h1 : 0 ≤ Real.log (4 + |r|) := Real.log_nonneg (by linarith)
    have h2 : Real.log (4 + |r|) ≤ 4 + |r| := (Real.log_le_sub_one_of_pos (by positivity)).trans
      (by linarith)
    calc |A * Real.log (4 + |r|) + B| ≤ |A| * Real.log (4 + |r|) + |B| := by
          refine (abs_add_le _ _).trans ?_
          rw [abs_mul, abs_of_nonneg h1]
      _ ≤ |A| * (4 + |r|) + |B| := by gcongr
      _ ≤ M * (1 + |r|) := by
          simp only [M]; nlinarith [abs_nonneg A, abs_nonneg B]
  have hpoly := sq_mul_poly_le (norm_nonneg _) ht (hG0 r) (hG2 r)
  have hpos : 0 < 1 + r ^ 2 := by positivity
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ ‖paperFT f r‖ ^ 2),
    ← div_eq_mul_inv, le_div_iff₀ hpos, sq_abs] at *
  have hM : 0 ≤ M := by positivity
  calc ‖paperFT f r‖ ^ 2 * |A * Real.log (4 + |r|) + B| * (1 + r ^ 2)
      ≤ ‖paperFT f r‖ ^ 2 * (M * (1 + |r|)) * (1 + r ^ 2) := by gcongr
    _ = M * (‖paperFT f r‖ ^ 2 * ((1 + |r| ^ 2) * (1 + |r|))) := by rw [sq_abs]; ring
    _ ≤ M * (C₀ ^ 2 + C₀ * (C₀ + C₂) + C₀ * C₂ + C₂ * (C₀ + C₂)) := by
        rw [sq_abs]; exact mul_le_mul_of_nonneg_left hpoly hM


/-- Two-sided bound: `|Re ψ(1/4 + κ/2 + ir/2)| ≤ C log(4+|r|) + 4` for κ ≤ 1. -/
theorem abs_re_digamma_gammaFactor_le {C : ℝ} (hC0 : 0 < C)
    (hb : ∀ z : ℂ, 1 / 2 ≤ z.re → ‖Complex.digamma z‖ ≤ C * Real.log (2 + ‖z‖))
    {κ : ℕ} (hκ : κ ≤ 1) (r : ℝ) :
    |(Complex.digamma (1 / 4 + (κ : ℂ) / 2 + I * r / 2)).re| ≤ C * Real.log (4 + |r|) + 4 := by
  set z : ℂ := 1 / 4 + (κ : ℂ) / 2 + I * r / 2 with hz
  have hκ' : (κ : ℝ) ≤ 1 := by exact_mod_cast hκ
  have hzre : z.re = 1 / 4 + (κ : ℝ) / 2 := by simp [hz]
  have hzim : z.im = r / 2 := by simp [hz]
  have hκ0 : (0 : ℝ) ≤ (κ : ℝ) / 2 := by positivity
  have hz0 : 0 < z.re := by rw [hzre]; positivity
  have hz1 : 1 / 2 ≤ (z + 1).re := by rw [Complex.add_re, hzre, Complex.one_re]; linarith
  have hnorm : ‖z + 1‖ ≤ 2 + |r| := by
    refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
    rw [Complex.add_re, Complex.add_im, hzre, hzim, Complex.one_re, Complex.one_im, add_zero,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / 4 + (κ : ℝ) / 2 + 1), abs_div,
      abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    linarith [abs_nonneg r]
  have hψ1 : ‖Complex.digamma (z + 1)‖ ≤ C * Real.log (4 + |r|) :=
    (hb _ hz1).trans (mul_le_mul_of_nonneg_left
      (Real.log_le_log (by positivity) (by linarith)) hC0.le)
  have hrec := Zeta23.XiPrime.ZeroFree.digamma_add_nat hz0 1
  simp only [Nat.cast_one, Finset.range_one, Finset.sum_singleton, Nat.cast_zero, add_zero,
    one_div] at hrec
  have hinv : ‖z⁻¹‖ ≤ 4 := by
    rw [norm_inv]
    have : 1 / 4 ≤ ‖z‖ := (by rw [hzre]; linarith : (1 : ℝ) / 4 ≤ z.re).trans
      ((le_abs_self _).trans (Complex.abs_re_le_norm z))
    rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
  have hre : (Complex.digamma z).re = (Complex.digamma (z + 1)).re - (z⁻¹).re := by
    rw [hrec, Complex.add_re]; ring
  rw [hre, abs_le]
  have h1 := Complex.abs_re_le_norm (Complex.digamma (z + 1))
  have h2 := Complex.abs_re_le_norm z⁻¹
  constructor <;> [skip; skip] <;>
    nlinarith [abs_le.mp h1, abs_le.mp h2, abs_nonneg (Complex.digamma (z + 1)).re]

/-- `r ↦ gammaDensity κ q r` is continuous. -/
theorem continuous_gammaDensity (κ q : ℕ) : Continuous (gammaDensity κ q) := by
  unfold gammaDensity
  refine Continuous.add ?_ continuous_const
  refine Complex.continuous_re.comp (continuous_iff_continuousAt.2 fun r ↦ ?_)
  have hz : 0 < (1 / 4 + (κ : ℂ) / 2 + I * (r : ℂ) / 2).re := by simp; positivity
  exact (Zeta23.XiPrime.ZeroFree.differentiableAt_digamma hz).continuousAt.comp
    (f := fun r : ℝ ↦ 1 / 4 + (κ : ℂ) / 2 + I * (r : ℂ) / 2) (by fun_prop)

/-- For `f ∈ C_c²`, `|f̂|² · gammaDensity` is integrable. -/
theorem integrable_normSq_paperFT_mul_gammaDensity {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f)
    (hfs : HasCompactSupport f) {κ : ℕ} (hκ : κ ≤ 1) (q : ℕ) :
    MeasureTheory.Integrable (fun r : ℝ ↦ ‖paperFT f (r : ℂ)‖ ^ 2 * gammaDensity κ q r) := by
  obtain ⟨C, hC0, hb⟩ := Zeta23.XiPrime.ZeroFree.norm_digamma_le
  have hcont : Continuous (fun r : ℝ ↦ paperFT f (r : ℂ)) :=
    (WeilEF.differentiable_paperFT hf.continuous hfs).continuous.comp Complex.continuous_ofReal
  refine (integrable_normSq_paperFT_mul_log hf hfs C (4 + |Real.log (q / π)|)).mono'
    ((hcont.norm.pow 2).mul (continuous_gammaDensity κ q)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun r ↦ ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ ‖paperFT f r‖ ^ 2)]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  unfold gammaDensity
  refine (abs_add_le _ _).trans ?_
  linarith [abs_re_digamma_gammaFactor_le hC0 hb hκ r]

end CoreSection


section RHSSection
open MeasureTheory


/-- `r ↦ log(4+|r|)/(1+r²)` is integrable. -/
theorem integrable_log_mul_inv_one_add_sq :
    Integrable (fun r : ℝ ↦ Real.log (4 + |r|) * (1 + r ^ 2)⁻¹) := by
  have hmaj : Integrable (fun r : ℝ ↦ (4 * (5 : ℝ) ^ (1 / 4 : ℝ)) *
      ((1 : ℝ) + ‖r‖ ^ 2) ^ (-(3 / 2 : ℝ) / 2)) :=
    (integrable_rpow_neg_one_add_norm_sq (by norm_num)).const_mul _
  refine hmaj.mono' (by
    have : Continuous (fun r : ℝ ↦ Real.log (4 + |r|)) :=
      (by fun_prop : Continuous (fun r : ℝ ↦ 4 + |r|)).log fun r ↦ by positivity
    exact (this.mul ((by fun_prop : Continuous (fun r : ℝ ↦ 1 + r ^ 2)).inv₀
      fun r ↦ by positivity)).aestronglyMeasurable) (Filter.Eventually.of_forall fun r ↦ ?_)
  have hx : 0 < 1 + r ^ 2 := by positivity
  have hlog0 : 0 ≤ Real.log (4 + |r|) := Real.log_nonneg (by linarith [abs_nonneg r])
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), Real.norm_eq_abs, sq_abs]
  have h1 : Real.log (4 + |r|) ≤ Real.log (5 * (1 + r ^ 2)) :=
    Real.log_le_log (by positivity) (by nlinarith [abs_nonneg r, sq_abs r, abs_mul_abs_self r])
  have h2 : Real.log (5 * (1 + r ^ 2)) ≤ (5 * (1 + r ^ 2)) ^ (1 / 4 : ℝ) / (1 / 4) :=
    Real.log_le_rpow_div (by positivity) (by norm_num)
  have h3 : (5 * (1 + r ^ 2)) ^ (1 / 4 : ℝ) / (1 / 4) * (1 + r ^ 2)⁻¹
      = 4 * (5 : ℝ) ^ (1 / 4 : ℝ) * (1 + r ^ 2) ^ (-(3 / 2 : ℝ) / 2) := by
    rw [Real.mul_rpow (by norm_num) hx.le, ← Real.rpow_neg_one, div_eq_mul_inv]
    have : (1 + r ^ 2) ^ (-(3 / 2 : ℝ) / 2) = (1 + r ^ 2) ^ (1 / 4 : ℝ) * (1 + r ^ 2) ^ (-1 : ℝ) := by
      rw [← Real.rpow_add hx]; norm_num
    rw [this]; ring
  calc Real.log (4 + |r|) * (1 + r ^ 2)⁻¹
      ≤ (5 * (1 + r ^ 2)) ^ (1 / 4 : ℝ) / (1 / 4) * (1 + r ^ 2)⁻¹ :=
        mul_le_mul_of_nonneg_right (h1.trans h2) (by positivity)
    _ = _ := h3

/-- The fixed constant `J = ∫ log(4+|r|)/(1+r²) dr`. -/
def Jconst : ℝ := ∫ r : ℝ, Real.log (4 + |r|) * (1 + r ^ 2)⁻¹

/-- **Gamma-side upper bound.** If `|f̂| ≤ C₀` and `|f̂(r)|·|r| ≤ C₁` on ℝ, then
`∫ |f̂|² (A log(4+|r|) + B) ≤ (C₀² + C₁²)(A·J + B·π)` for `A, B ≥ 0`. -/
theorem integral_normSq_paperFT_mul_le {f : ℝ → ℂ} {C₀ C₁ A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hcont : Continuous (fun r : ℝ ↦ paperFT f (r : ℂ)))
    (h0 : ∀ r : ℝ, ‖paperFT f (r : ℂ)‖ ≤ C₀) (h1 : ∀ r : ℝ, ‖paperFT f (r : ℂ)‖ * |r| ≤ C₁) :
    ∫ r : ℝ, ‖paperFT f (r : ℂ)‖ ^ 2 * (A * Real.log (4 + |r|) + B)
      ≤ (C₀ ^ 2 + C₁ ^ 2) * (A * Jconst + B * π) := by
  have hJ := integrable_log_mul_inv_one_add_sq
  have hP := integrable_inv_one_add_sq
  have hmaj : Integrable (fun r : ℝ ↦ (C₀ ^ 2 + C₁ ^ 2) *
      (A * (Real.log (4 + |r|) * (1 + r ^ 2)⁻¹) + B * (1 + r ^ 2)⁻¹)) :=
    ((hJ.const_mul A).add (hP.const_mul B)).const_mul _
  have hpt : ∀ r : ℝ, ‖paperFT f (r : ℂ)‖ ^ 2 * (A * Real.log (4 + |r|) + B)
      ≤ (C₀ ^ 2 + C₁ ^ 2) * (A * (Real.log (4 + |r|) * (1 + r ^ 2)⁻¹) + B * (1 + r ^ 2)⁻¹) := by
    intro r
    have hx : 0 < 1 + r ^ 2 := by positivity
    have hn := norm_nonneg (paperFT f (r : ℂ))
    have hC0 : 0 ≤ C₀ := hn.trans (h0 r)
    have hw : 0 ≤ A * Real.log (4 + |r|) + B :=
      add_nonneg (mul_nonneg hA (Real.log_nonneg (by linarith [abs_nonneg r]))) hB
    have hsq : ‖paperFT f (r : ℂ)‖ ^ 2 * (1 + r ^ 2) ≤ C₀ ^ 2 + C₁ ^ 2 := by
      have e0 : ‖paperFT f (r : ℂ)‖ ^ 2 ≤ C₀ ^ 2 := pow_le_pow_left₀ hn (h0 r) 2
      have e1 : (‖paperFT f (r : ℂ)‖ * |r|) ^ 2 ≤ C₁ ^ 2 :=
        pow_le_pow_left₀ (by positivity) (h1 r) 2
      rw [mul_pow, sq_abs] at e1
      nlinarith
    have : ‖paperFT f (r : ℂ)‖ ^ 2 ≤ (C₀ ^ 2 + C₁ ^ 2) * (1 + r ^ 2)⁻¹ := by
      rw [← div_eq_mul_inv, le_div_iff₀ hx]; exact hsq
    calc ‖paperFT f (r : ℂ)‖ ^ 2 * (A * Real.log (4 + |r|) + B)
        ≤ (C₀ ^ 2 + C₁ ^ 2) * (1 + r ^ 2)⁻¹ * (A * Real.log (4 + |r|) + B) :=
          mul_le_mul_of_nonneg_right this hw
      _ = _ := by ring
  have hlhs : Integrable (fun r : ℝ ↦ ‖paperFT f (r : ℂ)‖ ^ 2 * (A * Real.log (4 + |r|) + B)) := by
    refine hmaj.mono' ((hcont.norm.pow 2).mul (continuous_const.mul ((by fun_prop :
      Continuous (fun r : ℝ ↦ 4 + |r|)).log fun r ↦ by positivity) |>.add continuous_const)
      ).aestronglyMeasurable (Filter.Eventually.of_forall fun r ↦ ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by positivity)
      (add_nonneg (mul_nonneg hA (Real.log_nonneg (by linarith [abs_nonneg r]))) hB))]
    exact hpt r
  calc ∫ r : ℝ, ‖paperFT f (r : ℂ)‖ ^ 2 * (A * Real.log (4 + |r|) + B)
      ≤ ∫ r : ℝ, (C₀ ^ 2 + C₁ ^ 2) *
          (A * (Real.log (4 + |r|) * (1 + r ^ 2)⁻¹) + B * (1 + r ^ 2)⁻¹) :=
        integral_mono hlhs hmaj hpt
    _ = (C₀ ^ 2 + C₁ ^ 2) * (A * Jconst + B * π) := by
        rw [integral_const_mul, integral_add (hJ.const_mul A) (hP.const_mul B),
          integral_const_mul, integral_const_mul, integral_univ_inv_one_add_sq, Jconst]


end RHSSection


section Assembly
open MeasureTheory

/-- `exp(log n / 2) = √n` for `n > 0`. -/
theorem exp_log_div_two {x : ℝ} (hx : 0 < x) : Real.exp (Real.log x / 2) = Real.sqrt x := by
  rw [← Real.log_sqrt hx.le, Real.exp_log (Real.sqrt_pos.mpr hx)]

end Assembly


section RealHelpers


/-- `ω(q) log 2 ≤ log q`. -/
theorem card_primeFactors_mul_log_two_le (q : ℕ) (hq : q ≠ 0) :
    (q.primeFactors.card : ℝ) * Real.log 2 ≤ Real.log q := by
  have h1 : 2 ^ q.primeFactors.card ≤ q := by
    calc 2 ^ q.primeFactors.card ≤ ∏ p ∈ q.primeFactors, p :=
          Finset.pow_card_le_prod _ _ _ fun p hp ↦ (Nat.prime_of_mem_primeFactors hp).two_le
      _ ≤ q := Nat.le_of_dvd (Nat.pos_of_ne_zero hq) (Nat.prod_primeFactors_dvd q)
  have h2 : ((2 : ℝ) ^ q.primeFactors.card) ≤ q := by exact_mod_cast h1
  calc (q.primeFactors.card : ℝ) * Real.log 2 = Real.log (2 ^ q.primeFactors.card) := by
        rw [Real.log_pow]
    _ ≤ Real.log q := Real.log_le_log (by positivity) h2

/-- `log₂ N · log 2 ≤ log N`. -/
theorem natLog_two_mul_log_two_le (N : ℕ) : (Nat.log 2 N : ℝ) * Real.log 2 ≤ Real.log N := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp
  have h : 2 ^ Nat.log 2 N ≤ N := Nat.pow_log_le_self 2 hN.ne'
  have h2 : ((2 : ℝ) ^ Nat.log 2 N) ≤ N := by exact_mod_cast h
  calc (Nat.log 2 N : ℝ) * Real.log 2 = Real.log (2 ^ Nat.log 2 N) := by rw [Real.log_pow]
    _ ≤ Real.log N := Real.log_le_log (by positivity) h2

end RealHelpers

section T1

/-- `J ≥ 0`. -/
theorem Jconst_nonneg : 0 ≤ Jconst :=
  MeasureTheory.integral_nonneg fun r ↦ mul_nonneg
    (Real.log_nonneg (by linarith [abs_nonneg r])) (inv_nonneg.mpr (by positivity))

end T1


section T2


open MeasureTheory

/-- Prime side when `χ ≡ 1` only on units mod a multiple `Q` of the level: lower bound by the
unit terms minus the non-unit terms. -/
theorem primeSum_re_ge_of_trivial_mod {q Q : ℕ} [NeZero q] [NeZero Q] {χ : DirichletCharacter ℂ q}
    {k : ℝ → ℂ} (hherm : ∀ u, k (-u) = (starRingEnd ℂ) (k u)) {L : ℝ}
    (hks : tsupport k ⊆ Set.Icc (-L) L)
    (hχ : ∀ n : ℕ, n ∈ Finset.Ioc 0 ⌊Real.exp L⌋₊ → IsUnit (n : ZMod Q) → χ n = 1) :
    ∑ n ∈ (Finset.Ioc 0 ⌊Real.exp L⌋₊).filter (fun n : ℕ ↦ IsUnit (n : ZMod Q)),
        ArithmeticFunction.vonMangoldt n / Real.sqrt n * (2 * (k (Real.log n)).re)
      - ∑ n ∈ (Finset.Ioc 0 ⌊Real.exp L⌋₊).filter (fun n : ℕ ↦ ¬ IsUnit (n : ZMod Q)),
        ArithmeticFunction.vonMangoldt n / Real.sqrt n * (2 * ‖k (Real.log n)‖)
      ≤ (∑' n : ℕ, ((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ)
        * (coeff χ n * k (Real.log n) + (starRingEnd ℂ) (coeff χ n) * k (-Real.log n))).re := by
  classical
  rw [tsum_eq_sum (s := Finset.Ioc 0 ⌊Real.exp L⌋₊) (fun n hn ↦ prime_summand_chi_eq_zero hks hn),
    Complex.re_sum, ← Finset.sum_filter_add_sum_filter_not (Finset.Ioc 0 ⌊Real.exp L⌋₊)
      (fun n : ℕ ↦ IsUnit (n : ZMod Q))]
  have hre : ∀ n : ℕ, (((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ)
      * (coeff χ n * k (Real.log n) + (starRingEnd ℂ) (coeff χ n) * k (-Real.log n))).re
      = ArithmeticFunction.vonMangoldt n / Real.sqrt n * (2 * (coeff χ n * k (Real.log n)).re) := by
    intro n
    rw [hherm, ← map_mul, Complex.add_conj, ← Complex.ofReal_mul, Complex.ofReal_re]
  have h1 : ∑ n ∈ (Finset.Ioc 0 ⌊Real.exp L⌋₊).filter (fun n : ℕ ↦ IsUnit (n : ZMod Q)),
      (((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ)
        * (coeff χ n * k (Real.log n) + (starRingEnd ℂ) (coeff χ n) * k (-Real.log n))).re
      = ∑ n ∈ (Finset.Ioc 0 ⌊Real.exp L⌋₊).filter (fun n : ℕ ↦ IsUnit (n : ZMod Q)),
        ArithmeticFunction.vonMangoldt n / Real.sqrt n * (2 * (k (Real.log n)).re) := by
    refine Finset.sum_congr rfl fun n hn ↦ ?_
    have hc : coeff χ n = 1 := hχ n (Finset.mem_filter.mp hn).1 (Finset.mem_filter.mp hn).2
    rw [hre, hc, one_mul]
  have h2 : ∑ n ∈ (Finset.Ioc 0 ⌊Real.exp L⌋₊).filter (fun n : ℕ ↦ ¬ IsUnit (n : ZMod Q)),
        -(ArithmeticFunction.vonMangoldt n / Real.sqrt n * (2 * ‖k (Real.log n)‖))
      ≤ ∑ n ∈ (Finset.Ioc 0 ⌊Real.exp L⌋₊).filter (fun n : ℕ ↦ ¬ IsUnit (n : ZMod Q)),
        (((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ)
          * (coeff χ n * k (Real.log n) + (starRingEnd ℂ) (coeff χ n) * k (-Real.log n))).re := by
    refine Finset.sum_le_sum fun n _ ↦ ?_
    rw [hre]
    have hw : 0 ≤ ArithmeticFunction.vonMangoldt n / Real.sqrt n :=
      div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _)
    have hc1 : ‖coeff χ n‖ ≤ 1 := DirichletCharacter.norm_le_one χ _
    have hz : -‖k (Real.log n)‖ ≤ (coeff χ n * k (Real.log n)).re := by
      have h3 := Complex.abs_re_le_norm (coeff χ n * k (Real.log n))
      rw [norm_mul] at h3
      have h4 : ‖coeff χ n‖ * ‖k (Real.log n)‖ ≤ ‖k (Real.log n)‖ :=
        mul_le_of_le_one_left (norm_nonneg _) hc1
      linarith [neg_abs_le (coeff χ n * k (Real.log n)).re]
    nlinarith
  rw [Finset.sum_neg_distrib] at h2
  linarith

end T2


section MillerSection


/-- `s` with `n - 1 = 2^s d`, `d` odd. -/
def millerS (n : ℕ) : ℕ := (n - 1).factorization 2
/-- `d` with `n - 1 = 2^s d`, `d` odd. -/
def millerD (n : ℕ) : ℕ := (n - 1) / 2 ^ millerS n

/-- `x` is a (strong) Miller–Rabin liar for `n`. -/
def IsMillerLiar (n : ℕ) (x : ZMod n) : Prop :=
  x ^ millerD n = 1 ∨ ∃ r < millerS n, x ^ (2 ^ r * millerD n) = -1

/-- `a` is a Miller–Rabin witness for `n` (same as `Targets.lean`). -/
def IsMillerWitness (n a : ℕ) : Prop :=
  (a : ZMod n) ^ millerD n ≠ 1 ∧ ∀ r < millerS n, (a : ZMod n) ^ (2 ^ r * millerD n) ≠ -1

theorem isMillerWitness_iff (n a : ℕ) : IsMillerWitness n a ↔ ¬ IsMillerLiar n (a : ZMod n) := by
  unfold IsMillerWitness IsMillerLiar
  push Not
  rfl

theorem two_pow_millerS_mul_millerD (n : ℕ) : 2 ^ millerS n * millerD n = n - 1 :=
  Nat.ordProj_mul_ordCompl_eq_self (n - 1) 2

theorem odd_millerD {n : ℕ} (h1 : 1 < n) : Odd (millerD n) := by
  have hc := Nat.coprime_ordCompl Nat.prime_two (by omega : n - 1 ≠ 0)
  exact Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp fun h ↦ by
    have := Nat.Coprime.eq_one_of_dvd hc h; omega)

theorem millerS_pos {n : ℕ} (hodd : Odd n) (h1 : 1 < n) : 0 < millerS n := by
  unfold millerS
  refine Nat.Prime.factorization_pos_of_dvd Nat.prime_two (by omega) ?_
  obtain ⟨k, rfl⟩ := hodd
  exact ⟨k, by omega⟩

/-- Liars satisfy Fermat: `x^(n-1) = 1`. -/
theorem pow_sub_one_of_liar {n : ℕ} {x : ZMod n} (h : IsMillerLiar n x) : x ^ (n - 1) = 1 := by
  rw [← two_pow_millerS_mul_millerD n]
  rcases h with h | ⟨r, hr, h⟩
  · rw [mul_comm, pow_mul, h, one_pow]
  · obtain ⟨t, ht⟩ : ∃ t, millerS n = r + (t + 1) := ⟨millerS n - r - 1, by omega⟩
    rw [ht, show 2 ^ (r + (t + 1)) * millerD n = (2 ^ r * millerD n) * 2 ^ (t + 1) by ring,
      pow_mul, h, pow_succ, pow_mul', neg_one_sq, one_pow]

/-! ## Case 1: `n = p^k`, `k ≥ 2` -/

/-- In a commutative ring, if `x² = 0` then `(1 + x)^m = 1 + m x`. -/
theorem one_add_pow_of_sq_eq_zero {R : Type*} [CommRing R] {x : R} (hx : x ^ 2 = 0) (m : ℕ) :
    (1 + x) ^ m = 1 + m * x := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ, ih]
    push_cast
    linear_combination (m : R) * hx

/-- For `n = p^k` (`p` odd prime, `k ≥ 2`) some unit violates Fermat. -/
theorem exists_unit_pow_sub_one_ne_one_of_prime_pow {p k : ℕ} (hp : p.Prime) (hk : 2 ≤ k) :
    ∃ g : (ZMod (p ^ k))ˣ, (g : ZMod (p ^ k)) ^ (p ^ k - 1) ≠ 1 := by
  have : NeZero (p ^ k) := ⟨pow_ne_zero _ hp.ne_zero⟩
  set x : ZMod (p ^ k) := ((p ^ (k - 1) : ℕ) : ZMod (p ^ k))
  have hx2 : x ^ 2 = 0 := by
    simp only [x, ← Nat.cast_pow, ← pow_mul]
    rw [ZMod.natCast_eq_zero_iff]
    exact pow_dvd_pow p (by omega)
  have hunit : IsUnit (1 + x) := (IsNilpotent.isUnit_one_add ⟨2, hx2⟩)
  refine ⟨hunit.unit, ?_⟩
  rw [IsUnit.unit_spec, one_add_pow_of_sq_eq_zero hx2]
  intro h
  have h0 : ((p ^ k - 1 : ℕ) : ZMod (p ^ k)) * x = 0 := by linear_combination h
  simp only [x, ← Nat.cast_mul] at h0
  rw [ZMod.natCast_eq_zero_iff] at h0
  have hpk : p ^ k = p * p ^ (k - 1) := by rw [← pow_succ']; congr 1; omega
  have h0' : p * p ^ (k - 1) ∣ (p ^ k - 1) * p ^ (k - 1) := by rw [← hpk]; exact h0
  have hdiv : p ∣ p ^ k - 1 := (Nat.mul_dvd_mul_iff_right (pow_pos hp.pos _)).mp h0'
  have h1 : p ∣ p ^ k := dvd_pow_self p (by omega)
  have hone : 1 ≤ p ^ k := Nat.one_le_pow k p hp.pos
  have h2 : p ∣ p ^ k - (p ^ k - 1) := Nat.dvd_sub h1 hdiv
  rw [Nat.sub_sub_self hone] at h2
  exact hp.one_lt.ne' (Nat.dvd_one.mp h2)


/-! ## Case 2: `n = A B` with `A, B > 2` coprime -/

theorem miller_subgroup_of_coprime {A B : ℕ} (hAB : A.Coprime B) (hA : 2 < A) (hB : 2 < B)
    (hodd : Odd (A * B)) :
    ∃ H : Subgroup (ZMod (A * B))ˣ, H ≠ ⊤ ∧
      ∀ u : (ZMod (A * B))ˣ, IsMillerLiar (A * B) (u : ZMod (A * B)) → u ∈ H := by
  classical
  have h1 : 1 < A * B := by nlinarith
  have hFA : Fact (2 < A) := ⟨hA⟩
  have hFB : Fact (2 < B) := ⟨hB⟩
  set n := A * B with hn
  set s := millerS n
  set d := millerD n
  have hs0 : 0 < s := millerS_pos hodd h1
  have hdodd : Odd d := odd_millerD h1
  set R := (Finset.range s).filter (fun r ↦ ∃ u : (ZMod n)ˣ, (u : ZMod n) ^ (2 ^ r * d) = -1)
  have h0R : 0 ∈ R := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hs0, -1, ?_⟩
    rw [Units.val_neg, Units.val_one, pow_zero, one_mul, hdodd.neg_one_pow]
  set ν := R.max' ⟨0, h0R⟩
  have hνR : ν ∈ R := R.max'_mem _
  obtain ⟨b, hb⟩ := (Finset.mem_filter.mp hνR).2
  set e := 2 ^ ν * d
  -- the subgroup `{u : u^e = ±1}`
  let H : Subgroup (ZMod n)ˣ :=
    { carrier := {u | (u : ZMod n) ^ e = 1 ∨ (u : ZMod n) ^ e = -1}
      mul_mem' := by
        intro u v hu hv
        simp only [Set.mem_setOf_eq, Units.val_mul, mul_pow] at hu hv ⊢
        rcases hu with hu | hu <;> rcases hv with hv | hv <;> rw [hu, hv] <;> simp
      one_mem' := by simp
      inv_mem' := by
        intro u hu
        simp only [Set.mem_setOf_eq] at hu ⊢
        have hprod : ((u⁻¹ : (ZMod n)ˣ) : ZMod n) ^ e * (u : ZMod n) ^ e = 1 := by
          rw [← mul_pow, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_pow]
        rcases hu with hu | hu
        · left; rw [hu, mul_one] at hprod; exact hprod
        · right; rw [hu] at hprod; linear_combination -hprod }
  refine ⟨H, ?_, ?_⟩
  · -- properness via CRT
    intro htop
    let cr := ZMod.chineseRemainder hAB
    have hbu : IsUnit (cr (b : ZMod n)) := b.isUnit.map cr
    have hb1 : IsUnit (cr (b : ZMod n)).1 := (Prod.isUnit_iff.mp hbu).1
    set a0 : ZMod n := cr.symm ((cr (b : ZMod n)).1, 1)
    have hpair : IsUnit (((cr (b : ZMod n)).1, (1 : ZMod B)) : ZMod A × ZMod B) :=
      Prod.isUnit_iff.mpr ⟨hb1, isUnit_one⟩
    have ha0 : IsUnit a0 := hpair.map cr.symm
    have hmem : ha0.unit ∈ H := htop ▸ Subgroup.mem_top _
    have hcr : cr (a0 ^ e) = (-1, 1) := by
      rw [map_pow]
      simp only [a0, RingEquiv.apply_symm_apply, Prod.pow_mk, one_pow]
      have : (cr (b : ZMod n)).1 ^ e = (cr ((b : ZMod n) ^ e)).1 := by rw [map_pow, Prod.pow_fst]
      rw [this, hb, map_neg, map_one]
      rfl
    rcases hmem with h | h
    · rw [IsUnit.unit_spec] at h
      rw [h, map_one] at hcr
      exact ZMod.neg_one_ne_one (congrArg Prod.fst hcr).symm
    · rw [IsUnit.unit_spec] at h
      rw [h, map_neg, map_one] at hcr
      exact ZMod.neg_one_ne_one (n := B) (congrArg Prod.snd hcr)
  · -- liars lie in `H`
    intro u hu
    show (u : ZMod n) ^ e = 1 ∨ (u : ZMod n) ^ e = -1
    rcases hu with hu | ⟨r, hr, hu⟩
    · left; rw [show e = 2 ^ ν * d from rfl, pow_mul', hu, one_pow]
    · have hrR : r ∈ R := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hr, u, hu⟩
      have hrν : r ≤ ν := R.le_max' r hrR
      rcases hrν.lt_or_eq with hlt | heq
      · left
        obtain ⟨t, ht⟩ : ∃ t, ν = r + (t + 1) := ⟨ν - r - 1, by omega⟩
        rw [show e = (2 ^ r * d) * 2 ^ (t + 1) by simp only [e, ht]; ring, pow_mul, hu, pow_succ,
          pow_mul', neg_one_sq, one_pow]
      · right
        have he : e = 2 ^ r * millerD n := by rw [heq]
        rw [he]; exact hu

/-! ## Miller's lemma -/

/-- **Miller's lemma.** For odd composite `n`, all Miller–Rabin liars among the units lie in a
proper subgroup of `(ZMod n)ˣ`. -/
theorem exists_proper_subgroup_of_liars {n : ℕ} (hodd : Odd n) (h1 : 1 < n) (hnp : ¬ n.Prime) :
    ∃ H : Subgroup (ZMod n)ˣ, H ≠ ⊤ ∧
      ∀ u : (ZMod n)ˣ, IsMillerLiar n (u : ZMod n) → u ∈ H := by
  classical
  by_cases hpp : IsPrimePow n
  · obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff n).mp hpp
    have hk2 : 2 ≤ k := by
      by_contra h
      have : k = 1 := by omega
      subst this; exact hnp (by simpa using hp)
    obtain ⟨g, hg⟩ := exists_unit_pow_sub_one_ne_one_of_prime_pow hp hk2
    refine ⟨(powMonoidHom (p ^ k - 1) : (ZMod (p ^ k))ˣ →* (ZMod (p ^ k))ˣ).ker, ?_, ?_⟩
    · intro htop
      apply hg
      have : g ∈ (powMonoidHom (p ^ k - 1) : (ZMod (p ^ k))ˣ →* (ZMod (p ^ k))ˣ).ker :=
        htop ▸ Subgroup.mem_top g
      rw [MonoidHom.mem_ker, powMonoidHom_apply] at this
      rw [← Units.val_pow_eq_pow_val, this, Units.val_one]
    · intro u hu
      rw [MonoidHom.mem_ker, powMonoidHom_apply]
      ext
      rw [Units.val_pow_eq_pow_val, Units.val_one]
      exact pow_sub_one_of_liar hu
  · obtain ⟨A, B, rfl, hcop, hA, hB⟩ : ∃ A B, A * B = n ∧ A.Coprime B ∧ 2 < A ∧ 2 < B := by
      set p := n.minFac
      have hp : p.Prime := Nat.minFac_prime (by omega)
      have hpn : p ∣ n := Nat.minFac_dvd n
      have hfac : 0 < n.factorization p := hp.factorization_pos_of_dvd (by omega) hpn
      have hAB := Nat.ordProj_mul_ordCompl_eq_self n p
      have hA1 : p ≤ p ^ n.factorization p := Nat.le_self_pow hfac.ne' p
      have hB0 : 0 < n / p ^ n.factorization p := Nat.pos_of_ne_zero fun h ↦ by
        rw [h, mul_zero] at hAB; omega
      have hB1 : n / p ^ n.factorization p ≠ 1 := fun h ↦ by
        rw [h, mul_one] at hAB
        exact hpp ⟨p, n.factorization p, hp.prime, hfac, hAB⟩
      have hoAB : Odd (p ^ n.factorization p * (n / p ^ n.factorization p)) := by
        rw [hAB]; exact hodd
      have hoA : Odd (p ^ n.factorization p) := Nat.Odd.of_mul_left hoAB
      have hoB : Odd (n / p ^ n.factorization p) := Nat.Odd.of_mul_right hoAB
      refine ⟨_, _, hAB, (Nat.coprime_ordCompl hp (by omega)).pow_left _, ?_, ?_⟩
      · have := hp.two_le
        rcases hoA with ⟨j, hj⟩; omega
      · rcases hoB with ⟨j, hj⟩; omega
    exact miller_subgroup_of_coprime hcop hA hB hodd


/-! ## Primes have no witnesses -/

/-- For an odd prime `p`, every nonzero `x : ZMod p` is a Miller–Rabin liar. -/
theorem isMillerLiar_of_prime {p : ℕ} [hp : Fact p.Prime] {x : ZMod p}
    (hx : x ≠ 0) : IsMillerLiar p x := by
  classical
  have h1 : 1 < p := hp.out.one_lt
  set s := millerS p
  set d := millerD p
  have hfer : x ^ (2 ^ s * d) = 1 := by
    rw [two_pow_millerS_mul_millerD]; exact ZMod.pow_card_sub_one_eq_one hx
  by_cases h0 : x ^ d = 1
  · exact Or.inl h0
  · right
    have hex : ∃ r, x ^ (2 ^ r * d) = 1 := ⟨s, hfer⟩
    set m := Nat.find hex with hm
    have hmspec : x ^ (2 ^ m * d) = 1 := Nat.find_spec hex
    have hms : m ≤ s := Nat.find_min' hex hfer
    have hm0 : m ≠ 0 := by
      intro h; rw [h, pow_zero, one_mul] at hmspec; exact h0 hmspec
    obtain ⟨r, hr⟩ : ∃ r, m = r + 1 := ⟨m - 1, by omega⟩
    have hrlt : ¬ x ^ (2 ^ r * d) = 1 := Nat.find_min hex (by omega)
    have hsq : x ^ (2 ^ r * d) * x ^ (2 ^ r * d) = 1 := by
      rw [← pow_add, show 2 ^ r * d + 2 ^ r * d = 2 ^ m * d by rw [hr, pow_succ]; ring]
      exact hmspec
    refine ⟨r, by omega, ?_⟩
    rcases mul_self_eq_one_iff.mp hsq with h | h
    · exact absurd h hrlt
    · exact h


end MillerSection

section T3T5


/-- A proper subgroup of `(ZMod q)ˣ` is contained in the kernel of a nontrivial character. -/
theorem exists_dirichletCharacter_ne_one_trivial_on (q : ℕ) [NeZero q]
    (H : Subgroup (ZMod q)ˣ) (hH : H ≠ ⊤) :
    ∃ χ : DirichletCharacter ℂ q, χ ≠ 1 ∧ ∀ u ∈ H, χ (u : ZMod q) = 1 := by
  obtain ⟨g, hg⟩ : ∃ g : (ZMod q)ˣ, g ∉ H := by
    by_contra h
    push Not at h
    exact hH (eq_top_iff.mpr fun g _ ↦ h g)
  have hg' : (QuotientGroup.mk g : (ZMod q)ˣ ⧸ H) ≠ 1 := by
    rwa [ne_eq, QuotientGroup.eq_one_iff]
  have hexp : Monoid.exponent ((ZMod q)ˣ ⧸ H) ≠ 0 :=
    Monoid.exponent_ne_zero_of_finite (G := (ZMod q)ˣ ⧸ H)
  have : NeZero ((Monoid.exponent ((ZMod q)ˣ ⧸ H) : ℕ) : ℂ) := ⟨by exact_mod_cast hexp⟩
  obtain ⟨φ, hφ⟩ := CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity ((ZMod q)ˣ ⧸ H) ℂ hg'
  set χ : DirichletCharacter ℂ q := MulChar.ofUnitHom (φ.comp (QuotientGroup.mk' H)) with hχ
  refine ⟨χ, fun h1 ↦ hφ ?_, fun u hu ↦ ?_⟩
  · have := congrArg (fun ψ : DirichletCharacter ℂ q ↦ ψ (g : ZMod q)) h1
    simp only [hχ, MulChar.ofUnitHom_coe, MulChar.one_apply_coe] at this
    exact Units.ext (by simpa using this)
  · simp only [hχ, MulChar.ofUnitHom_coe, MonoidHom.coe_comp, Function.comp_apply,
      QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff u).mpr hu, map_one, Units.val_one]


end T3T5


section ExplicitIngredients
open MeasureTheory Set Filter Topology
/-- `Re ψ(a + i s) = Re ψ(a + i |s|)` (conjugate symmetry). -/
theorem re_digamma_abs (a s : ℝ) :
    (Complex.digamma ((a : ℂ) + I * s)).re = (Complex.digamma ((a : ℂ) + I * |s|)).re := by
  rcases le_or_gt 0 s with hs | hs
  · rw [abs_of_nonneg hs]
  · rw [abs_of_neg hs]
    have hc : (starRingEnd ℂ) ((a : ℂ) + I * ((-s : ℝ) : ℂ)) = (a : ℂ) + I * s := by
      apply Complex.ext <;> simp
    rw [← hc, Zeta23.digamma_conj, Complex.conj_re]

end ExplicitIngredients


section NarrowSec
open MeasureTheory
namespace Narrow


/-- Narrow cutoff (transition width 1/64). -/
def etaN (a t : ℝ) : ℝ := Real.smoothTransition (64 * (a - t)) * Real.smoothTransition (64 * (a + t))
def testFN (a t : ℝ) : ℝ := Real.cosh (t / 2) * etaN a t
def testFnN (a : ℝ) : ℝ → ℂ := fun t ↦ (testFN a t : ℂ)

theorem etaN_nonneg (a t : ℝ) : 0 ≤ etaN a t :=
  mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _)

theorem etaN_le_one (a t : ℝ) : etaN a t ≤ 1 :=
  mul_le_one₀ (Real.smoothTransition.le_one _) (Real.smoothTransition.nonneg _)
    (Real.smoothTransition.le_one _)

theorem etaN_eq_one {a t : ℝ} (ht : |t| ≤ a - 1 / 64) : etaN a t = 1 := by
  rw [abs_le] at ht
  unfold etaN
  rw [Real.smoothTransition.one_of_one_le (by linarith),
    Real.smoothTransition.one_of_one_le (by linarith), mul_one]

theorem etaN_eq_zero {a t : ℝ} (ht : a ≤ |t|) : etaN a t = 0 := by
  unfold etaN
  rcases le_abs'.mp ht with h | h
  · rw [Real.smoothTransition.zero_of_nonpos (x := 64 * (a + t)) (by linarith), mul_zero]
  · rw [Real.smoothTransition.zero_of_nonpos (x := 64 * (a - t)) (by linarith), zero_mul]

theorem testFN_nonneg (a t : ℝ) : 0 ≤ testFN a t :=
  mul_nonneg (Real.cosh_pos _).le (etaN_nonneg a t)

theorem testFN_le_cosh (a t : ℝ) : testFN a t ≤ Real.cosh (t / 2) :=
  mul_le_of_le_one_right (Real.cosh_pos _).le (etaN_le_one a t)

theorem contDiff_testFN (a : ℝ) : ContDiff ℝ 2 (testFN a) := by
  unfold testFN etaN
  exact (Real.contDiff_cosh.comp (contDiff_id.div_const 2)).mul
    ((Real.smoothTransition.contDiff.comp (contDiff_const.mul (contDiff_const.sub contDiff_id))).mul
      (Real.smoothTransition.contDiff.comp (contDiff_const.mul (contDiff_const.add contDiff_id))))

theorem contDiff_testFnN (a : ℝ) : ContDiff ℝ 2 (testFnN a) :=
  Complex.ofRealCLM.contDiff.comp (contDiff_testFN a)

theorem support_testFN_subset (a : ℝ) : Function.support (testFN a) ⊆ Set.Icc (-a) a := by
  intro t ht
  rw [Set.mem_Icc, ← abs_le]
  by_contra h
  exact ht (by rw [testFN, etaN_eq_zero (le_of_lt (not_le.mp h)), mul_zero])

theorem tsupport_testFnN_subset (a : ℝ) : tsupport (testFnN a) ⊆ Set.Icc (-a) a := by
  refine closure_minimal (fun t ht ↦ support_testFN_subset a ?_) isClosed_Icc
  intro h; exact ht (by simp [testFnN, h])

theorem hasCompactSupport_testFN (a : ℝ) : HasCompactSupport (testFN a) :=
  HasCompactSupport.of_support_subset_isCompact isCompact_Icc (support_testFN_subset a)

theorem hasCompactSupport_testFnN (a : ℝ) : HasCompactSupport (testFnN a) :=
  HasCompactSupport.of_support_subset_isCompact isCompact_Icc
    ((Function.support_subset_iff'.mpr fun t ht ↦ by
      have : t ∉ tsupport (testFnN a) := fun h ↦ ht (tsupport_testFnN_subset a h)
      exact image_eq_zero_of_notMem_tsupport this).trans (fun _ h ↦ h))

theorem weilTest_testFnN (a u : ℝ) :
    weilTest (testFnN a) (testFnN a) u = ((∫ t, testFN a t * testFN a (t - u) : ℝ) : ℂ) := by
  simp only [weilTest, MeasureTheory.convolution_def, ContinuousLinearMap.mul_apply', tilde,
    testFnN, Complex.conj_ofReal]
  rw [← integral_complex_ofReal]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t ↦ ?_)
  simp only [Complex.ofReal_mul]
  congr 3; ring

theorem exp_div_two_le_cosh (x : ℝ) : Real.exp x / 2 ≤ Real.cosh x := by
  rw [Real.cosh_eq]; linarith [Real.exp_pos (-x)]

theorem integrable_testFN_shift (a u : ℝ) : Integrable (fun t ↦ testFN a t * testFN a (t - u)) :=
  (((contDiff_testFN a).continuous).mul ((contDiff_testFN a).continuous.comp
      (continuous_id.sub continuous_const))).integrable_of_hasCompactSupport
    (hasCompactSupport_testFN a).mul_right

/-- Key lower bound with the narrow plateau: for `0 ≤ u ≤ 2a − 1/32`,
`Re k(u) ≥ (2a − 1/32 − u) e^{u/2} / 4`. -/
theorem weilTest_testFnN_re_ge {a u : ℝ} (hu0 : 0 ≤ u) (hua : u ≤ 2 * a - 1 / 32) :
    (2 * a - 1 / 32 - u) * (Real.exp (u / 2) / 4) ≤ (weilTest (testFnN a) (testFnN a) u).re := by
  rw [weilTest_testFnN, Complex.ofReal_re]
  set g : ℝ → ℝ := fun t ↦ testFN a t * testFN a (t - u)
  have hgi : Integrable g := integrable_testFN_shift a u
  have hg0 : ∀ t, 0 ≤ g t := fun t ↦ mul_nonneg (testFN_nonneg a t) (testFN_nonneg a _)
  set I := Set.Icc (u - (a - 1 / 64)) (a - 1 / 64)
  have hbound : ∀ t ∈ I, Real.exp (u / 2) / 4 ≤ g t := by
    intro t ht
    obtain ⟨h1, h2⟩ := ht
    have hA : |t| ≤ a - 1 / 64 := abs_le.mpr ⟨by linarith, h2⟩
    have hB : |t - u| ≤ a - 1 / 64 := abs_le.mpr ⟨by linarith, by linarith⟩
    simp only [g, testFN, etaN_eq_one hA, etaN_eq_one hB, mul_one]
    have e1 := exp_div_two_le_cosh (t / 2)
    have e2 := exp_div_two_le_cosh (-((t - u) / 2))
    rw [Real.cosh_neg] at e2
    have hprod : Real.exp (t / 2) / 2 * (Real.exp (-((t - u) / 2)) / 2) = Real.exp (u / 2) / 4 := by
      rw [div_mul_div_comm, ← Real.exp_add]; congr 1 <;> ring_nf
    rw [← hprod]
    exact mul_le_mul e1 e2 (by positivity) (Real.cosh_pos _).le
  have hvol : volume.real I = 2 * a - 1 / 32 - u := by
    rw [Measure.real, Real.volume_Icc, ENNReal.toReal_ofReal (by linarith)]; ring
  calc (2 * a - 1 / 32 - u) * (Real.exp (u / 2) / 4)
      = volume.real I • (Real.exp (u / 2) / 4) := by rw [smul_eq_mul, hvol]
    _ ≤ ∫ t in I, g t := setIntegral_ge_of_const_le measurableSet_Icc
        (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top) hbound hgi.integrableOn
    _ ≤ ∫ t, g t := setIntegral_le_integral hgi (Filter.Eventually.of_forall hg0)

theorem weilTest_testFnN_re_nonneg (a u : ℝ) : 0 ≤ (weilTest (testFnN a) (testFnN a) u).re := by
  rw [weilTest_testFnN, Complex.ofReal_re]
  exact integral_nonneg fun t ↦ mul_nonneg (testFN_nonneg a t) (testFN_nonneg a _)

/-- `k(0) = ∫ F² ≤ sinh a + a`. -/
theorem weilTest_testFnN_zero_le {a : ℝ} (ha : 0 ≤ a) :
    (weilTest (testFnN a) (testFnN a) 0).re ≤ Real.sinh a + a := by
  rw [weilTest_testFnN, Complex.ofReal_re]
  simp only [sub_zero]
  have hzero : ∀ t ∉ Set.Icc (-a) a, testFN a t * testFN a t = 0 := by
    intro t ht
    have : testFN a t = 0 := by
      by_contra h; exact ht (support_testFN_subset a h)
    rw [this, zero_mul]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hzero]
  have hc : Continuous (fun t : ℝ ↦ (Real.cosh t + 1) / 2) := by fun_prop
  have hgc : Continuous (fun t ↦ testFN a t * testFN a t) :=
    (contDiff_testFN a).continuous.mul (contDiff_testFN a).continuous
  calc ∫ t in Set.Icc (-a) a, testFN a t * testFN a t
      ≤ ∫ t in Set.Icc (-a) a, (Real.cosh t + 1) / 2 :=
        setIntegral_mono_on hgc.integrableOn_Icc hc.integrableOn_Icc measurableSet_Icc fun t _ ↦ by
          have h1 := testFN_le_cosh a t
          have h0 := testFN_nonneg a t
          have hsq : Real.cosh (t / 2) ^ 2 = (Real.cosh t + 1) / 2 := by
            have h2 := Real.cosh_two_mul (t / 2)
            rw [show 2 * (t / 2) = t by ring] at h2
            nlinarith [Real.cosh_sq (t / 2)]
          nlinarith [mul_le_mul h1 h1 h0 (Real.cosh_pos _).le]
    _ = Real.sinh a + a := by
        rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith)]
        rw [intervalIntegral.integral_div, intervalIntegral.integral_add
          (Real.continuous_cosh.intervalIntegrable _ _) intervalIntegrable_const,
          intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ ↦ Real.hasDerivAt_sinh x)
            (Real.continuous_cosh.intervalIntegrable _ _), intervalIntegral.integral_const,
          Real.sinh_neg, smul_eq_mul]
        ring

/-! ### Derivative of the narrow test function -/

theorem deriv_smoothTransition_nonneg' (x : ℝ) : 0 ≤ deriv Real.smoothTransition x :=
  Real.smoothTransition.monotone.deriv_nonneg

theorem deriv_smoothTransition_eq_zero' {x : ℝ} (hx : x ∉ Set.Icc (0 : ℝ) 1) :
    deriv Real.smoothTransition x = 0 := by
  rw [Set.mem_Icc, not_and_or, not_le, not_le] at hx
  rcases hx with h | h
  · have : Real.smoothTransition =ᶠ[nhds x] fun _ ↦ 0 :=
      Filter.eventually_of_mem (Iio_mem_nhds h) fun y hy ↦
        Real.smoothTransition.zero_of_nonpos (le_of_lt hy)
    rw [this.deriv_eq, deriv_const]
  · have : Real.smoothTransition =ᶠ[nhds x] fun _ ↦ 1 :=
      Filter.eventually_of_mem (Ioi_mem_nhds h) fun y hy ↦
        Real.smoothTransition.one_of_one_le (le_of_lt hy)
    rw [this.deriv_eq, deriv_const]

theorem continuous_deriv_smoothTransition' : Continuous (deriv Real.smoothTransition) :=
  (Real.smoothTransition.contDiff (n := 1)).continuous_deriv le_rfl

theorem hasCompactSupport_deriv_smoothTransition' :
    HasCompactSupport (deriv Real.smoothTransition) :=
  HasCompactSupport.of_support_subset_isCompact isCompact_Icc fun x hx ↦ by
    by_contra h; exact hx (deriv_smoothTransition_eq_zero' h)

theorem integral_deriv_smoothTransition' : ∫ x, deriv Real.smoothTransition x = 1 := by
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Set.Icc (0 : ℝ) 1)
    (fun x hx ↦ deriv_smoothTransition_eq_zero' hx), integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le zero_le_one,
    intervalIntegral.integral_deriv_eq_sub
      (fun x _ ↦ (Real.smoothTransition.contDiff (n := 1)).differentiable one_ne_zero x)
      (continuous_deriv_smoothTransition'.intervalIntegrable _ _),
    Real.smoothTransition.one, Real.smoothTransition.zero, sub_zero]

/-- `∫ 64 S'(64 t) dt = 1`. -/
theorem integral_scaled_deriv : ∫ t, 64 * deriv Real.smoothTransition (64 * t) = 1 := by
  rw [integral_const_mul, Measure.integral_comp_mul_left (fun y ↦ deriv Real.smoothTransition y) 64,
    integral_deriv_smoothTransition', smul_eq_mul]
  norm_num

/-- A nonnegative continuous compactly supported weight of total mass 1 supported in `[−a, a]`
against `cosh(t/2)` gives at most `cosh(a/2)`. -/
theorem integral_cosh_mul_weight_le {a : ℝ} (w : ℝ → ℝ) (hw0 : ∀ t, 0 ≤ w t) (hwc : Continuous w)
    (hwcs : HasCompactSupport w) (hsupp : ∀ t, w t ≠ 0 → |t| ≤ a) (hint : ∫ t, w t = 1) :
    ∫ t, Real.cosh (t / 2) * w t ≤ Real.cosh (a / 2) := by
  have hwi : Integrable w := hwc.integrable_of_hasCompactSupport hwcs
  have hi : Integrable (fun t ↦ Real.cosh (t / 2) * w t) :=
    ((by fun_prop : Continuous fun t : ℝ ↦ Real.cosh (t / 2)).mul hwc).integrable_of_hasCompactSupport
      hwcs.mul_left
  calc ∫ t, Real.cosh (t / 2) * w t ≤ ∫ t, Real.cosh (a / 2) * w t := by
        refine integral_mono hi (hwi.const_mul _) fun t ↦ ?_
        by_cases h0 : w t = 0
        · simp [h0]
        · refine mul_le_mul_of_nonneg_right ?_ (hw0 t)
          rw [Real.cosh_le_cosh, abs_div, abs_div, abs_two]
          exact div_le_div_of_nonneg_right ((hsupp t h0).trans (le_abs_self a)) (by norm_num)
    _ = Real.cosh (a / 2) := by rw [integral_const_mul, hint, mul_one]

theorem hasDerivAt_testFN (a t : ℝ) :
    HasDerivAt (testFN a)
      (Real.sinh (t / 2) * (1 / 2) * etaN a t + Real.cosh (t / 2) *
        (deriv Real.smoothTransition (64 * (a - t)) * (64 * -1) * Real.smoothTransition (64 * (a + t))
          + Real.smoothTransition (64 * (a - t)) * (deriv Real.smoothTransition (64 * (a + t)) * (64 * 1)))) t := by
  have hS : ∀ x, HasDerivAt Real.smoothTransition (deriv Real.smoothTransition x) x := fun x ↦
    ((Real.smoothTransition.contDiff (n := 1)).differentiable one_ne_zero x).hasDerivAt
  have h1 := ((hasDerivAt_id' t).div_const 2).cosh
  have h2 := (hS (64 * (a - t))).comp t (((hasDerivAt_id' t).const_sub a).const_mul 64)
  have h3 := (hS (64 * (a + t))).comp t (((hasDerivAt_id' t).const_add a).const_mul 64)
  have h := h1.mul (h2.mul h3)
  unfold testFN etaN
  exact h

/-- **`‖f_a'‖₁ ≤ 2 sinh(a/2) + 2 cosh(a/2)` for the narrow cutoff** (no derivative bound on `S`). -/
theorem integral_abs_deriv_testFN_le {a : ℝ} (ha : 1 ≤ a) :
    ∫ t, |deriv (testFN a) t| ≤ 2 * Real.sinh (a / 2) + 2 * Real.cosh (a / 2) := by
  have ha0 : 0 ≤ a := by linarith
  set S' := deriv Real.smoothTransition
  have hS'c := continuous_deriv_smoothTransition'
  have hS'cs := hasCompactSupport_deriv_smoothTransition'
  have hFi : Integrable (testFN a) :=
    (contDiff_testFN a).continuous.integrable_of_hasCompactSupport (hasCompactSupport_testFN a)
  -- ∫ F ≤ 4 sinh(a/2)
  have hF1 : ∫ t, testFN a t ≤ 4 * Real.sinh (a / 2) := by
    have hzero : ∀ t ∉ Set.Icc (-a) a, testFN a t = 0 := fun t ht ↦ by
      by_contra h; exact ht (support_testFN_subset a h)
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hzero]
    have hcc : Continuous (fun t : ℝ ↦ Real.cosh (t / 2)) := by fun_prop
    calc ∫ t in Set.Icc (-a) a, testFN a t ≤ ∫ t in Set.Icc (-a) a, Real.cosh (t / 2) :=
          setIntegral_mono_on (contDiff_testFN a).continuous.integrableOn_Icc hcc.integrableOn_Icc
            measurableSet_Icc fun t _ ↦ testFN_le_cosh a t
      _ = 4 * Real.sinh (a / 2) := by
          rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith),
            intervalIntegral.integral_comp_div (fun x ↦ Real.cosh x) (by norm_num : (2 : ℝ) ≠ 0),
            intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ ↦ Real.hasDerivAt_sinh x)
              (Real.continuous_cosh.intervalIntegrable _ _), smul_eq_mul, neg_div, Real.sinh_neg]
          ring
  -- the two edge weights
  set w1 : ℝ → ℝ := fun t ↦ 64 * S' (64 * (a - t))
  set w2 : ℝ → ℝ := fun t ↦ 64 * S' (64 * (a + t))
  have hw1c : Continuous w1 := continuous_const.mul (hS'c.comp (by fun_prop))
  have hw2c : Continuous w2 := continuous_const.mul (hS'c.comp (by fun_prop))
  have hsupp1 : ∀ t, w1 t ≠ 0 → |t| ≤ a := fun t ht ↦ by
    have h' : S' (64 * (a - t)) ≠ 0 := fun h ↦ ht (by simp [w1, h])
    have := (not_imp_comm.mp deriv_smoothTransition_eq_zero') h'
    rw [Set.mem_Icc] at this; rw [abs_le]; constructor <;> linarith
  have hsupp2 : ∀ t, w2 t ≠ 0 → |t| ≤ a := fun t ht ↦ by
    have h' : S' (64 * (a + t)) ≠ 0 := fun h ↦ ht (by simp [w2, h])
    have := (not_imp_comm.mp deriv_smoothTransition_eq_zero') h'
    rw [Set.mem_Icc] at this; rw [abs_le]; constructor <;> linarith
  have hcs_of : ∀ w : ℝ → ℝ, (∀ t, w t ≠ 0 → |t| ≤ a) → HasCompactSupport w := fun w hw ↦
    HasCompactSupport.of_support_subset_isCompact (isCompact_Icc (a := -a) (b := a))
      fun t ht ↦ abs_le.mp (hw t ht)
  have hw1cs := hcs_of w1 hsupp1
  have hw2cs := hcs_of w2 hsupp2
  have hint1 : ∫ t, w1 t = 1 := by
    have := integral_sub_left_eq_self (fun t ↦ 64 * S' (64 * t)) (μ := volume) a
    simp only [w1]; rw [this]; exact integral_scaled_deriv
  have hint2 : ∫ t, w2 t = 1 := by
    have := integral_add_left_eq_self (fun t ↦ 64 * S' (64 * t)) (μ := volume) a
    simp only [w2]; rw [this]; exact integral_scaled_deriv
  have I1 := integral_cosh_mul_weight_le w1 (fun t ↦ mul_nonneg (by norm_num)
    (deriv_smoothTransition_nonneg' _)) hw1c hw1cs hsupp1 hint1
  have I2 := integral_cosh_mul_weight_le w2 (fun t ↦ mul_nonneg (by norm_num)
    (deriv_smoothTransition_nonneg' _)) hw2c hw2cs hsupp2 hint2
  have hcosh : Continuous (fun t : ℝ ↦ Real.cosh (t / 2)) := by fun_prop
  have hJ1 : Integrable (fun t ↦ Real.cosh (t / 2) * w1 t) :=
    (hcosh.mul hw1c).integrable_of_hasCompactSupport hw1cs.mul_left
  have hJ2 : Integrable (fun t ↦ Real.cosh (t / 2) * w2 t) :=
    (hcosh.mul hw2c).integrable_of_hasCompactSupport hw2cs.mul_left
  have hmaj : Integrable (fun t ↦ testFN a t / 2 + (Real.cosh (t / 2) * w1 t +
      Real.cosh (t / 2) * w2 t)) := (hFi.div_const 2).add (hJ1.add hJ2)
  have hpt : ∀ t, |deriv (testFN a) t| ≤ testFN a t / 2 + (Real.cosh (t / 2) * w1 t +
      Real.cosh (t / 2) * w2 t) := by
    intro t
    rw [(hasDerivAt_testFN a t).deriv]
    have hc : 0 < Real.cosh (t / 2) := Real.cosh_pos _
    have hsh : |Real.sinh (t / 2)| ≤ Real.cosh (t / 2) := by
      rw [abs_le]; constructor <;> nlinarith [Real.cosh_sq (t / 2), Real.sinh_lt_cosh (t / 2),
        Real.sinh_lt_cosh (-(t / 2)), Real.sinh_neg (t / 2), Real.cosh_neg (t / 2)]
    have he0 := etaN_nonneg a t
    have hA := deriv_smoothTransition_nonneg' (64 * (a - t))
    have hB := deriv_smoothTransition_nonneg' (64 * (a + t))
    have hS1 := Real.smoothTransition.le_one (64 * (a + t))
    have hS0 := Real.smoothTransition.nonneg (64 * (a + t))
    have hT1 := Real.smoothTransition.le_one (64 * (a - t))
    have hT0 := Real.smoothTransition.nonneg (64 * (a - t))
    have hη : |deriv Real.smoothTransition (64 * (a - t)) * (64 * -1) * Real.smoothTransition (64 * (a + t))
        + Real.smoothTransition (64 * (a - t)) * (deriv Real.smoothTransition (64 * (a + t)) * (64 * 1))|
        ≤ w1 t + w2 t := by
      simp only [w1, w2, S']
      rw [abs_le]; constructor <;>
        nlinarith [mul_nonneg hA hS0, mul_nonneg hB hT0, mul_le_mul_of_nonneg_left hS1 hA,
          mul_le_mul_of_nonneg_left hT1 hB]
    have hF : testFN a t = Real.cosh (t / 2) * etaN a t := rfl
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul, abs_mul, abs_of_pos hc, abs_of_nonneg he0,
      abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2), hF]
    nlinarith [mul_le_mul_of_nonneg_right hsh he0, mul_le_mul_of_nonneg_left hη hc.le]
  calc ∫ t, |deriv (testFN a) t|
      ≤ ∫ t, (testFN a t / 2 + (Real.cosh (t / 2) * w1 t + Real.cosh (t / 2) * w2 t)) :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall fun t ↦ abs_nonneg _) hmaj
          (Filter.Eventually.of_forall hpt)
    _ = (∫ t, testFN a t) / 2 + ((∫ t, Real.cosh (t / 2) * w1 t) +
          ∫ t, Real.cosh (t / 2) * w2 t) := by
        have e1 : ∫ t, (testFN a t / 2 + (Real.cosh (t / 2) * w1 t + Real.cosh (t / 2) * w2 t))
            = (∫ t, testFN a t / 2) + ∫ t, (Real.cosh (t / 2) * w1 t + Real.cosh (t / 2) * w2 t) :=
          integral_add (hFi.div_const 2) (hJ1.add hJ2)
        have e2 : ∫ t, (Real.cosh (t / 2) * w1 t + Real.cosh (t / 2) * w2 t) =
            (∫ t, Real.cosh (t / 2) * w1 t) + ∫ t, Real.cosh (t / 2) * w2 t := integral_add hJ1 hJ2
        rw [e1, e2, integral_div]
    _ ≤ 4 * Real.sinh (a / 2) / 2 + (Real.cosh (a / 2) + Real.cosh (a / 2)) := by gcongr
    _ = 2 * Real.sinh (a / 2) + 2 * Real.cosh (a / 2) := by ring


theorem integral_testFN_le {a : ℝ} (ha0 : 0 ≤ a) : ∫ t, testFN a t ≤ 4 * Real.sinh (a / 2) := by
  have hzero : ∀ t ∉ Set.Icc (-a) a, testFN a t = 0 := fun t ht ↦ by
    by_contra h; exact ht (support_testFN_subset a h)
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hzero]
  have hcc : Continuous (fun t : ℝ ↦ Real.cosh (t / 2)) := by fun_prop
  calc ∫ t in Set.Icc (-a) a, testFN a t ≤ ∫ t in Set.Icc (-a) a, Real.cosh (t / 2) :=
        setIntegral_mono_on (contDiff_testFN a).continuous.integrableOn_Icc hcc.integrableOn_Icc
          measurableSet_Icc fun t _ ↦ testFN_le_cosh a t
    _ = 4 * Real.sinh (a / 2) := by
        rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith),
          intervalIntegral.integral_comp_div (fun x ↦ Real.cosh x) (by norm_num : (2 : ℝ) ≠ 0),
          intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ ↦ Real.hasDerivAt_sinh x)
            (Real.continuous_cosh.intervalIntegrable _ _), smul_eq_mul, neg_div, Real.sinh_neg]
        ring


end Narrow
end NarrowSec

section TightN
open MeasureTheory

/-- **Fourier inversion at 0** for `k = f ⋆ f̃`: `Re k(0) = (1/2π) ∫ |f̂(r)|² dr`. -/
theorem re_weilTest_zero' {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f) (hfs : HasCompactSupport f)
    (hint : Integrable (fun r : ℝ ↦ ‖paperFT f (r : ℂ)‖ ^ 2)) :
    (weilTest f f 0).re = (1 / (2 * π)) * ∫ r : ℝ, ‖paperFT f (r : ℂ)‖ ^ 2 := by
  set k := weilTest f f
  have hkc : ContDiff ℝ 2 k := weilTest_contDiff hf hf.continuous hfs
  have hks : HasCompactSupport k := weilTest_hasCompactSupport hfs hfs
  have hki : Integrable k := hkc.continuous.integrable_of_hasCompactSupport hks
  have hpt : ∀ r : ℝ, paperFT k (r : ℂ) = ((‖paperFT f (r : ℂ)‖ ^ 2 : ℝ) : ℂ) := fun r ↦ by
    rw [paperFT_weilTest hf.continuous hf.continuous hfs hfs, Complex.conj_ofReal,
      Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hPi : Integrable (fun r : ℝ ↦ paperFT k (r : ℂ)) := by
    simp_rw [hpt]; exact hint.ofReal
  have hFk : Integrable (FourierTransform.fourier k) := by
    have h := hPi.comp_mul_left' (show (-(2 * π) : ℝ) ≠ 0 by have := Real.pi_pos; linarith)
    refine h.congr (Filter.Eventually.of_forall fun w ↦ ?_)
    show paperFT k ((-(2 * π) * w : ℝ) : ℂ) = _
    rw [EF.paperFT_ofReal_eq_fourier]
    congr 1
    field_simp
  have hinv := paper_inversion hkc.continuous hki hFk 0
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, mul_one] at hinv
  rw [hinv]
  simp_rw [hpt]
  rw [integral_complex_ofReal]
  have : (1 / (2 * π) : ℂ) = ((1 / (2 * π) : ℝ) : ℂ) := by push_cast; ring
  rw [this, ← Complex.ofReal_mul, Complex.ofReal_re]

section NonUnitOmega
open ArithmeticFunction Finset

/-- `Σ_{n ≤ N, (n,q) ≠ 1} Λ(n) ≤ ω(q) · log N`. -/
theorem sum_vonMangoldt_nonunit_le_omega (q N : ℕ) [NeZero q] :
    ∑ n ∈ (Ioc 0 N).filter (fun n : ℕ ↦ ¬ IsUnit (n : ZMod q)), Λ n
      ≤ (q.primeFactors.card : ℝ) * Real.log N := by
  classical
  set S := (Ioc 0 N).filter (fun n : ℕ ↦ ¬ IsUnit (n : ZMod q))
  set P := q.primeFactors.sigma (fun p ↦ Icc 1 (Nat.log p N))
  set T := P.image (fun pk : (_ : ℕ) × ℕ ↦ pk.1 ^ pk.2)
  have hmem : ∀ n ∈ S, Λ n ≠ 0 → n ∈ T := by
    intro n hn hΛ
    obtain ⟨hnI, hnu⟩ := mem_filter.mp hn
    obtain ⟨hn0, hnN⟩ := mem_Ioc.mp hnI
    obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff n).mp (vonMangoldt_ne_zero_iff.mp hΛ)
    have hncop : ¬ (p ^ k).Coprime q := fun h ↦ hnu ((ZMod.isUnit_iff_coprime _ _).mpr h)
    rw [Nat.coprime_pow_left_iff hk] at hncop
    have hpq : p ∣ q := by
      by_contra h; exact hncop ((Nat.Prime.coprime_iff_not_dvd hp).mpr h)
    have hkN : k ≤ Nat.log p N := Nat.le_log_of_pow_le hp.one_lt hnN
    exact mem_image.mpr ⟨⟨p, k⟩, mem_sigma.mpr ⟨Nat.mem_primeFactors.mpr ⟨hp, hpq, NeZero.ne q⟩,
      mem_Icc.mpr ⟨hk, hkN⟩⟩, rfl⟩
  have hg0 : ∀ n, 0 ≤ Λ n := fun n ↦ vonMangoldt_nonneg
  have hp_bound : ∀ p ∈ q.primeFactors, ∑ j ∈ Icc 1 (Nat.log p N), Λ (p ^ j) ≤ Real.log N := by
    intro p hp
    have hpp := Nat.prime_of_mem_primeFactors hp
    rw [sum_congr rfl (fun j hj ↦ by
      rw [vonMangoldt_apply_pow (by have := (mem_Icc.mp hj).1; omega), vonMangoldt_apply_prime hpp]),
      sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
    rcases Nat.eq_zero_or_pos N with hN | hN
    · subst hN; simp
    have h1 : p ^ Nat.log p N ≤ N := Nat.pow_log_le_self p hN.ne'
    have h2 : ((p : ℝ) ^ Nat.log p N) ≤ N := by exact_mod_cast h1
    calc (Nat.log p N : ℝ) * Real.log p = Real.log ((p : ℝ) ^ Nat.log p N) := by rw [Real.log_pow]
      _ ≤ Real.log N := Real.log_le_log (by have := hpp.pos; positivity) h2
  calc ∑ n ∈ S, Λ n = ∑ n ∈ S.filter (· ∈ T), Λ n :=
        (sum_filter_of_ne fun n hn h ↦ hmem n hn h).symm
    _ ≤ ∑ n ∈ T, Λ n :=
        sum_le_sum_of_subset_of_nonneg (fun n hn ↦ (mem_filter.mp hn).2) fun n _ _ ↦ hg0 n
    _ ≤ ∑ pk ∈ P, Λ (pk.1 ^ pk.2) := sum_image_le_of_nonneg fun n _ ↦ hg0 n
    _ = ∑ p ∈ q.primeFactors, ∑ j ∈ Icc 1 (Nat.log p N), Λ (p ^ j) := sum_sigma _ _ _
    _ ≤ ∑ _p ∈ q.primeFactors, Real.log N := sum_le_sum hp_bound
    _ = (q.primeFactors.card : ℝ) * Real.log N := by rw [sum_const, nsmul_eq_mul]

/-- `Σ_{n ≤ N, (n,q)=1} Λ(n) ≥ N log 2 − log(N+1) − ω(q) log N`. -/
theorem sum_vonMangoldt_unit_ge_omega (q N : ℕ) [NeZero q] :
    N * Real.log 2 - Real.log (N + 1) - (q.primeFactors.card : ℝ) * Real.log N
      ≤ ∑ n ∈ (Ioc 0 N).filter (fun n : ℕ ↦ IsUnit (n : ZMod q)), Λ n := by
  classical
  have h1 := Chebyshev.psi_ge N
  have h2 := sum_vonMangoldt_nonunit_le_omega q N
  have h3 : Chebyshev.psi N = ∑ n ∈ (Ioc 0 N).filter (fun n : ℕ ↦ IsUnit (n : ZMod q)), Λ n
      + ∑ n ∈ (Ioc 0 N).filter (fun n : ℕ ↦ ¬ IsUnit (n : ZMod q)), Λ n := by
    rw [Chebyshev.psi, Nat.floor_natCast, sum_filter_add_sum_filter_not]
  linarith

end NonUnitOmega

end TightN


section T2N
open MeasureTheory

/-- `exp(1/32) ≤ 32/31`. -/
theorem exp_one_div_32_le : Real.exp (1 / 32) ≤ 32 / 31 := by
  have h := Real.add_one_le_exp (-(1 / 32 : ℝ))
  have hp := Real.exp_pos (1 / 32 : ℝ)
  have hm : Real.exp (-(1 / 32 : ℝ)) * Real.exp (1 / 32) = 1 := by rw [← Real.exp_add]; simp
  nlinarith

theorem exp_33_32_le : Real.exp (33 / 32) ≤ 2.81 := by
  have h1 := Real.exp_one_lt_d9
  have h2 := exp_one_div_32_le
  have e : Real.exp (33 / 32) = Real.exp 1 * Real.exp (1 / 32) := by rw [← Real.exp_add]; norm_num
  rw [e]
  nlinarith [Real.exp_pos 1, Real.exp_pos (1 / 32)]

theorem exp_65_32_le : Real.exp (65 / 32) ≤ 7.65 := by
  have h1 := Real.exp_one_lt_d9
  have h2 := exp_one_div_32_le
  have e : Real.exp (65 / 32) = Real.exp 1 * Real.exp 1 * Real.exp (1 / 32) := by
    rw [← Real.exp_add, ← Real.exp_add]; norm_num
  rw [e]
  have h0 := Real.exp_pos 1
  have h3 : Real.exp 1 * Real.exp 1 ≤ 7.3891 := by nlinarith
  nlinarith [Real.exp_pos (1 / 32), mul_pos h0 h0]


end T2N


section AnalyticConstants
/-! ## Sharper analytic constants: `J ≤ 6` and the digamma constant `1/2` -/
open MeasureTheory Set Filter Topology


/-- `∫_{1}^{∞} log r / r^(m+1) = 1/m²` for `m ≥ 1`, via the antiderivative `-(m log r + 1)/(m² r^m)`. -/
theorem integral_log_div_pow (m : ℕ) (hm : 0 < m) :
    ∫ r in Ioi (1 : ℝ), Real.log r / r ^ (m + 1) = 1 / (m : ℝ) ^ 2 := by
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  set F : ℝ → ℝ := fun r ↦ -((m : ℝ) * Real.log r + 1) / ((m : ℝ) ^ 2 * r ^ m) with hF
  have hderiv : ∀ x ∈ Ici (1 : ℝ), HasDerivAt F (Real.log x / x ^ (m + 1)) x := by
    intro x hx
    have hx1 : (1 : ℝ) ≤ x := hx
    have hx0 : x ≠ 0 := by positivity
    have hN := (((Real.hasDerivAt_log hx0).const_mul (m : ℝ)).add_const 1).neg
    have hD := (hasDerivAt_pow m x).const_mul ((m : ℝ) ^ 2)
    have h := hN.div hD (by positivity)
    refine h.congr_deriv ?_
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    simp only [Pi.neg_apply]
    push_cast
    field_simp
    ring
  have hcont : ContinuousWithinAt F (Ici 1) 1 :=
    (hderiv 1 (Set.mem_Ici.mpr le_rfl)).continuousAt.continuousWithinAt
  have hlim : Tendsto F atTop (𝓝 0) := by
    -- |F r| ≤ (m log r + 1)/(m² r) for r ≥ 1, and that tends to 0
    have h1 : Tendsto (fun r : ℝ ↦ Real.log r / r) atTop (𝓝 0) := by
      simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
    have h2 : Tendsto (fun r : ℝ ↦ 1 / r) atTop (𝓝 0) := tendsto_const_nhds.div_atTop tendsto_id
    have hg : Tendsto (fun r : ℝ ↦ (1 / (m : ℝ)) * (Real.log r / r) + (1 / (m : ℝ) ^ 2) * (1 / r))
        atTop (𝓝 0) := by
      have := (h1.const_mul (1 / (m : ℝ))).add (h2.const_mul (1 / (m : ℝ) ^ 2))
      simpa [one_div] using this
    refine squeeze_zero_norm' ?_ hg
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with r hr
    have hr0 : 0 < r := by linarith
    have hl : 0 ≤ Real.log r := Real.log_nonneg hr
    have hrm : r ≤ r ^ m := by
      calc r = r ^ 1 := (pow_one r).symm
        _ ≤ r ^ m := pow_le_pow_right₀ hr hm
    have hnum : 0 ≤ (m : ℝ) * Real.log r + 1 := by positivity
    rw [Real.norm_eq_abs, hF, abs_div, abs_neg, abs_of_nonneg hnum, abs_of_pos (by positivity)]
    calc ((m : ℝ) * Real.log r + 1) / ((m : ℝ) ^ 2 * r ^ m)
        ≤ ((m : ℝ) * Real.log r + 1) / ((m : ℝ) ^ 2 * r) := by
          gcongr
      _ = (1 / (m : ℝ)) * (Real.log r / r) + (1 / (m : ℝ) ^ 2) * (1 / r) := by
          field_simp
  have hint : IntegrableOn (fun r : ℝ ↦ Real.log r / r ^ (m + 1)) (Ioi 1) := by
    refine integrableOn_Ioi_deriv_of_nonneg hcont (fun x hx ↦ hderiv x (Ioi_subset_Ici_self hx)) ?_ hlim
    intro x hx; exact div_nonneg (Real.log_nonneg (le_of_lt hx)) (by have : (1:ℝ) < x := hx; positivity)
  rw [integral_Ioi_of_hasDerivAt_of_tendsto hcont (fun x hx ↦ hderiv x (Ioi_subset_Ici_self hx)) hint hlim]
  simp [hF, one_div]
  ring

/-- `∫_0^1 r/(1+r²) = log 2 / 2`. -/
theorem integral_r_div_one_add_sq_01 : ∫ r in (0:ℝ)..1, r / (1 + r ^ 2) = Real.log 2 / 2 := by
  have hd : ∀ x ∈ Set.uIcc (0:ℝ) 1,
      HasDerivAt (fun r : ℝ ↦ Real.log (1 + r ^ 2) / 2) (x / (1 + x ^ 2)) x := by
    intro x _
    have h1 : (1 + x ^ 2) ≠ 0 := by positivity
    have h := (((hasDerivAt_pow 2 x).const_add 1).log h1).div_const 2
    refine h.congr_deriv ?_
    field_simp; ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    ((continuous_id.div (continuous_const.add (continuous_pow 2)) fun x ↦ by
      show (1:ℝ) + x ^ 2 ≠ 0; positivity).intervalIntegrable _ _)]
  norm_num

/-- `∫_0^1 1/(1+r²) = π/4`. -/
theorem integral_inv_one_add_sq_01 : ∫ r in (0:ℝ)..1, 1 / (1 + r ^ 2) = Real.pi / 4 := by
  rw [integral_one_div_one_add_sq, Real.arctan_one, Real.arctan_zero, sub_zero]

/-- `∫_1^∞ 1/(1+r²) = π/4`. -/
theorem integral_Ioi_inv_one_add_sq_1 : ∫ r in Ioi (1:ℝ), 1 / (1 + r ^ 2) = Real.pi / 4 := by
  have hd : ∀ x ∈ Ici (1:ℝ), HasDerivAt Real.arctan (1 / (1 + x ^ 2)) x := fun x _ ↦ by
    simpa [one_div] using Real.hasDerivAt_arctan x
  have hlim : Tendsto Real.arctan atTop (𝓝 (Real.pi / 2)) :=
    Real.tendsto_arctan_atTop.mono_right nhdsWithin_le_nhds
  have hint : IntegrableOn (fun r : ℝ ↦ 1 / (1 + r ^ 2)) (Ioi 1) := by
    simpa [one_div] using integrable_inv_one_add_sq.integrableOn
  rw [integral_Ioi_of_hasDerivAt_of_tendsto Real.continuous_arctan.continuousWithinAt
    (fun x hx ↦ hd x (Ioi_subset_Ici_self hx)) hint hlim, Real.arctan_one]
  ring

/-- `∫_1^∞ 1/(r(1+r²)) = log 2 / 2`, antiderivative `log r − log(1+r²)/2`. -/
theorem integral_Ioi_inv_r_one_add_sq_1 :
    ∫ r in Ioi (1:ℝ), 1 / (r * (1 + r ^ 2)) = Real.log 2 / 2 := by
  set G : ℝ → ℝ := fun r ↦ Real.log r - Real.log (1 + r ^ 2) / 2 with hG
  have hd : ∀ x ∈ Ici (1:ℝ), HasDerivAt G (1 / (x * (1 + x ^ 2))) x := by
    intro x hx
    have hx0 : x ≠ 0 := by have : (1:ℝ) ≤ x := hx; positivity
    have h1 : (1 + x ^ 2) ≠ 0 := by positivity
    have h := (Real.hasDerivAt_log hx0).sub ((((hasDerivAt_pow 2 x).const_add 1).log h1).div_const 2)
    refine h.congr_deriv ?_
    field_simp; ring
  -- G r = -(1/2) log(1 + r⁻²) → 0
  have hlim : Tendsto G atTop (𝓝 0) := by
    have hinv : Tendsto (fun r : ℝ ↦ 1 + (r ^ 2)⁻¹) atTop (𝓝 1) := by
      have hp : Tendsto (fun r : ℝ ↦ r ^ 2) atTop atTop := tendsto_pow_atTop two_ne_zero
      have h0 := (tendsto_inv_atTop_zero.comp hp).const_add (1:ℝ)
      simpa [Function.comp] using h0
    have := ((Real.continuousAt_log one_ne_zero).tendsto.comp hinv).div_const 2 |>.neg
    simp only [Real.log_one, zero_div, neg_zero] at this
    refine this.congr' (eventually_gt_atTop 0 |>.mono fun r hr ↦ ?_)
    simp only [Function.comp, hG]
    have : 1 + (r ^ 2)⁻¹ = (1 + r ^ 2) / r ^ 2 := by field_simp; ring
    rw [this, Real.log_div (by positivity) (by positivity), Real.log_pow]
    push_cast; ring
  have hint : IntegrableOn (fun r : ℝ ↦ 1 / (r * (1 + r ^ 2))) (Ioi 1) := by
    refine integrableOn_Ioi_deriv_of_nonneg (hd 1 (Set.mem_Ici.mpr le_rfl)).continuousAt.continuousWithinAt
      (fun x hx ↦ hd x (Ioi_subset_Ici_self hx)) ?_ hlim
    intro x hx; have : (1:ℝ) < x := hx; positivity
  rw [integral_Ioi_of_hasDerivAt_of_tendsto (hd 1 (Set.mem_Ici.mpr le_rfl)).continuousAt.continuousWithinAt
    (fun x hx ↦ hd x (Ioi_subset_Ici_self hx)) hint hlim]
  simp [hG]
  norm_num


/-- Tangent-line bound on `[0,1]`: `log(4+r) ≤ log(9/2) + (r - 1/2)·(2/9)`. -/
theorem log_four_add_le_tangent (r : ℝ) (hr : 0 ≤ r) :
    Real.log (4 + r) ≤ Real.log (9 / 2) + (r - 1 / 2) * (2 / 9) := by
  have h := Real.log_le_sub_one_of_pos (show 0 < (4 + r) / (9 / 2) by positivity)
  rw [Real.log_div (by positivity) (by norm_num)] at h
  linarith

/-- For `r ≥ 1`: `log(4+r) ≤ log r + log 3 + (4/r - 2)/3` (tangent of `log(1+4u)` at `u = 1/2`). -/
theorem log_four_add_le_tail (r : ℝ) (hr : 1 ≤ r) :
    Real.log (4 + r) ≤ Real.log r + Real.log 3 + (4 / r - 2) / 3 := by
  have hr0 : 0 < r := by linarith
  have hsplit : Real.log (4 + r) = Real.log r + Real.log (1 + 4 / r) := by
    rw [← Real.log_mul hr0.ne' (by positivity)]; congr 1; field_simp; ring
  have h := Real.log_le_sub_one_of_pos (show 0 < (1 + 4 / r) / 3 by positivity)
  rw [Real.log_div (by positivity) (by norm_num)] at h
  rw [hsplit]
  have : (1 + 4 / r) / 3 - 1 = (4 / r - 2) / 3 := by ring
  linarith

/-- For `r ≥ 1`: `1/(1+r²) ≤ 1/r² - 1/r⁴ + 1/r⁶`. -/
theorem inv_one_add_sq_le_series (r : ℝ) (hr : 1 ≤ r) :
    1 / (1 + r ^ 2) ≤ 1 / r ^ 2 - 1 / r ^ 4 + 1 / r ^ 6 := by
  have hr0 : 0 < r := by linarith
  rw [div_le_iff₀ (by positivity)]
  have e : (1 / r ^ 2 - 1 / r ^ 4 + 1 / r ^ 6) * (1 + r ^ 2) = 1 + 1 / r ^ 6 := by
    field_simp; ring
  rw [e]; have : 0 ≤ 1 / r ^ 6 := by positivity
  linarith


set_option maxHeartbeats 1000000 in
theorem J_le_6 : ∫ r : ℝ, Real.log (4 + |r|) * (1 + r ^ 2)⁻¹ ≤ 6 := by
  set g : ℝ → ℝ := fun t ↦ Real.log (4 + t) * (1 + t ^ 2)⁻¹ with hg
  have hcomp : (fun r : ℝ ↦ Real.log (4 + |r|) * (1 + r ^ 2)⁻¹) = fun r ↦ g |r| := by
    funext r; simp [hg, sq_abs]
  rw [hcomp, integral_comp_abs (f := g)]
  have hgc : ContinuousOn g (Ici 0) := by
    intro t ht
    have ht0 : (0:ℝ) ≤ t := ht
    refine ContinuousAt.continuousWithinAt ?_
    exact ((continuous_const.add continuous_id).continuousAt.log (by simp; linarith)).mul
      ((continuous_const.add (continuous_pow 2)).continuousAt.inv₀ (by
        show (1:ℝ) + t ^ 2 ≠ 0; positivity))
  -- majorants
  set m1 : ℝ → ℝ := fun r ↦ (Real.log (9 / 2) - 1 / 9) * (1 / (1 + r ^ 2)) + (2 / 9) * (r / (1 + r ^ 2))
  set m2 : ℝ → ℝ := fun r ↦ (Real.log r / r ^ 2 - Real.log r / r ^ 4 + Real.log r / r ^ 6)
      + (Real.log 3 - 2 / 3) * (1 / (1 + r ^ 2)) + (4 / 3) * (1 / (r * (1 + r ^ 2)))
  have hp1 : ∀ r ∈ Ioc (0:ℝ) 1, g r ≤ m1 r := by
    intro r hr
    have h := log_four_add_le_tangent r hr.1.le
    have hi : 0 < (1 + r ^ 2)⁻¹ := by positivity
    simp only [hg, m1]
    have : (Real.log (9 / 2) - 1 / 9) * (1 / (1 + r ^ 2)) + 2 / 9 * (r / (1 + r ^ 2))
        = (Real.log (9 / 2) + (r - 1 / 2) * (2 / 9)) * (1 + r ^ 2)⁻¹ := by field_simp; ring
    rw [this]; exact mul_le_mul_of_nonneg_right h hi.le
  have hp2 : ∀ r ∈ Ioi (1:ℝ), g r ≤ m2 r := by
    intro r hr
    have hr1 : (1:ℝ) ≤ r := le_of_lt hr
    have hr0 : 0 < r := by linarith
    have h := log_four_add_le_tail r hr1
    have hs := inv_one_add_sq_le_series r hr1
    have hl : 0 ≤ Real.log r := Real.log_nonneg hr1
    have hi : 0 < (1 + r ^ 2)⁻¹ := by positivity
    simp only [hg, m2]
    have step1 : Real.log (4 + r) * (1 + r ^ 2)⁻¹
        ≤ (Real.log r + Real.log 3 + (4 / r - 2) / 3) * (1 + r ^ 2)⁻¹ :=
      mul_le_mul_of_nonneg_right h hi.le
    have step2 : Real.log r * (1 + r ^ 2)⁻¹ ≤ Real.log r * (1 / r ^ 2 - 1 / r ^ 4 + 1 / r ^ 6) := by
      rw [← one_div]; exact mul_le_mul_of_nonneg_left hs hl
    have e : (Real.log r + Real.log 3 + (4 / r - 2) / 3) * (1 + r ^ 2)⁻¹
        = Real.log r * (1 + r ^ 2)⁻¹ + ((Real.log 3 - 2 / 3) * (1 / (1 + r ^ 2))
          + (4 / 3) * (1 / (r * (1 + r ^ 2)))) := by field_simp; ring
    have e2 : Real.log r * (1 / r ^ 2 - 1 / r ^ 4 + 1 / r ^ 6)
        = Real.log r / r ^ 2 - Real.log r / r ^ 4 + Real.log r / r ^ 6 := by ring
    linarith
  -- integrals of the pieces (nonzero values give integrability)
  have iL : ∀ m : ℕ, 0 < m → IntegrableOn (fun r : ℝ ↦ Real.log r / r ^ (m + 1)) (Ioi 1) := by
    intro m hm
    refine Integrable.of_integral_ne_zero ?_
    rw [integral_log_div_pow m hm]; have : (0:ℝ) < m := by exact_mod_cast hm
    positivity
  have iA : IntegrableOn (fun r : ℝ ↦ 1 / (1 + r ^ 2)) (Ioi 1) := by
    refine Integrable.of_integral_ne_zero ?_
    rw [integral_Ioi_inv_one_add_sq_1]; positivity
  have iB : IntegrableOn (fun r : ℝ ↦ 1 / (r * (1 + r ^ 2))) (Ioi 1) := by
    refine Integrable.of_integral_ne_zero ?_
    rw [integral_Ioi_inv_r_one_add_sq_1]; positivity
  have iL2 := iL 1 one_pos; have iL4 := iL 3 (by norm_num); have iL6 := iL 5 (by norm_num)
  norm_num at iL2 iL4 iL6
  have im2 : IntegrableOn m2 (Ioi 1) :=
    (((iL2.sub iL4).add iL6).add (iA.const_mul _)).add (iB.const_mul _)
  have hm2 : ∫ r in Ioi (1:ℝ), m2 r
      = (1 - 1 / 9 + 1 / 25) + (Real.log 3 - 2 / 3) * (Real.pi / 4) + (4 / 3) * (Real.log 2 / 2) := by
    simp only [m2]
    have a1 := integral_log_div_pow 1 one_pos
    have a3 := integral_log_div_pow 3 (by norm_num)
    have a5 := integral_log_div_pow 5 (by norm_num)
    norm_num at a1 a3 a5
    rw [integral_add, integral_add, integral_add, integral_sub, integral_const_mul, integral_const_mul,
      integral_Ioi_inv_one_add_sq_1, integral_Ioi_inv_r_one_add_sq_1, a1, a3, a5]
    all_goals first
      | exact iL2 | exact iL4 | exact iL6 | exact iA.const_mul _ | exact iB.const_mul _
      | exact iL2.sub iL4 | exact (iL2.sub iL4).add iL6
      | exact ((iL2.sub iL4).add iL6).add (iA.const_mul _)
      | norm_num
  -- [0,1] piece
  have hm1 : ∫ r in Ioc (0:ℝ) 1, m1 r
      = (Real.log (9 / 2) - 1 / 9) * (Real.pi / 4) + (2 / 9) * (Real.log 2 / 2) := by
    rw [← intervalIntegral.integral_of_le zero_le_one]
    simp only [m1]
    rw [intervalIntegral.integral_add, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul, integral_inv_one_add_sq_01, integral_r_div_one_add_sq_01]
    · exact ((continuous_const.div (continuous_const.add (continuous_pow 2)) fun x ↦ by
        show (1:ℝ) + x ^ 2 ≠ 0; positivity).const_mul _ |>.intervalIntegrable _ _)
    · exact ((continuous_id.div (continuous_const.add (continuous_pow 2)) fun x ↦ by
        show (1:ℝ) + x ^ 2 ≠ 0; positivity).const_mul _ |>.intervalIntegrable _ _)
  have im1 : IntegrableOn m1 (Ioc 0 1) := by
    refine Integrable.of_integral_ne_zero ?_
    rw [hm1]
    have : Real.log (9 / 2) - 1 / 9 > 0 := by
      have := Real.log_le_log (by norm_num) (show (2:ℝ) ≤ 9/2 by norm_num)
      linarith [Real.log_two_gt_d9]
    positivity
  have ig1 : IntegrableOn g (Ioc 0 1) :=
    ((hgc.mono Icc_subset_Ici_self).integrableOn_Icc).mono_set Ioc_subset_Icc_self
  have ig2 : IntegrableOn g (Ioi 1) := by
    refine im2.mono' ((hgc.mono (Ioi_subset_Ici zero_le_one)).aestronglyMeasurable
      measurableSet_Ioi) ?_
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun r hr ↦ ?_)
    have hr0 : (0:ℝ) < r := lt_trans zero_lt_one hr
    have : 0 ≤ g r := mul_nonneg (Real.log_nonneg (by linarith)) (by positivity)
    rw [Real.norm_eq_abs, abs_of_nonneg this]; exact hp2 r hr
  have hsplit : ∫ r in Ioi (0:ℝ), g r = (∫ r in Ioc (0:ℝ) 1, g r) + ∫ r in Ioi (1:ℝ), g r := by
    rw [← Ioc_union_Ioi_eq_Ioi zero_le_one, setIntegral_union (Ioc_disjoint_Ioi le_rfl)
      measurableSet_Ioi ig1 ig2]
  have b1 : ∫ r in Ioc (0:ℝ) 1, g r ≤ ∫ r in Ioc (0:ℝ) 1, m1 r :=
    setIntegral_mono_on ig1 im1 measurableSet_Ioc hp1
  have b2 : ∫ r in Ioi (1:ℝ), g r ≤ ∫ r in Ioi (1:ℝ), m2 r :=
    setIntegral_mono_on ig2 im2 measurableSet_Ioi hp2
  rw [hsplit]
  rw [hm1] at b1; rw [hm2] at b2
  -- numerics: log 2 < 0.6932, log 3 < 1.1, π < 3.15
  have l2 := Real.log_two_lt_d9
  have l2l := Real.log_two_gt_d9
  have l3 : Real.log 3 < 1.1 := by
    rw [Real.log_lt_iff_lt_exp (by norm_num)]
    have hq := Real.quadratic_le_exp_of_nonneg (show (0:ℝ) ≤ 0.1 by norm_num)
    have he := Real.exp_one_gt_d9
    have hsplit : Real.exp 1.1 = Real.exp 1 * Real.exp 0.1 := by rw [← Real.exp_add]; norm_num
    have hm : (2.7182818283 : ℝ) * 1.105 ≤ Real.exp 1 * Real.exp 0.1 :=
      mul_le_mul he.le (by norm_num at hq ⊢; linarith) (by norm_num) (Real.exp_pos 1).le
    rw [hsplit]; norm_num at hm ⊢; linarith
  have l92 : Real.log (9 / 2) = 2 * Real.log 3 - Real.log 2 := by
    rw [show (9 / 2 : ℝ) = 3 ^ 2 / 2 by norm_num, Real.log_div (by norm_num) (by norm_num), Real.log_pow]
    push_cast; ring
  have hpi := Real.pi_lt_d2
  have hpi0 : 0 ≤ Real.pi := Real.pi_pos.le
  rw [l92] at b1
  have P1 : (2 * Real.log 3 - Real.log 2 - 1 / 9) * (Real.pi / 4) ≤ 1.3958 * (3.15 / 4) := by
    rcases le_total 0 (2 * Real.log 3 - Real.log 2 - 1 / 9) with h | h
    · exact mul_le_mul (by linarith) (by linarith) (by positivity) (by norm_num)
    · nlinarith [mul_nonpos_of_nonpos_of_nonneg h (by positivity : (0:ℝ) ≤ Real.pi / 4)]
  have P2 : (Real.log 3 - 2 / 3) * (Real.pi / 4) ≤ 0.4334 * (3.15 / 4) := by
    rcases le_total 0 (Real.log 3 - 2 / 3) with h | h
    · exact mul_le_mul (by linarith) (by linarith) (by positivity) (by norm_num)
    · nlinarith [mul_nonpos_of_nonpos_of_nonneg h (by positivity : (0:ℝ) ≤ Real.pi / 4)]
  have hb1 : ∫ r in Ioc (0:ℝ) 1, g r ≤ 1.3958 * (3.15 / 4) + (2 / 9) * (0.6932 / 2) := by
    have : (2 * Real.log 3 - Real.log 2 - 1 / 9) = Real.log (9/2) - 1/9 := by rw [l92]
    linarith
  have hb2 : ∫ r in Ioi (1:ℝ), g r ≤ (1 - 1 / 9 + 1 / 25) + 0.4334 * (3.15 / 4) + (4 / 3) * (0.6932 / 2) := by
    linarith
  norm_num at hb1 hb2 ⊢
  linarith


theorem Jconst_le_6 : Jconst ≤ 6 := by unfold Jconst; exact J_le_6

theorem re_digamma_gammaFactor_le_half (κ : ℕ) (hκ : κ ≤ 1) (r : ℝ) :
    (Complex.digamma (1 / 4 + (κ : ℂ) / 2 + I * r / 2)).re ≤ Real.log (4 + |r|) + 1 / 2 := by
  set a : ℝ := 1 / 4 + (κ : ℝ) / 2 with ha
  have hκ' : (κ : ℝ) ≤ 1 := by exact_mod_cast hκ
  have ha0 : 0 < a := by positivity
  have ha1 : a < 1 := by linarith
  have hz : (1 / 4 + (κ : ℂ) / 2 + I * r / 2) = (a : ℂ) + I * ((r / 2 : ℝ) : ℂ) := by
    simp only [ha]; push_cast; ring
  set t' : ℝ := max (|r| / 2) 3 with ht'
  have ht'0 : 0 ≤ |r| / 2 := by positivity
  have ht'h : 3 ≤ t' := le_max_right _ _
  -- reduce to `t' ≥ 1/2`
  have hmono : (Complex.digamma ((a : ℂ) + I * ((r / 2 : ℝ) : ℂ))).re
      ≤ (Complex.digamma ((a : ℂ) + I * (t' : ℂ))).re := by
    rw [re_digamma_abs a (r / 2), abs_div, abs_two]
    exact Zeta23.MuFields.re_digamma_mono ha0 ha1 (Set.mem_Ici.mpr ht'0)
      (Set.mem_Ici.mpr (by linarith)) (le_max_left _ _)
  set w : ℂ := (a : ℂ) + I * (t' : ℂ) with hw
  have hwre : w.re = a := by simp [hw]
  have hwim : w.im = t' := by simp [hw]
  have hwim_abs : 1 / 2 ≤ |w.im| := by rw [hwim, abs_of_pos (by linarith)]; linarith
  have hst := Zeta23.StirlingVert.digamma_stirling (w := w) (by rw [hwre]; exact ha0) hwim_abs
  have hnw : 3 ≤ ‖w‖ := by
    have := Complex.abs_im_le_norm w; rw [hwim, abs_of_pos (by linarith)] at this; linarith
  have hnw0 : 0 < ‖w‖ := by linarith
  have hE : 3 / w.im ^ 2 ≤ 1 / 3 := by
    rw [hwim, div_le_iff₀ (by nlinarith)]; nlinarith
  have hinv : ‖(1 / 2 : ℂ) / w‖ ≤ 1 / 6 := by
    rw [norm_div, div_le_iff₀ hnw0]; simp; linarith
  have hlog : (Complex.log w).re = Real.log ‖w‖ := Complex.log_re w
  have hwnorm : ‖w‖ ≤ 4 + |r| := by
    refine (Complex.norm_le_abs_re_add_abs_im w).trans ?_
    rw [hwre, hwim, abs_of_pos ha0, abs_of_pos (by linarith)]
    have : t' ≤ |r| / 2 + 3 := max_le (by linarith) (by linarith [abs_nonneg r])
    linarith [abs_nonneg r]
  have hpsi : (Complex.digamma w).re ≤ Real.log ‖w‖ + 1 / 2 := by
    set E := Complex.digamma w - Complex.log w + (1 / 2 : ℂ) / w
    have hdec : Complex.digamma w = Complex.log w - (1 / 2 : ℂ) / w + E := by simp only [E]; ring
    have h1 := Complex.re_le_norm E
    have h2 := neg_le_of_abs_le (Complex.abs_re_le_norm ((1 / 2 : ℂ) / w))
    rw [hdec, Complex.add_re, Complex.sub_re, hlog]
    linarith [hst, hE, hinv]
  have hlogw : Real.log ‖w‖ ≤ Real.log (4 + |r|) := Real.log_le_log hnw0 hwnorm
  have hlog1 : 1 ≤ Real.log (4 + |r|) := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) (by linarith [Real.exp_one_lt_d9, abs_nonneg r])
  rw [hz]
  linarith


/-- **Lemma 3b.** Upper bound for the Gamma term (integrability supplied by the caller; it
follows from the decay of `f̂` for `f ∈ C_c²`). -/
theorem gammaTerm_re_le_half
    (hC : ∀ κ : ℕ, κ ≤ 1 → ∀ r : ℝ,
      (Complex.digamma (1 / 4 + (κ : ℂ) / 2 + I * r / 2)).re ≤ Real.log (4 + |r|) + 1 / 2)
    {f : ℝ → ℂ} (hf : Continuous f) (hfs : HasCompactSupport f) {κ q : ℕ} (hκ : κ ≤ 1)
    (hq : 1 ≤ q)
    (hI : MeasureTheory.Integrable (fun r : ℝ ↦ ‖paperFT f (r : ℂ)‖ ^ 2 * gammaDensity κ q r))
    (hJ : MeasureTheory.Integrable
      (fun r : ℝ ↦ ‖paperFT f (r : ℂ)‖ ^ 2 * (1 * Real.log (4 + |r|) + (1 / 2 + Real.log q)))) :
    ((1 / (2 * π) : ℂ) * ∫ r : ℝ, paperFT (weilTest f f) r
        * ((((Complex.digamma (1 / 4 + (κ : ℂ) / 2 + I * r / 2)).re + Real.log (q / π) : ℝ)) : ℂ)).re
      ≤ (1 / (2 * π)) * ∫ r : ℝ, ‖paperFT f (r : ℂ)‖ ^ 2 * (1 * Real.log (4 + |r|) + (1 / 2 + Real.log q)) := by
  rw [gammaTerm_weilTest_self hf hfs, Complex.ofReal_re]
  refine mul_le_mul_of_nonneg_left (MeasureTheory.integral_mono hI hJ fun r ↦ ?_) (by positivity)
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hlog : Real.log (q / π) ≤ Real.log q := by
    rw [Real.log_div hq0.ne' Real.pi_pos.ne']
    linarith [Real.log_nonneg (by linarith [Real.pi_gt_three] : (1 : ℝ) ≤ π)]
  unfold gammaDensity
  linarith [hC κ hκ r]

/-- **Combined bound (Lemmas 1 + 3).** Under GRH, for primitive `χ` mod `q > 1` and `f ∈ C_c²`,
`Re Σ_n Λ(n) n^{-1/2} (χ(n) k(log n) + conj χ(n) k(−log n))
   ≤ (1/2π) ∫ |f̂(r)|² (C log(4 + |r|) + log q) dr`,  with `k = f ⋆ f̃`. -/
theorem primeSide_re_le_add_half {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hGRH : DirichletLZerosOnLine) (hq : 1 < q) (hprim : χ.IsPrimitive)
    (hC : ∀ κ : ℕ, κ ≤ 1 → ∀ r : ℝ,
      (Complex.digamma (1 / 4 + (κ : ℂ) / 2 + I * r / 2)).re ≤ Real.log (4 + |r|) + 1 / 2)
    {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f) (hfs : HasCompactSupport f)
    (hI : MeasureTheory.Integrable
      (fun r : ℝ ↦ ‖paperFT f (r : ℂ)‖ ^ 2 * gammaDensity (parity χ) q r))
    (hJ : MeasureTheory.Integrable
      (fun r : ℝ ↦ ‖paperFT f (r : ℂ)‖ ^ 2 * (1 * Real.log (4 + |r|) + (1 / 2 + Real.log q)))) :
    (∑' n : ℕ, ((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ)
        * (coeff χ n * weilTest f f (Real.log n)
          + (starRingEnd ℂ) (coeff χ n) * weilTest f f (-Real.log n))).re
      ≤ (1 / (2 * π)) * ∫ r : ℝ, ‖paperFT f (r : ℂ)‖ ^ 2 * (1 * Real.log (4 + |r|) + (1 / 2 + Real.log q)) := by
  have hκ : parity χ ≤ 1 := by unfold parity; split_ifs <;> norm_num
  have hM := master_inequality hGRH hq hprim hf hfs
  have hG := gammaTerm_re_le_half hC hf.continuous hfs hκ hq.le hI hJ
  unfold literatureRHSchi at hM
  rw [Complex.add_re, Complex.neg_re] at hM
  linarith

/-- Prime side bounded via Fourier inversion. -/
theorem primeSide_re_le_inv_half {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hGRH : DirichletLZerosOnLine) (hq : 1 < q) (hprim : χ.IsPrimitive)
    {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f) (hfs : HasCompactSupport f) :
    (∑' n : ℕ, ((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ)
        * (coeff χ n * weilTest f f (Real.log n)
          + (starRingEnd ℂ) (coeff χ n) * weilTest f f (-Real.log n))).re
      ≤ (1 / (2 * π)) * (∫ r : ℝ, ‖paperFT f (r : ℂ)‖ ^ 2 * (1 * Real.log (4 + |r|) + 0))
        + (1 / 2 + Real.log q) * (weilTest f f 0).re := by
  have hκ : parity χ ≤ 1 := by unfold parity; split_ifs <;> norm_num
  have h1 := primeSide_re_le_add_half hGRH hq hprim re_digamma_gammaFactor_le_half hf hfs
    (integrable_normSq_paperFT_mul_gammaDensity hf hfs hκ q)
    (integrable_normSq_paperFT_mul_log hf hfs 1 (1 / 2 + Real.log q))
  have hA := integrable_normSq_paperFT_mul_log hf hfs 1 0
  have hB : Integrable (fun r : ℝ ↦ ‖paperFT f (r : ℂ)‖ ^ 2) := by
    have := integrable_normSq_paperFT_mul_log hf hfs 0 1
    refine this.congr (Filter.Eventually.of_forall fun r ↦ ?_)
    simp
  have hsplit : ∫ r : ℝ, ‖paperFT f (r : ℂ)‖ ^ 2 * (1 * Real.log (4 + |r|) + (1 / 2 + Real.log q))
      = (∫ r : ℝ, ‖paperFT f (r : ℂ)‖ ^ 2 * (1 * Real.log (4 + |r|) + 0))
        + (1 / 2 + Real.log q) * ∫ r : ℝ, ‖paperFT f (r : ℂ)‖ ^ 2 := by
    rw [← integral_const_mul, ← integral_add hA (hB.const_mul _)]
    congr 1; funext r; ring
  have hinv := re_weilTest_zero' hf hfs hB
  rw [hsplit] at h1
  have e : (1 / (2 * π)) * ((∫ r : ℝ, ‖paperFT f (r : ℂ)‖ ^ 2 * (1 * Real.log (4 + |r|) + 0))
        + (1 / 2 + Real.log q) * ∫ r : ℝ, ‖paperFT f (r : ℂ)‖ ^ 2)
      = (1 / (2 * π)) * (∫ r : ℝ, ‖paperFT f (r : ℂ)‖ ^ 2 * (1 * Real.log (4 + |r|) + 0))
        + (1 / 2 + Real.log q) * ((1 / (2 * π)) * ∫ r : ℝ, ‖paperFT f (r : ℂ)‖ ^ 2) := by ring
  rw [e, ← hinv] at h1
  exact h1

end AnalyticConstants

end GRHMiller


