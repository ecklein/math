import GRHPseudo.AnalyticNumberTheory.LogDerivGRH
import GRHPseudo.AnalyticNumberTheory.Contour
import GRHPseudo.Vendor.Schoenfeld.Weighted

/-!
# A uniform bound for weighted prime character sums (uses GRH)

**Theorem** (`norm_sum_vonMangoldt_char_le`). Assume `GRHHyp`. For every modulus `q ≥ 1`,
every nonprincipal Dirichlet character `χ` mod `q`, and every integer `N ≥ 3`,

    ‖Σ_{0<n<N} χ(n) Λ(n) (1 − n/N)‖ ≤ (48 e / π) · log² N · √N · (π log(2 + 8q) + J),

where `J = ∫_ℝ log(4 + |t|) / (1 + t²) dt` (`Jconst`, a finite absolute constant).

Proof: weighted Perron at `Re s = 2` with kernel `N^s (1/s − 1/(s+1))` (vendored from
schoenfeld-rh-lean). Identify the Dirichlet series with `−L'/L` (Mathlib). Shift to
`Re s = 1/2 + 1/log N`, where `−L'/L` is holomorphic by GRH (`integral_vertical_eq`). Then bound
the integrand with the Borel–Carathéodory estimate `norm_logDeriv_LFunction_le`.
Proof obligations A4–A5 of `notes/proof_obligations.md`.
-/

noncomputable section

open Complex Filter Topology MeasureTheory Set DirichletCharacter ArithmeticFunction
open scoped Interval LSeries.notation

namespace GRHPseudo

/-! ### Constants and elementary bounds -/

/-- `J = ∫ log(4 + |t|) / (1 + t²) dt`. -/
def Jconst : ℝ := ∫ r : ℝ, Real.log (4 + |r|) * (1 + r ^ 2)⁻¹

/-- Vendored from amrehan/grh-miller `GRHMiller/Ankeny.lean` (Apache-2.0). -/
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
  rw [Real.norm_eq_abs, abs_of_nonneg (by
    have : 0 ≤ Real.log (4 + |r|) := Real.log_nonneg (by linarith [abs_nonneg r])
    positivity), Real.norm_eq_abs, sq_abs]
  have h1 : Real.log (4 + |r|) ≤ Real.log (5 * (1 + r ^ 2)) :=
    Real.log_le_log (by positivity) (by nlinarith [abs_nonneg r, sq_abs r, abs_mul_abs_self r])
  have h2 : Real.log (5 * (1 + r ^ 2)) ≤ (5 * (1 + r ^ 2)) ^ (1 / 4 : ℝ) / (1 / 4) :=
    Real.log_le_rpow_div (by positivity) (by norm_num)
  have h3 : (5 * (1 + r ^ 2)) ^ (1 / 4 : ℝ) / (1 / 4) * (1 + r ^ 2)⁻¹
      = 4 * (5 : ℝ) ^ (1 / 4 : ℝ) * (1 + r ^ 2) ^ (-(3 / 2 : ℝ) / 2) := by
    rw [Real.mul_rpow (by norm_num) hx.le, ← Real.rpow_neg_one, div_eq_mul_inv]
    have : (1 + r ^ 2) ^ (-(3 / 2 : ℝ) / 2) =
        (1 + r ^ 2) ^ (1 / 4 : ℝ) * (1 + r ^ 2) ^ (-1 : ℝ) := by
      rw [← Real.rpow_add hx]; norm_num
    rw [this]; ring
  calc Real.log (4 + |r|) * (1 + r ^ 2)⁻¹
      ≤ (5 * (1 + r ^ 2)) ^ (1 / 4 : ℝ) / (1 / 4) * (1 + r ^ 2)⁻¹ :=
        mul_le_mul_of_nonneg_right (h1.trans h2) (by positivity)
    _ = _ := h3

/-- The Perron kernel for the weight `1 − n/N`. -/
def perronKernel (N : ℕ) (s : ℂ) : ℂ := (N : ℂ) ^ s * (1 / s - 1 / (s + 1))

lemma ne_zero_of_half_le_re {s : ℂ} (hs : 1 / 2 ≤ s.re) : s ≠ 0 := by
  intro h; rw [h] at hs; norm_num at hs

lemma add_one_ne_zero_of_half_le_re {s : ℂ} (hs : 1 / 2 ≤ s.re) : s + 1 ≠ 0 := by
  intro h
  have : (s + 1).re = 0 := by rw [h]; rfl
  simp at this; linarith

lemma norm_inv_sub_inv_le {s : ℂ} (hs : 1 / 2 ≤ s.re) :
    ‖1 / s - 1 / (s + 1)‖ ≤ 2 * (1 + s.im ^ 2)⁻¹ := by
  have h0 := ne_zero_of_half_le_re hs
  have h1 := add_one_ne_zero_of_half_le_re hs
  have heq : 1 / s - 1 / (s + 1) = 1 / (s * (s + 1)) := by field_simp; ring
  rw [heq, norm_div, norm_one, norm_mul]
  have hsq1 : (1 + s.im ^ 2) / 4 ≤ ‖s‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; nlinarith
  have hsq2 : 1 + s.im ^ 2 ≤ ‖s + 1‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; simp only [add_re, one_re, add_im, one_im]
    nlinarith
  have hP : (1 + s.im ^ 2) / 2 ≤ ‖s‖ * ‖s + 1‖ := by
    have hsq : ((1 + s.im ^ 2) / 2) ^ 2 ≤ (‖s‖ * ‖s + 1‖) ^ 2 := by
      rw [mul_pow]
      have := mul_le_mul hsq1 hsq2 (by positivity) (by positivity)
      nlinarith
    exact le_of_pow_le_pow_left₀ two_ne_zero (by positivity) hsq
  have hpos : 0 < (1 + s.im ^ 2) / 2 := by positivity
  calc 1 / (‖s‖ * ‖s + 1‖) ≤ 1 / ((1 + s.im ^ 2) / 2) := one_div_le_one_div_of_le hpos hP
    _ = 2 * (1 + s.im ^ 2)⁻¹ := by field_simp

lemma norm_perronKernel_le {N : ℕ} (hN : 0 < N) {s : ℂ} (hs : 1 / 2 ≤ s.re) :
    ‖perronKernel N s‖ ≤ (N : ℝ) ^ s.re * (2 * (1 + s.im ^ 2)⁻¹) := by
  rw [perronKernel, norm_mul, norm_natCast_cpow_of_pos hN]
  exact mul_le_mul_of_nonneg_left (norm_inv_sub_inv_le hs) (by positivity)

lemma log_two_mul_le (q t : ℝ) (hq : 0 ≤ q) :
    Real.log (2 * (1 + 4 * q * (|t| + 4))) ≤ Real.log (2 + 8 * q) + Real.log (4 + |t|) := by
  rw [← Real.log_mul (by positivity) (by positivity)]
  apply Real.log_le_log (by positivity)
  nlinarith [abs_nonneg t]

/-! ### The integrand -/

variable {q : ℕ} [NeZero q]

/-- `−L'/L(s, χ) · N^s (1/s − 1/(s+1))`. -/
def integrand (χ : DirichletCharacter ℂ q) (N : ℕ) (s : ℂ) : ℂ :=
  -(deriv χ.LFunction s / χ.LFunction s) * perronKernel N s

lemma norm_integrand_le (hGRH : GRHHyp) {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) {N : ℕ} (hN : 0 < N) {s : ℂ}
    (h1 : 1 / 2 + ε ≤ s.re) (h2 : s.re ≤ 2) :
    ‖integrand χ N s‖ ≤ 96 / ε ^ 2 * (N : ℝ) ^ s.re *
      ((Real.log (2 + 8 * q) + Real.log (4 + |s.im|)) * (1 + s.im ^ 2)⁻¹) := by
  have hL := norm_logDeriv_LFunction_le hGRH hχ hε hε1 h1 h2
  have hK := norm_perronKernel_le hN (s := s) (by linarith)
  have hlog := log_two_mul_le (q : ℝ) s.im (Nat.cast_nonneg q)
  rw [integrand, norm_mul, norm_neg]
  have hlog0 : 0 ≤ Real.log (2 * (1 + 4 * (q : ℝ) * (|s.im| + 4))) :=
    Real.log_nonneg (by nlinarith [abs_nonneg s.im, (Nat.cast_nonneg q : (0 : ℝ) ≤ q)])
  calc ‖deriv χ.LFunction s / χ.LFunction s‖ * ‖perronKernel N s‖
      ≤ (48 / ε ^ 2 * Real.log (2 * (1 + 4 * q * (|s.im| + 4)))) *
          ((N : ℝ) ^ s.re * (2 * (1 + s.im ^ 2)⁻¹)) :=
        mul_le_mul hL hK (norm_nonneg _) (by positivity)
    _ ≤ (48 / ε ^ 2 * (Real.log (2 + 8 * q) + Real.log (4 + |s.im|))) *
          ((N : ℝ) ^ s.re * (2 * (1 + s.im ^ 2)⁻¹)) := by gcongr
    _ = _ := by ring

lemma differentiableOn_integrand (hGRH : GRHHyp) {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1)
    {N : ℕ} (hN : 0 < N) {σ₀ : ℝ} (hσ₀ : 1 / 2 < σ₀) (hσ₀2 : σ₀ ≤ 2) :
    DifferentiableOn ℂ (integrand χ N) ([[σ₀, 2]] ×ℂ univ) := by
  intro z hz
  have hzre : σ₀ ≤ z.re := by
    have := (mem_reProdIm.mp hz).1
    rw [uIcc_of_le hσ₀2] at this
    exact this.1
  have hre : 1 / 2 < z.re := lt_of_lt_of_le hσ₀ hzre
  apply DifferentiableAt.differentiableWithinAt
  have hLd : Differentiable ℂ χ.LFunction := differentiable_LFunction hχ
  have hdL : DifferentiableAt ℂ (deriv χ.LFunction) z :=
    ((hLd.differentiableOn.deriv isOpen_univ) z (mem_univ z)).differentiableAt
      (isOpen_univ.mem_nhds (mem_univ z))
  have hne : χ.LFunction z ≠ 0 := LFunction_ne_zero hGRH hχ hre
  have h0 : z ≠ 0 := ne_zero_of_half_le_re hre.le
  have h1 : z + 1 ≠ 0 := add_one_ne_zero_of_half_le_re hre.le
  have hNne : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  unfold integrand perronKernel
  refine ((hdL.div (hLd z) hne).neg).mul ?_
  refine (differentiableAt_id.const_cpow (Or.inl hNne)).mul ?_
  exact ((differentiableAt_const _).div differentiableAt_id h0).sub
    ((differentiableAt_const _).div (differentiableAt_id.add_const 1) h1)

/-- Dominating function on a vertical line. -/
def domLine (ε : ℝ) (N q : ℕ) (σ : ℝ) (t : ℝ) : ℝ :=
  96 / ε ^ 2 * (N : ℝ) ^ σ * ((Real.log (2 + 8 * q) + Real.log (4 + |t|)) * (1 + t ^ 2)⁻¹)

lemma integrable_domLine (ε : ℝ) (N q : ℕ) (σ : ℝ) : Integrable (domLine ε N q σ) := by
  unfold domLine
  refine Integrable.const_mul ?_ _
  have : (fun t : ℝ ↦ (Real.log (2 + 8 * q) + Real.log (4 + |t|)) * (1 + t ^ 2)⁻¹) =
      fun t ↦ Real.log (2 + 8 * q) * (1 + t ^ 2)⁻¹ + Real.log (4 + |t|) * (1 + t ^ 2)⁻¹ := by
    funext t; ring
  rw [this]
  exact (integrable_inv_one_add_sq.const_mul _).add integrable_log_mul_inv_one_add_sq

lemma integral_domLine (ε : ℝ) (N q : ℕ) (σ : ℝ) :
    ∫ t, domLine ε N q σ t = 96 / ε ^ 2 * (N : ℝ) ^ σ * (Real.pi * Real.log (2 + 8 * q) + Jconst) := by
  unfold domLine Jconst
  rw [integral_const_mul]
  congr 1
  have : (fun t : ℝ ↦ (Real.log (2 + 8 * q) + Real.log (4 + |t|)) * (1 + t ^ 2)⁻¹) =
      fun t ↦ Real.log (2 + 8 * q) * (1 + t ^ 2)⁻¹ + Real.log (4 + |t|) * (1 + t ^ 2)⁻¹ := by
    funext t; ring
  rw [this, integral_add (integrable_inv_one_add_sq.const_mul _) integrable_log_mul_inv_one_add_sq,
    integral_const_mul, integral_univ_inv_one_add_sq]
  ring

lemma continuous_integrand_line (hGRH : GRHHyp) {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1)
    {N : ℕ} (hN : 0 < N) {σ₀ σ : ℝ} (hσ₀ : 1 / 2 < σ₀) (hσ₀2 : σ₀ ≤ 2) (hσ : σ ∈ [[σ₀, 2]]) :
    Continuous fun t : ℝ ↦ integrand χ N (σ + t * I) := by
  have hd := differentiableOn_integrand hGRH hχ hN hσ₀ hσ₀2
  refine hd.continuousOn.comp_continuous (by fun_prop) fun t ↦ ?_
  rw [mem_reProdIm]
  simpa using hσ

lemma integrable_integrand_line (hGRH : GRHHyp) {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) {N : ℕ} (hN : 0 < N) {σ : ℝ}
    (h1 : 1 / 2 + ε ≤ σ) (h2 : σ ≤ 2) :
    Integrable fun t : ℝ ↦ integrand χ N (σ + t * I) := by
  have hσ₀ : 1 / 2 < 1 / 2 + ε := by linarith
  have hc := continuous_integrand_line hGRH hχ hN hσ₀ (by linarith) (σ := σ)
    (by rw [uIcc_of_le (by linarith)]; exact ⟨h1, h2⟩)
  refine (integrable_domLine ε N q σ).mono' hc.aestronglyMeasurable
    (Eventually.of_forall fun t ↦ ?_)
  have := norm_integrand_le hGRH hχ hε hε1 hN (s := σ + t * I) (by simpa using h1)
    (by simpa using h2)
  simpa [domLine] using this

/-- Horizontal integrals across the strip vanish at height `±∞`. -/
lemma tendsto_horizontal (hGRH : GRHHyp) {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) {N : ℕ} (hN : 0 < N) (l : Filter ℝ)
    (hl : Tendsto (fun T : ℝ ↦ |T|) l atTop) :
    Tendsto (fun T : ℝ ↦ ∫ x in (1 / 2 + ε)..2, integrand χ N (x + T * I)) l (𝓝 0) := by
  set A : ℝ := Real.log (2 + 8 * q)
  have hA : 0 ≤ A := Real.log_nonneg (by have := (Nat.cast_nonneg q : (0 : ℝ) ≤ q); linarith)
  set C : ℝ := 96 / ε ^ 2 * (N : ℝ) ^ (2 : ℝ) * 2
  have hC : 0 ≤ C := by positivity
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  -- pointwise bound on the segment
  have hpt : ∀ T : ℝ, ∀ x ∈ Ι (1 / 2 + ε) 2, ‖integrand χ N (x + T * I)‖ ≤
      96 / ε ^ 2 * (N : ℝ) ^ (2 : ℝ) * ((A + Real.log (4 + |T|)) * (1 + T ^ 2)⁻¹) := by
    intro T x hx
    rw [uIoc_of_le (by linarith)] at hx
    have hre : ((x : ℂ) + T * I).re = x := by simp
    have him : ((x : ℂ) + T * I).im = T := by simp
    have := norm_integrand_le hGRH hχ hε hε1 hN (s := x + T * I) (by rw [hre]; exact hx.1.le)
      (by rw [hre]; exact hx.2)
    rw [hre, him] at this
    refine this.trans ?_
    have hnn : 0 ≤ (A + Real.log (4 + |T|)) * (1 + T ^ 2)⁻¹ := by
      have : 0 ≤ Real.log (4 + |T|) := Real.log_nonneg (by linarith [abs_nonneg T])
      positivity
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hN1 hx.2) (by positivity)) hnn
  -- eventual bound by C (A + 5) / |T|
  have hev : ∀ᶠ T : ℝ in l, ‖∫ x : ℝ in (1 / 2 + ε)..2, integrand χ N ((x : ℂ) + (T : ℂ) * I)‖ ≤
      C * (A + 5) * |T|⁻¹ := by
    filter_upwards [hl.eventually_ge_atTop 1] with T hT
    have hT0 : 0 < |T| := by linarith
    have hint := intervalIntegral.norm_integral_le_of_norm_le_const (hpt T)
    refine hint.trans ?_
    have hlen : |(2 : ℝ) - (1 / 2 + ε)| ≤ 2 := by
      rw [abs_le]; constructor <;> linarith
    have hlogT : Real.log (4 + |T|) ≤ 4 + |T| := by
      have := Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < 4 + |T|); linarith
    have hsq : |T| ^ 2 = T ^ 2 := sq_abs T
    have hL0 : 0 ≤ Real.log (4 + |T|) := Real.log_nonneg (by linarith [abs_nonneg T])
    have hnum : A + Real.log (4 + |T|) ≤ (A + 5) * |T| := by nlinarith
    have hden : |T| ^ 2 ≤ 1 + T ^ 2 := by rw [hsq]; linarith
    have key : (A + Real.log (4 + |T|)) * (1 + T ^ 2)⁻¹ ≤ (A + 5) * |T|⁻¹ := by
      calc (A + Real.log (4 + |T|)) * (1 + T ^ 2)⁻¹ ≤ ((A + 5) * |T|) * (|T| ^ 2)⁻¹ :=
            mul_le_mul hnum (inv_anti₀ (by positivity) hden) (by positivity) (by positivity)
        _ = (A + 5) * |T|⁻¹ := by field_simp
    calc 96 / ε ^ 2 * (N : ℝ) ^ (2 : ℝ) * ((A + Real.log (4 + |T|)) * (1 + T ^ 2)⁻¹) *
          |(2 : ℝ) - (1 / 2 + ε)|
        ≤ 96 / ε ^ 2 * (N : ℝ) ^ (2 : ℝ) * ((A + 5) * |T|⁻¹) * 2 := by
          gcongr
      _ = C * (A + 5) * |T|⁻¹ := by simp only [C]; ring
  have hlim : Tendsto (fun T : ℝ ↦ C * (A + 5) * |T|⁻¹) l (𝓝 0) := by
    have := (tendsto_inv_atTop_zero.comp hl).const_mul (C * (A + 5))
    simpa using this
  exact squeeze_zero_norm' hev hlim

/-! ### The main estimate -/

lemma one_lt_log_three : 1 < Real.log 3 := by
  rw [Real.lt_log_iff_exp_lt (by norm_num)]
  have := Real.exp_one_lt_d9
  linarith

/-- **Uniform bound for weighted prime character sums under GRH.** -/
theorem norm_sum_vonMangoldt_char_le (hGRH : GRHHyp) {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1)
    {N : ℕ} (hN : 3 ≤ N) :
    ‖∑ n ∈ Finset.Ioo 0 N, χ n * (Λ n : ℂ) * (((1 - (n : ℝ) / N : ℝ)) : ℂ)‖ ≤
      48 * Real.exp 1 / Real.pi * Real.log N ^ 2 * Real.sqrt N *
        (Real.pi * Real.log (2 + 8 * q) + Jconst) := by
  have hN0 : 0 < N := by omega
  have hNr : (3 : ℝ) ≤ N := by exact_mod_cast hN
  have hlogN : 1 < Real.log N :=
    lt_of_lt_of_le one_lt_log_three (Real.log_le_log (by norm_num) hNr)
  set ε : ℝ := 1 / Real.log N with hεdef
  have hε : 0 < ε := by positivity
  have hε1 : ε ≤ 1 := by rw [hεdef, div_le_one (by linarith)]; linarith
  set σ₀ : ℝ := 1 / 2 + ε with hσ₀def
  -- the Dirichlet coefficients
  set a : ℕ → ℂ := ↗χ * ↗Λ with ha
  have hsum : Summable fun n : ℕ ↦ ‖a n‖ / (n : ℝ) ^ (2 : ℝ) := by
    have hΛ := (ArithmeticFunction.LSeriesSummable_vonMangoldt (s := 2) (by norm_num)).norm
    refine Summable.of_nonneg_of_le (fun n ↦ by positivity) (fun n ↦ ?_) hΛ
    rw [LSeries.norm_term_eq]
    rcases eq_or_ne n 0 with rfl | hn
    · simp [ha]
    · simp only [hn, ite_false]
      simp only [ha, Pi.mul_apply, norm_mul, re_ofNat]
      gcongr
      exact mul_le_of_le_one_left (norm_nonneg _) (χ.norm_le_one n)
  have hperron := SchoenfeldRH.Explicit.perron_weighted_mu a 2 1 (by norm_num) (by norm_num)
    hsum N (by omega)
  -- identify the series with `-L'/L` on `Re s = 2`
  have hline2 : ∀ t : ℝ, LSeries a ((2 : ℝ) + t * I) * ((N : ℂ) ^ (((2 : ℝ) : ℂ) + t * I) *
      (1 / (((2 : ℝ) : ℂ) + t * I) - 1 / (((2 : ℝ) : ℂ) + t * I + ((1 : ℝ) : ℂ)))) =
      integrand χ N ((2 : ℝ) + t * I) := by
    intro t
    have hre : 1 < (((2 : ℝ) : ℂ) + t * I).re := by simp
    rw [integrand, perronKernel, ha, LSeries_twist_vonMangoldt_eq χ hre,
      ← χ.LFunction_eq_LSeries hre, ← deriv_LFunction_eq_deriv_LSeries χ hre]
    simp only [ofReal_one]
    ring
  have hsumeq : ∑ n ∈ Finset.Ioo 0 N, χ n * (Λ n : ℂ) * (((1 - (n : ℝ) / N : ℝ)) : ℂ) =
      ∑ n ∈ Finset.Ioo 0 N, a n * (((1 - ((n : ℝ) / N) ^ (1 : ℝ) : ℝ)) : ℂ) := by
    refine Finset.sum_congr rfl fun n _ ↦ ?_
    simp [ha, Real.rpow_one]
  -- shift the line
  have hshift : ∫ t : ℝ, integrand χ N ((2 : ℝ) + t * I) =
      ∫ t : ℝ, integrand χ N (σ₀ + t * I) := by
    symm
    refine integral_vertical_eq (differentiableOn_integrand hGRH hχ hN0 (by linarith)
      (by linarith)) (integrable_integrand_line hGRH hχ hε hε1 hN0 le_rfl (by linarith))
      (integrable_integrand_line hGRH hχ hε hε1 hN0 (by linarith) le_rfl)
      (tendsto_horizontal hGRH hχ hε hε1 hN0 atTop tendsto_abs_atTop_atTop)
      (tendsto_horizontal hGRH hχ hε hε1 hN0 atBot tendsto_abs_atBot_atTop)
  -- bound on the shifted line
  have hbound : ‖∫ t : ℝ, integrand χ N (σ₀ + t * I)‖ ≤ ∫ t, domLine ε N q σ₀ t := by
    refine norm_integral_le_of_norm_le (integrable_domLine ε N q σ₀)
      (Eventually.of_forall fun t ↦ ?_)
    have := norm_integrand_le hGRH hχ hε hε1 hN0 (s := σ₀ + t * I) (by simp [σ₀])
      (by simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im]; simp [σ₀]; linarith)
    simpa [domLine] using this
  -- N^σ₀ = e √N
  have hNpow : (N : ℝ) ^ σ₀ = Real.exp 1 * Real.sqrt N := by
    have hNpos : (0 : ℝ) < N := by positivity
    rw [Real.rpow_add hNpos, Real.sqrt_eq_rpow, Real.rpow_def_of_pos hNpos (1 / Real.log N)]
    rw [mul_one_div_cancel (by linarith)]
    ring
  have hJ : 0 ≤ Real.pi * Real.log (2 + 8 * q) + Jconst := by
    have h1 : 0 ≤ Jconst := integral_nonneg fun r ↦ by
      have : 0 ≤ Real.log (4 + |r|) := Real.log_nonneg (by linarith [abs_nonneg r])
      positivity
    have h2 : 0 ≤ Real.log (2 + 8 * (q : ℝ)) :=
      Real.log_nonneg (by have := (Nat.cast_nonneg q : (0 : ℝ) ≤ q); linarith)
    positivity
  rw [hsumeq, hperron, funext hline2, hshift, norm_mul]
  calc ‖(1 / (2 * Real.pi) : ℂ)‖ * ‖∫ t : ℝ, integrand χ N (σ₀ + t * I)‖
      ≤ 1 / (2 * Real.pi) * (96 / ε ^ 2 * (N : ℝ) ^ σ₀ *
          (Real.pi * Real.log (2 + 8 * q) + Jconst)) := by
        rw [← integral_domLine]
        have : ‖(1 / (2 * Real.pi) : ℂ)‖ = 1 / (2 * Real.pi) := by
          rw [norm_div, norm_one, norm_mul, Complex.norm_ofNat, Complex.norm_real,
            Real.norm_eq_abs, abs_of_pos Real.pi_pos]
        rw [this]
        exact mul_le_mul_of_nonneg_left hbound (by positivity)
    _ = 48 * Real.exp 1 / Real.pi * Real.log N ^ 2 * Real.sqrt N *
          (Real.pi * Real.log (2 + 8 * q) + Jconst) := by
        rw [hNpow, hεdef]
        field_simp
        ring

end GRHPseudo
