import GRHPseudo.AnalyticNumberTheory.Sharp.Majorant

/-!
# The convolution-square kernel

Test function (window `[−A, 0]`, transition width `1/64`, `S = Real.smoothTransition`):

    f_A(t) = e^{t/2} · S(64(t + A)) · S(−64 t).

Kernel `K_A = f_A ⋆ f_A = weilTest f_A (tilde f_A)`, supported in `[−2A, 0]`, with majorant
`M_A = f_A ⋆ f̃_A = weilTest f_A f_A`, supported in `[−A, A]`. Facts proved here:
* `K_A(u) = ∫ f(t) f(u − t) dt ≥ 0` and `K_A(u) ≤ A e^{u/2}`; `K_A(u) = 0` for `u > 0` or `u < −2A`;
* `M_A(u) = ∫ f(t) f(t − u) dt`, `0 ≤ M_A(u) ≤ (1 − e^{−A}) e^{−|u|/2}`;
* `F₊ = ∫ f e^{t/2} ∈ [e^{−1/64} − e^{−A+1/64}, 1]` and `0 ≤ F₋ = ∫ f e^{−t/2} ≤ A`;
* `K̂_A(−i/2) = F₊²`, `K̂_A(i/2) = F₋²`, `M̂_A(±i/2) = F₊F₋`;
* `∫ |f_A'| ≤ 3`, hence `|r| ‖f̂_A(r)‖ ≤ 3`.

Provenance: the proof of `integral_abs_deriv_F_le` follows grh-miller's `integral_abs_deriv_testFN_le`
(amrehan/grh-miller v1.0.0, `GRHMiller/Ankeny.lean`, Apache-2.0), adapted to this test function.
-/

noncomputable section

open Complex MeasureTheory Zeta23 Zeta23.EF
open scoped Real ComplexConjugate

namespace GRHPseudo.Sharp.Conv

/-- The cutoff `η_A(t) = S(64(t + A)) S(−64 t)`. -/
def eta (A t : ℝ) : ℝ := Real.smoothTransition (64 * (t + A)) * Real.smoothTransition (-(64 * t))

/-- The real test function `f_A(t) = e^{t/2} η_A(t)`. -/
def F (A t : ℝ) : ℝ := Real.exp (t / 2) * eta A t

/-- The complex test function. -/
def f (A : ℝ) : ℝ → ℂ := fun t ↦ (F A t : ℂ)

/-- The kernel `K_A = f_A ⋆ f_A`. -/
def K (A : ℝ) : ℝ → ℂ := weilTest (f A) (tilde (f A))

/-- The majorant `M_A = f_A ⋆ f̃_A`. -/
def M (A : ℝ) : ℝ → ℂ := weilTest (f A) (f A)

variable {A : ℝ}

lemma eta_nonneg (A t : ℝ) : 0 ≤ eta A t :=
  mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _)

lemma eta_le_one (A t : ℝ) : eta A t ≤ 1 :=
  mul_le_one₀ (Real.smoothTransition.le_one _) (Real.smoothTransition.nonneg _)
    (Real.smoothTransition.le_one _)

lemma eta_eq_one {t : ℝ} (h1 : -A + 1 / 64 ≤ t) (h2 : t ≤ -(1 / 64)) : eta A t = 1 := by
  unfold eta
  rw [Real.smoothTransition.one_of_one_le (by linarith),
    Real.smoothTransition.one_of_one_le (by linarith), mul_one]

lemma eta_eq_zero {t : ℝ} (ht : t ∉ Set.Icc (-A) 0) : eta A t = 0 := by
  unfold eta
  rw [Set.mem_Icc, not_and_or, not_le, not_le] at ht
  rcases ht with h | h
  · rw [Real.smoothTransition.zero_of_nonpos (x := 64 * (t + A)) (by linarith), zero_mul]
  · rw [Real.smoothTransition.zero_of_nonpos (x := -(64 * t)) (by linarith), mul_zero]

lemma F_nonneg (A t : ℝ) : 0 ≤ F A t := mul_nonneg (Real.exp_pos _).le (eta_nonneg A t)

lemma F_le_exp (A t : ℝ) : F A t ≤ Real.exp (t / 2) :=
  mul_le_of_le_one_right (Real.exp_pos _).le (eta_le_one A t)

lemma F_eq_zero {t : ℝ} (ht : t ∉ Set.Icc (-A) 0) : F A t = 0 := by
  rw [F, eta_eq_zero ht, mul_zero]

lemma F_le_one (A t : ℝ) : F A t ≤ 1 := by
  by_cases ht : t ∈ Set.Icc (-A) 0
  · exact (F_le_exp A t).trans (Real.exp_le_one_iff.mpr (by linarith [ht.2]))
  · rw [F_eq_zero ht]; exact zero_le_one

lemma contDiff_F (A : ℝ) : ContDiff ℝ 2 (F A) := by
  unfold F eta
  exact (Real.contDiff_exp.comp (contDiff_id.div_const 2)).mul
    ((Real.smoothTransition.contDiff.comp (contDiff_const.mul (contDiff_id.add contDiff_const))).mul
      (Real.smoothTransition.contDiff.comp (contDiff_const.mul contDiff_id).neg))

lemma contDiff_f (A : ℝ) : ContDiff ℝ 2 (f A) := Complex.ofRealCLM.contDiff.comp (contDiff_F A)

lemma support_F_subset (A : ℝ) : Function.support (F A) ⊆ Set.Icc (-A) 0 := fun t ht ↦ by
  by_contra h; exact ht (F_eq_zero h)

lemma hasCompactSupport_F (A : ℝ) : HasCompactSupport (F A) :=
  HasCompactSupport.of_support_subset_isCompact isCompact_Icc (support_F_subset A)

lemma hasCompactSupport_f (A : ℝ) : HasCompactSupport (f A) :=
  (hasCompactSupport_F A).comp_left (g := fun x : ℝ ↦ (x : ℂ)) Complex.ofReal_zero

lemma f_supp (hA : 0 ≤ A) : ∀ u, f A u ≠ 0 → |u| ≤ A := fun u hu ↦ by
  have : F A u ≠ 0 := fun h ↦ hu (by simp [f, h])
  have hm := support_F_subset A this
  rw [abs_le]; exact ⟨hm.1, by linarith [hm.2]⟩

lemma integrable_F (A : ℝ) : Integrable (F A) :=
  (contDiff_F A).continuous.integrable_of_hasCompactSupport (hasCompactSupport_F A)

/-! ### Pointwise formulas for `K` and `M` -/

lemma K_apply (A u : ℝ) : K A u = ((∫ t, F A t * F A (u - t) : ℝ) : ℂ) := by
  simp only [K, weilTest, MeasureTheory.convolution_def, ContinuousLinearMap.mul_apply', tilde, f,
    Complex.conj_ofReal, neg_neg]
  rw [← integral_complex_ofReal]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t ↦ ?_)
  simp only [Complex.ofReal_mul]

lemma M_apply (A u : ℝ) : M A u = ((∫ t, F A t * F A (t - u) : ℝ) : ℂ) := by
  simp only [M, weilTest, MeasureTheory.convolution_def, ContinuousLinearMap.mul_apply', tilde, f,
    Complex.conj_ofReal]
  rw [← integral_complex_ofReal]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t ↦ ?_)
  simp only [Complex.ofReal_mul]
  congr 3; ring

lemma K_real (A u : ℝ) : K A u = ((K A u).re : ℂ) := by rw [K_apply]; simp

lemma M_real (A u : ℝ) : M A u = ((M A u).re : ℂ) := by rw [M_apply]; simp

lemma K_re_nonneg (A u : ℝ) : 0 ≤ (K A u).re := by
  rw [K_apply, Complex.ofReal_re]
  exact integral_nonneg fun t ↦ mul_nonneg (F_nonneg A t) (F_nonneg A _)

lemma M_re_nonneg (A u : ℝ) : 0 ≤ (M A u).re := by
  rw [M_apply, Complex.ofReal_re]
  exact integral_nonneg fun t ↦ mul_nonneg (F_nonneg A t) (F_nonneg A _)

lemma K_eq_zero_of_pos {u : ℝ} (hu : 0 < u) : K A u = 0 := by
  rw [K_apply]
  have : ∀ t, F A t * F A (u - t) = 0 := by
    intro t
    by_cases ht : t ≤ 0
    · rw [F_eq_zero (t := u - t) (fun h ↦ by linarith [h.2]), mul_zero]
    · rw [F_eq_zero (t := t) (fun h ↦ ht h.2), zero_mul]
  simp [this]

lemma K_eq_zero_of_lt {u : ℝ} (hu : u < -(2 * A)) : K A u = 0 := by
  rw [K_apply]
  have : ∀ t, F A t * F A (u - t) = 0 := by
    intro t
    by_cases ht : -A ≤ t
    · rw [F_eq_zero (t := u - t) (fun h ↦ by linarith [h.1]), mul_zero]
    · rw [F_eq_zero (t := t) (fun h ↦ ht h.1), zero_mul]
  simp [this]

lemma M_eq_zero {u : ℝ} (hu : A < |u|) : M A u = 0 := by
  rw [M_apply]
  have : ∀ t, F A t * F A (t - u) = 0 := by
    intro t
    by_cases ht : t ∈ Set.Icc (-A) 0
    · by_cases ht' : t - u ∈ Set.Icc (-A) 0
      · exfalso
        have : |u| ≤ A := abs_le.mpr ⟨by linarith [ht.1, ht'.2], by linarith [ht.2, ht'.1]⟩
        linarith
      · rw [F_eq_zero ht', mul_zero]
    · rw [F_eq_zero ht, zero_mul]
  simp [this]

/-- Integral of a nonnegative function supported in `[−A, 0]` bounded by `g` there. -/
lemma integral_le_of_supp {φ g : ℝ → ℝ} (hA : 0 ≤ A) (hφi : Integrable φ) (hgc : Continuous g)
    (hzero : ∀ t ∉ Set.Icc (-A) 0, φ t = 0) (hle : ∀ t ∈ Set.Icc (-A) 0, φ t ≤ g t) :
    ∫ t, φ t ≤ ∫ t in (-A)..0, g t := by
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hzero, intervalIntegral.integral_of_le
    (by linarith), ← integral_Icc_eq_integral_Ioc]
  exact setIntegral_mono_on hφi.integrableOn hgc.integrableOn_Icc measurableSet_Icc hle

lemma integrable_F_mul (A : ℝ) {g : ℝ → ℝ} (hg : Continuous g) : Integrable (fun t ↦ F A t * g t) :=
  ((contDiff_F A).continuous.mul hg).integrable_of_hasCompactSupport (hasCompactSupport_F A).mul_right

lemma K_le (hA : 0 ≤ A) (u : ℝ) : (K A u).re ≤ A * Real.exp (u / 2) := by
  rw [K_apply, Complex.ofReal_re]
  have hc : Continuous fun t ↦ F A (u - t) := (contDiff_F A).continuous.comp (by fun_prop)
  calc ∫ t, F A t * F A (u - t) ≤ ∫ t in (-A)..0, Real.exp (u / 2) :=
        integral_le_of_supp hA (integrable_F_mul A hc) continuous_const
          (fun t ht ↦ by rw [F_eq_zero ht, zero_mul]) fun t _ ↦ by
            have h1 := F_le_exp A t
            have h2 := F_le_exp A (u - t)
            have : Real.exp (t / 2) * Real.exp ((u - t) / 2) = Real.exp (u / 2) := by
              rw [← Real.exp_add]; ring_nf
            rw [← this]
            exact mul_le_mul h1 h2 (F_nonneg _ _) (Real.exp_pos _).le
    _ = A * Real.exp (u / 2) := by rw [intervalIntegral.integral_const, smul_eq_mul]; ring

lemma integral_exp_window (A : ℝ) : ∫ t in (-A)..0, Real.exp t = 1 - Real.exp (-A) := by
  rw [integral_exp, Real.exp_zero]

lemma M_le_of_nonneg (hA : 0 ≤ A) {u : ℝ} (hu : 0 ≤ u) :
    (M A u).re ≤ (1 - Real.exp (-A)) * Real.exp (-(u / 2)) := by
  rw [M_apply, Complex.ofReal_re]
  have hc : Continuous fun t ↦ F A (t - u) := (contDiff_F A).continuous.comp (by fun_prop)
  have hgc : Continuous fun t ↦ Real.exp t * Real.exp (-(u / 2)) := by fun_prop
  calc ∫ t, F A t * F A (t - u) ≤ ∫ t in (-A)..0, Real.exp t * Real.exp (-(u / 2)) :=
        integral_le_of_supp hA (integrable_F_mul A hc) hgc
          (fun t ht ↦ by rw [F_eq_zero ht, zero_mul]) fun t _ ↦ by
            have h1 := F_le_exp A t
            have h2 := F_le_exp A (t - u)
            have : Real.exp (t / 2) * Real.exp ((t - u) / 2) = Real.exp t * Real.exp (-(u / 2)) := by
              rw [← Real.exp_add, ← Real.exp_add]; ring_nf
            rw [← this]
            exact mul_le_mul h1 h2 (F_nonneg _ _) (Real.exp_pos _).le
    _ = (1 - Real.exp (-A)) * Real.exp (-(u / 2)) := by
        rw [intervalIntegral.integral_mul_const, integral_exp_window]

lemma M_zero_le (hA : 0 ≤ A) : (M A 0).re ≤ 1 - Real.exp (-A) := by
  have := M_le_of_nonneg hA le_rfl
  simpa using this

lemma norm_M_le (hA : 0 ≤ A) (u : ℝ) : ‖M A u‖ ≤ Real.exp (-(|u| / 2)) := by
  have hE : 1 - Real.exp (-A) ≤ 1 := by linarith [Real.exp_pos (-A)]
  have key : ∀ v, 0 ≤ v → ‖M A v‖ ≤ Real.exp (-(v / 2)) := fun v hv ↦ by
    rw [M_real, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (M_re_nonneg A v)]
    exact (M_le_of_nonneg hA hv).trans (mul_le_of_le_one_left (Real.exp_pos _).le hE)
  rcases le_total 0 u with hu | hu
  · rw [abs_of_nonneg hu]; exact key u hu
  · have h := key (-u) (by linarith)
    rw [show M A (-u) = conj (M A u) from GRHMiller.weilTest_self_neg (f A) u, Complex.norm_conj] at h
    rw [abs_of_nonpos hu]; exact h

/-! ### The Laplace values `F₊`, `F₋` -/

/-- `F₊ = ∫ f e^{t/2}`. -/
def Fp (A : ℝ) : ℝ := ∫ t, F A t * Real.exp (t / 2)

/-- `F₋ = ∫ f e^{−t/2}`. -/
def Fm (A : ℝ) : ℝ := ∫ t, F A t * Real.exp (-(t / 2))

lemma paperFT_f_neg_I_half (A : ℝ) : paperFT (f A) (-I / 2) = (Fp A : ℂ) := by
  unfold paperFT Fp f
  rw [← integral_complex_ofReal]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t ↦ ?_)
  have : I * (-I / 2) * (t : ℂ) = ((t / 2 : ℝ) : ℂ) := by
    push_cast; ring_nf; rw [I_sq]; ring
  simp only [this, ← Complex.ofReal_exp, Complex.ofReal_mul]

lemma paperFT_f_I_half (A : ℝ) : paperFT (f A) (I / 2) = (Fm A : ℂ) := by
  unfold paperFT Fm f
  rw [← integral_complex_ofReal]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t ↦ ?_)
  have : I * (I / 2) * (t : ℂ) = ((-(t / 2) : ℝ) : ℂ) := by
    push_cast; ring_nf; rw [I_sq]; ring
  simp only [this, ← Complex.ofReal_exp, Complex.ofReal_mul]

lemma Fp_le_one (hA : 0 ≤ A) : Fp A ≤ 1 := by
  have h := integral_le_of_supp (φ := fun t ↦ F A t * Real.exp (t / 2)) (g := Real.exp) hA
    (integrable_F_mul A (by fun_prop)) Real.continuous_exp
    (fun t ht ↦ by simp only [F_eq_zero ht, zero_mul]) fun t _ ↦ by
      have : Real.exp (t / 2) * Real.exp (t / 2) = Real.exp t := by rw [← Real.exp_add]; ring_nf
      rw [← this]; exact mul_le_mul_of_nonneg_right (F_le_exp A t) (Real.exp_pos _).le
  rw [integral_exp_window] at h
  unfold Fp; linarith [Real.exp_pos (-A)]

lemma Fp_ge (hA : 1 / 32 ≤ A) :
    Real.exp (-(1 / 64)) - Real.exp (-A + 1 / 64) ≤ Fp A := by
  have hφi := integrable_F_mul A (g := fun t ↦ Real.exp (t / 2)) (by fun_prop)
  have h0 : ∀ t, 0 ≤ F A t * Real.exp (t / 2) := fun t ↦ mul_nonneg (F_nonneg A t) (Real.exp_pos _).le
  have hplat : ∫ t in Set.Icc (-A + 1 / 64) (-(1 / 64)), F A t * Real.exp (t / 2) =
      Real.exp (-(1 / 64)) - Real.exp (-A + 1 / 64) := by
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith)]
    rw [intervalIntegral.integral_congr (g := Real.exp) fun t ht ↦ by
      rw [Set.uIcc_of_le (by linarith)] at ht
      simp only [F, eta_eq_one ht.1 ht.2, mul_one]
      rw [← Real.exp_add]; ring_nf]
    rw [integral_exp]
  rw [← hplat]
  exact setIntegral_le_integral hφi (Filter.Eventually.of_forall h0)

lemma Fp_nonneg (A : ℝ) : 0 ≤ Fp A :=
  integral_nonneg fun t ↦ mul_nonneg (F_nonneg A t) (Real.exp_pos _).le

lemma Fm_nonneg (A : ℝ) : 0 ≤ Fm A :=
  integral_nonneg fun t ↦ mul_nonneg (F_nonneg A t) (Real.exp_pos _).le

lemma Fm_le (hA : 0 ≤ A) : Fm A ≤ A := by
  have h := integral_le_of_supp (φ := fun t ↦ F A t * Real.exp (-(t / 2))) (g := fun _ ↦ 1) hA
    (integrable_F_mul A (by fun_prop)) continuous_const
    (fun t ht ↦ by simp only [F_eq_zero ht, zero_mul]) fun t _ ↦ by
      have : Real.exp (t / 2) * Real.exp (-(t / 2)) = 1 := by rw [← Real.exp_add]; simp
      rw [← this]; exact mul_le_mul_of_nonneg_right (F_le_exp A t) (Real.exp_pos _).le
  rw [intervalIntegral.integral_const, smul_eq_mul, mul_one] at h
  unfold Fm; linarith

/-! ### Transforms at `±i/2` -/

lemma paperFT_K (A : ℝ) (z : ℂ) : paperFT (K A) z = paperFT (f A) z ^ 2 :=
  paperFT_convSq (contDiff_f A).continuous (hasCompactSupport_f A) z

lemma paperFT_K_neg_I_half (A : ℝ) : paperFT (K A) (-I / 2) = ((Fp A ^ 2 : ℝ) : ℂ) := by
  rw [paperFT_K, paperFT_f_neg_I_half]; push_cast; ring

lemma paperFT_K_I_half (A : ℝ) : paperFT (K A) (I / 2) = ((Fm A ^ 2 : ℝ) : ℂ) := by
  rw [paperFT_K, paperFT_f_I_half]; push_cast; ring

lemma poleSide_M (A : ℝ) : poleSide (M A) = ((2 * (Fp A * Fm A) : ℝ) : ℂ) := by
  have hf := (contDiff_f A).continuous
  have hfs := hasCompactSupport_f A
  unfold poleSide M
  rw [paperFT_weilTest hf hf hfs hfs, paperFT_weilTest hf hf hfs hfs]
  have h1 : conj (I / 2) = -I / 2 := by rw [map_div₀, Complex.conj_I, map_ofNat]
  have h2 : conj (-I / 2) = I / 2 := by rw [map_div₀, map_neg, Complex.conj_I, map_ofNat, neg_neg]
  rw [h1, h2, paperFT_f_I_half, paperFT_f_neg_I_half, Complex.conj_ofReal, Complex.conj_ofReal]
  push_cast; ring

lemma norm_paperFT_K (A r : ℝ) : ‖paperFT (K A) (r : ℂ)‖ = ‖paperFT (f A) (r : ℂ)‖ ^ 2 :=
  norm_paperFT_convSq (contDiff_f A).continuous (hasCompactSupport_f A) r

lemma contDiff_K (A : ℝ) : ContDiff ℝ 2 (K A) :=
  weilTest_contDiff (contDiff_f A) (continuous_tilde (contDiff_f A).continuous) (hasCompactSupport_f A)

lemma hasCompactSupport_K (A : ℝ) : HasCompactSupport (K A) :=
  weilTest_hasCompactSupport (hasCompactSupport_f A) (hasCompactSupport_tilde (hasCompactSupport_f A))

/-! ### Decay: `|r| ‖f̂(r)‖ ≤ ∫ |f'| ≤ 3` -/

lemma hasDerivAt_F (A t : ℝ) :
    HasDerivAt (F A)
      (Real.exp (t / 2) * (1 / 2) * eta A t + Real.exp (t / 2) *
        (deriv Real.smoothTransition (64 * (t + A)) * (64 * 1) * Real.smoothTransition (-(64 * t))
          + Real.smoothTransition (64 * (t + A)) *
            (deriv Real.smoothTransition (-(64 * t)) * -(64 * 1)))) t := by
  have hS : ∀ x, HasDerivAt Real.smoothTransition (deriv Real.smoothTransition x) x := fun x ↦
    ((Real.smoothTransition.contDiff (n := 1)).differentiable one_ne_zero x).hasDerivAt
  have h1 := ((hasDerivAt_id' t).div_const 2).exp
  have h2 := (hS (64 * (t + A))).comp t (((hasDerivAt_id' t).add_const A).const_mul 64)
  have h3 := (hS (-(64 * t))).comp t (((hasDerivAt_id' t).const_mul 64).neg)
  have h := h1.mul (h2.mul h3)
  unfold F eta
  exact h

lemma integral_F_le (hA : 0 ≤ A) : ∫ t, F A t ≤ 2 := by
  have h := integral_le_of_supp (φ := F A) (g := fun t ↦ Real.exp (t / 2)) hA (integrable_F A)
    (by fun_prop) (fun t ht ↦ F_eq_zero ht) fun t _ ↦ F_le_exp A t
  have hI : ∫ t in (-A)..0, Real.exp (t / 2) = 2 - 2 * Real.exp (-A / 2) := by
    rw [intervalIntegral.integral_comp_div (fun x ↦ Real.exp x) (by norm_num : (2 : ℝ) ≠ 0),
      integral_exp, zero_div, Real.exp_zero, smul_eq_mul]
    ring
  rw [hI] at h
  linarith [Real.exp_pos (-A / 2)]

lemma integral_abs_deriv_F_le (hA : 1 / 64 ≤ A) : ∫ t, |deriv (F A) t| ≤ 3 := by
  have hA0 : 0 ≤ A := by linarith
  set S' := deriv Real.smoothTransition
  have hS'c := GRHMiller.Narrow.continuous_deriv_smoothTransition'
  set w1 : ℝ → ℝ := fun t ↦ 64 * S' (64 * (t + A))
  set w2 : ℝ → ℝ := fun t ↦ 64 * S' (-(64 * t))
  have hw1c : Continuous w1 := continuous_const.mul (hS'c.comp (by fun_prop))
  have hw2c : Continuous w2 := continuous_const.mul (hS'c.comp (by fun_prop))
  have hsupp1 : ∀ t, w1 t ≠ 0 → t ∈ Set.Icc (-A) (-A + 1 / 64) := fun t ht ↦ by
    have h' : S' (64 * (t + A)) ≠ 0 := fun h ↦ ht (by simp [w1, h])
    have := (not_imp_comm.mp GRHMiller.Narrow.deriv_smoothTransition_eq_zero') h'
    rw [Set.mem_Icc] at this ⊢; constructor <;> linarith
  have hsupp2 : ∀ t, w2 t ≠ 0 → t ∈ Set.Icc (-(1 / 64)) 0 := fun t ht ↦ by
    have h' : S' (-(64 * t)) ≠ 0 := fun h ↦ ht (by simp [w2, h])
    have := (not_imp_comm.mp GRHMiller.Narrow.deriv_smoothTransition_eq_zero') h'
    rw [Set.mem_Icc] at this ⊢; constructor <;> linarith
  have hw1cs : HasCompactSupport w1 :=
    HasCompactSupport.of_support_subset_isCompact isCompact_Icc fun t ht ↦ hsupp1 t ht
  have hw2cs : HasCompactSupport w2 :=
    HasCompactSupport.of_support_subset_isCompact isCompact_Icc fun t ht ↦ hsupp2 t ht
  have hw1i : Integrable w1 := hw1c.integrable_of_hasCompactSupport hw1cs
  have hw2i : Integrable w2 := hw2c.integrable_of_hasCompactSupport hw2cs
  have hint1 : ∫ t, w1 t = 1 := by
    have := integral_add_right_eq_self (fun t ↦ 64 * S' (64 * t)) (μ := volume) A
    simp only [w1]; rw [this]; exact GRHMiller.Narrow.integral_scaled_deriv
  have hint2 : ∫ t, w2 t = 1 := by
    have := integral_neg_eq_self (fun t ↦ 64 * S' (64 * t)) (μ := volume)
    simp only [w2, mul_neg] at this ⊢; rw [this]; exact GRHMiller.Narrow.integral_scaled_deriv
  have hFi := integrable_F A
  have hmaj : Integrable (fun t ↦ F A t / 2 + (w1 t + w2 t)) := (hFi.div_const 2).add (hw1i.add hw2i)
  have hpt : ∀ t, |deriv (F A) t| ≤ F A t / 2 + (w1 t + w2 t) := by
    intro t
    rw [(hasDerivAt_F A t).deriv]
    have hE0 : 0 < Real.exp (t / 2) := Real.exp_pos _
    have he0 := eta_nonneg A t
    have hA' := GRHMiller.Narrow.deriv_smoothTransition_nonneg' (64 * (t + A))
    have hB' := GRHMiller.Narrow.deriv_smoothTransition_nonneg' (-(64 * t))
    have hS1 := Real.smoothTransition.le_one (-(64 * t))
    have hS0 := Real.smoothTransition.nonneg (-(64 * t))
    have hT1 := Real.smoothTransition.le_one (64 * (t + A))
    have hT0 := Real.smoothTransition.nonneg (64 * (t + A))
    -- `e^{t/2} w_i ≤ w_i` since each `w_i` lives on `t ≤ 0`
    have hw1le : Real.exp (t / 2) * w1 t ≤ w1 t := by
      by_cases h : w1 t = 0
      · rw [h, mul_zero]
      · have := (hsupp1 t h).2
        exact mul_le_of_le_one_left (mul_nonneg (by norm_num) hA')
          (Real.exp_le_one_iff.mpr (by linarith))
    have hw2le : Real.exp (t / 2) * w2 t ≤ w2 t := by
      by_cases h : w2 t = 0
      · rw [h, mul_zero]
      · have := (hsupp2 t h).2
        exact mul_le_of_le_one_left (mul_nonneg (by norm_num) hB')
          (Real.exp_le_one_iff.mpr (by linarith))
    have hη : |deriv Real.smoothTransition (64 * (t + A)) * (64 * 1) * Real.smoothTransition (-(64 * t))
        + Real.smoothTransition (64 * (t + A)) * (deriv Real.smoothTransition (-(64 * t)) * -(64 * 1))|
        ≤ w1 t + w2 t := by
      simp only [w1, w2, S']
      rw [abs_le]; constructor <;>
        nlinarith [mul_nonneg hA' hS0, mul_nonneg hB' hT0, mul_le_mul_of_nonneg_left hS1 hA',
          mul_le_mul_of_nonneg_left hT1 hB']
    have hF : F A t = Real.exp (t / 2) * eta A t := rfl
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul, abs_mul, abs_of_pos hE0, abs_of_nonneg he0,
      abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2), hF]
    nlinarith [mul_le_mul_of_nonneg_left hη hE0.le]
  have hF2 := integral_F_le hA0
  calc ∫ t, |deriv (F A) t| ≤ ∫ t, (F A t / 2 + (w1 t + w2 t)) :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall fun t ↦ abs_nonneg _) hmaj
          (Filter.Eventually.of_forall hpt)
    _ = (∫ t, F A t) / 2 + ((∫ t, w1 t) + ∫ t, w2 t) := by
        have e1 : ∫ t, (F A t / 2 + (w1 t + w2 t)) = (∫ t, F A t / 2) + ∫ t, (w1 t + w2 t) :=
          integral_add (hFi.div_const 2) (hw1i.add hw2i)
        have e2 : ∫ t, (w1 t + w2 t) = (∫ t, w1 t) + ∫ t, w2 t := integral_add hw1i hw2i
        rw [e1, e2, integral_div]
    _ ≤ 3 := by rw [hint1, hint2]; linarith

lemma norm_paperFT_f_mul_le (hA : 1 / 64 ≤ A) (r : ℝ) :
    ‖paperFT (f A) (r : ℂ)‖ * |r| ≤ 3 := by
  have hf := contDiff_f A
  have := Taper.norm_paperFT_mul_le (hf.of_le (by norm_num)) (f_supp (by linarith)) (r : ℂ)
  simp only [Complex.ofReal_im, abs_zero, zero_mul, Real.exp_zero, one_mul,
    Complex.norm_real, Real.norm_eq_abs] at this
  refine this.trans ?_
  have hd : ∀ t, deriv (f A) t = ((deriv (F A) t : ℝ) : ℂ) := fun t ↦ by
    rw [(hasDerivAt_F A t).deriv]
    exact ((hasDerivAt_F A t).ofReal_comp).deriv
  simpa [hd, Complex.norm_real, Real.norm_eq_abs] using integral_abs_deriv_F_le hA

end GRHPseudo.Sharp.Conv
