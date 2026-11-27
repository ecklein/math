import GRHPseudo.AnalyticNumberTheory.Sharp.Assembly

/-!
# Closed-form bounds for the cosh kernel (Layer 2, part 1)

For `f_a = testFnN a = cosh(t/2) η_a(t)` (cutoff `η_a = 1` on `|t| ≤ a − 1/64`, `0` off `[−a, a]`)
and `k_a = f_a ⋆ f̃_a`:

* `‖k_a(u)‖ ≤ sinh a + a cosh a` for `|u| ≤ 2a`;
* `A(a) = Re k̂_a(−i/2) = F₊ F₋` and `B(a) = 2 F₊ F₋`, with `F± = ∫ f_a(t) e^{±t/2} dt`;
* `sinh a' + a' ≤ F± ≤ sinh a + a`, with `a' = a − 1/64`.

Hence `A(a) ≥ (sinh a' + a')²` and `B(a) ≤ 2 (sinh a + a)²`.
-/

noncomputable section

open Complex MeasureTheory Set Zeta23 Zeta23.EF
open scoped Real ComplexConjugate

namespace GRHPseudo.Sharp

open GRHMiller.Narrow

/-- Vendored from amrehan/grh-miller v1.0.0, `GRHMiller/Explicit.lean`,
`norm_weilTest_testFnN_le_decay` (Apache-2.0). -/
theorem norm_kern_le_decay {a u : ℝ} (hu : u ≤ 2 * a) :
    ‖kern a u‖ ≤ Real.sinh (a - u / 2) + (a - u / 2) * Real.cosh (u / 2) := by
  unfold kern testF
  rw [weilTest_testFnN, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (integral_nonneg fun t ↦ mul_nonneg (testFN_nonneg a t) (testFN_nonneg a _))]
  have hzero : ∀ t ∉ Set.Icc (u - a) a, testFN a t * testFN a (t - u) = 0 := by
    intro t ht
    rw [Set.mem_Icc, not_and_or, not_le, not_le] at ht
    rcases ht with h | h
    · have : testFN a (t - u) = 0 := by
        by_contra hne
        have := support_testFN_subset a hne
        rw [Set.mem_Icc] at this; linarith [this.1]
      rw [this, mul_zero]
    · have : testFN a t = 0 := by
        by_contra hne
        have := support_testFN_subset a hne
        rw [Set.mem_Icc] at this; linarith [this.2]
      rw [this, zero_mul]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hzero]
  have hc : Continuous (fun t : ℝ ↦ (Real.cosh (t - u / 2) + Real.cosh (u / 2)) / 2) := by fun_prop
  have hgc : Continuous (fun t ↦ testFN a t * testFN a (t - u)) :=
    (contDiff_testFN a).continuous.mul
      ((contDiff_testFN a).continuous.comp (continuous_id.sub continuous_const))
  calc ∫ t in Set.Icc (u - a) a, testFN a t * testFN a (t - u)
      ≤ ∫ t in Set.Icc (u - a) a, (Real.cosh (t - u / 2) + Real.cosh (u / 2)) / 2 :=
        setIntegral_mono_on hgc.integrableOn_Icc hc.integrableOn_Icc measurableSet_Icc fun t _ ↦ by
          have h1 := testFN_le_cosh a t
          have h2 := testFN_le_cosh a (t - u)
          have h0' := testFN_nonneg a (t - u)
          have hid : Real.cosh (t / 2) * Real.cosh ((t - u) / 2)
              = (Real.cosh (t - u / 2) + Real.cosh (u / 2)) / 2 := by
            have e1 := Real.cosh_add (t / 2) ((t - u) / 2)
            have e2 := Real.cosh_sub (t / 2) ((t - u) / 2)
            rw [show t / 2 + (t - u) / 2 = t - u / 2 by ring] at e1
            rw [show t / 2 - (t - u) / 2 = u / 2 by ring] at e2
            linarith
          rw [← hid]
          exact mul_le_mul h1 h2 h0' (Real.cosh_pos _).le
    _ = Real.sinh (a - u / 2) + (a - u / 2) * Real.cosh (u / 2) := by
        rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith)]
        have hd : ∀ x, HasDerivAt (fun t : ℝ ↦ Real.sinh (t - u / 2)) (Real.cosh (x - u / 2)) x :=
          fun x ↦ by simpa using ((hasDerivAt_id x).sub_const (u / 2)).sinh
        have hci : Continuous (fun t : ℝ ↦ Real.cosh (t - u / 2)) := by fun_prop
        rw [intervalIntegral.integral_div, intervalIntegral.integral_add
          (hci.intervalIntegrable _ _) intervalIntegrable_const,
          intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ ↦ hd x)
            (hci.intervalIntegrable _ _),
          intervalIntegral.integral_const, smul_eq_mul,
          show u - a - u / 2 = -(a - u / 2) by ring, Real.sinh_neg]
        ring

/-- Uniform size bound on the support. -/
theorem norm_kern_le {a u : ℝ} (ha : 0 ≤ a) (hu : |u| ≤ 2 * a) :
    ‖kern a u‖ ≤ Real.sinh a + a * Real.cosh a := by
  have key : ∀ v : ℝ, 0 ≤ v → v ≤ 2 * a → ‖kern a v‖ ≤ Real.sinh a + a * Real.cosh a := by
    intro v hv0 hv
    refine (norm_kern_le_decay hv).trans ?_
    have h1 : Real.sinh (a - v / 2) ≤ Real.sinh a := Real.sinh_le_sinh.mpr (by linarith)
    have h2 : Real.cosh (v / 2) ≤ Real.cosh a := by
      rw [Real.cosh_le_cosh, abs_of_nonneg (by linarith), abs_of_nonneg ha]; linarith
    have h3 : 0 ≤ a - v / 2 := by linarith
    nlinarith [Real.cosh_pos (v / 2)]
  rcases le_total 0 u with h | h
  · exact key u h (le_trans (le_abs_self u) hu)
  · have hneg : kern a u = conj (kern a (-u)) := by
      have := GRHMiller.weilTest_self_neg (testF a) (-u)
      rw [neg_neg] at this
      exact this
    rw [hneg, Complex.norm_conj]
    exact key (-u) (by linarith) (by rw [abs_of_nonpos h] at hu; linarith)

/-! ### Main and pole terms -/

/-- `F₊ = ∫ f_a(t) e^{t/2} dt`, `F₋ = ∫ f_a(t) e^{−t/2} dt`. -/
def Fplus (a : ℝ) : ℝ := ∫ t, testFN a t * Real.exp (t / 2)
def Fminus (a : ℝ) : ℝ := ∫ t, testFN a t * Real.exp (-t / 2)

lemma paperFT_testF_neg (a : ℝ) : paperFT (testF a) (-I / 2) = (Fplus a : ℂ) := by
  unfold paperFT testF Fplus testFnN
  rw [← integral_complex_ofReal]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t ↦ ?_)
  have : I * (-I / 2) * (t : ℂ) = ((t / 2 : ℝ) : ℂ) := by push_cast; ring_nf; rw [I_sq]; ring
  simp only [this, ← Complex.ofReal_exp]; push_cast; ring

lemma paperFT_testF_pos (a : ℝ) : paperFT (testF a) (I / 2) = (Fminus a : ℂ) := by
  unfold paperFT testF Fminus testFnN
  rw [← integral_complex_ofReal]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t ↦ ?_)
  have : I * (I / 2) * (t : ℂ) = ((-t / 2 : ℝ) : ℂ) := by push_cast; ring_nf; rw [I_sq]; ring
  simp only [this, ← Complex.ofReal_exp]; push_cast; ring

lemma mainA_eq (a : ℝ) : mainA a = Fplus a * Fminus a := by
  unfold mainA kern
  rw [paperFT_weilTest (contDiff_testF a).continuous (contDiff_testF a).continuous
    (hasCompactSupport_testF a) (hasCompactSupport_testF a)]
  have hc : (starRingEnd ℂ) (-I / 2) = I / 2 := by
    rw [map_div₀, map_neg, Complex.conj_I, neg_neg, map_ofNat]
  rw [hc, paperFT_testF_neg, paperFT_testF_pos, Complex.conj_ofReal, ← Complex.ofReal_mul,
    Complex.ofReal_re]

lemma poleB_eq (a : ℝ) : poleB a = 2 * (Fplus a * Fminus a) := by
  unfold poleB poleSide kern
  rw [paperFT_weilTest (contDiff_testF a).continuous (contDiff_testF a).continuous
      (hasCompactSupport_testF a) (hasCompactSupport_testF a),
    paperFT_weilTest (contDiff_testF a).continuous (contDiff_testF a).continuous
      (hasCompactSupport_testF a) (hasCompactSupport_testF a)]
  have hc1 : (starRingEnd ℂ) (I / 2) = -I / 2 := by rw [map_div₀, Complex.conj_I, map_ofNat]
  have hc2 : (starRingEnd ℂ) (-I / 2) = I / 2 := by
    rw [map_div₀, map_neg, Complex.conj_I, neg_neg, map_ofNat]
  rw [hc1, hc2, paperFT_testF_neg, paperFT_testF_pos, Complex.conj_ofReal, Complex.conj_ofReal,
    ← Complex.ofReal_mul, ← Complex.ofReal_mul, ← Complex.ofReal_add, Complex.ofReal_re]
  ring

/-- `∫_{[−c,c]} cosh(t/2) e^{±t/2} dt = sinh c + c`. -/
lemma integral_cosh_mul_exp (c : ℝ) (hc : 0 ≤ c) (s : ℝ) (hs : s = 1 ∨ s = -1) :
    ∫ t in Icc (-c) c, Real.cosh (t / 2) * Real.exp (s * t / 2) = Real.sinh c + c := by
  have hpt : ∀ t : ℝ, Real.cosh (t / 2) * Real.exp (s * t / 2) = (Real.exp (s * t) + 1) / 2 := by
    intro t
    rw [Real.cosh_eq]
    rcases hs with rfl | rfl
    · have h1 : Real.exp (t / 2) * Real.exp (1 * t / 2) = Real.exp (1 * t) := by
        rw [← Real.exp_add]; congr 1; ring
      have h2 : Real.exp (-(t / 2)) * Real.exp (1 * t / 2) = 1 := by
        rw [← Real.exp_add, show -(t / 2) + 1 * t / 2 = 0 by ring, Real.exp_zero]
      linear_combination (h1 + h2) / 2
    · have h1 : Real.exp (t / 2) * Real.exp (-1 * t / 2) = 1 := by
        rw [← Real.exp_add, show t / 2 + -1 * t / 2 = 0 by ring, Real.exp_zero]
      have h2 : Real.exp (-(t / 2)) * Real.exp (-1 * t / 2) = Real.exp (-1 * t) := by
        rw [← Real.exp_add]; congr 1; ring
      linear_combination (h1 + h2) / 2
  simp_rw [hpt]
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith),
    intervalIntegral.integral_div, intervalIntegral.integral_add
      ((by fun_prop : Continuous fun t : ℝ ↦ Real.exp (s * t)).intervalIntegrable _ _)
      intervalIntegrable_const, intervalIntegral.integral_const, smul_eq_mul]
  rcases hs with rfl | rfl
  · simp only [one_mul, integral_exp]
    rw [Real.sinh_eq]; ring
  · have : ∫ x in (-c)..c, Real.exp (-1 * x) = Real.exp c - Real.exp (-c) := by
      have h := intervalIntegral.integral_comp_neg (a := -c) (b := c) Real.exp
      simp only [neg_neg] at h
      simp only [neg_one_mul]
      rw [h, integral_exp]
    rw [this, Real.sinh_eq]; ring

lemma integrable_testFN_mul_exp (a s : ℝ) :
    Integrable fun t ↦ testFN a t * Real.exp (s * t / 2) := by
  have hc : Continuous fun t ↦ testFN a t * Real.exp (s * t / 2) :=
    (contDiff_testFN a).continuous.mul (by fun_prop)
  refine hc.integrable_of_hasCompactSupport ?_
  exact (hasCompactSupport_testFN a).mul_right

/-- Two-sided bounds on `F±`. -/
lemma F_bounds (a s : ℝ) (ha : 1 / 64 ≤ a) (hs : s = 1 ∨ s = -1) :
    Real.sinh (a - 1 / 64) + (a - 1 / 64) ≤ ∫ t, testFN a t * Real.exp (s * t / 2) ∧
      ∫ t, testFN a t * Real.exp (s * t / 2) ≤ Real.sinh a + a := by
  have hint := integrable_testFN_mul_exp a s
  have hnn : ∀ t, 0 ≤ testFN a t * Real.exp (s * t / 2) :=
    fun t ↦ mul_nonneg (testFN_nonneg a t) (Real.exp_pos _).le
  constructor
  · rw [← integral_cosh_mul_exp (a - 1 / 64) (by linarith) s hs]
    calc ∫ t in Icc (-(a - 1 / 64)) (a - 1 / 64), Real.cosh (t / 2) * Real.exp (s * t / 2)
        = ∫ t in Icc (-(a - 1 / 64)) (a - 1 / 64), testFN a t * Real.exp (s * t / 2) := by
          refine setIntegral_congr_fun measurableSet_Icc fun t ht ↦ ?_
          have : |t| ≤ a - 1 / 64 := abs_le.mpr ⟨ht.1, ht.2⟩
          simp only [testFN, etaN_eq_one this, mul_one]
      _ ≤ ∫ t, testFN a t * Real.exp (s * t / 2) :=
          setIntegral_le_integral hint (Filter.Eventually.of_forall hnn)
  · rw [← integral_cosh_mul_exp a (by linarith) s hs]
    have hzero : ∀ t ∉ Icc (-a) a, testFN a t * Real.exp (s * t / 2) = 0 := by
      intro t ht
      have : testFN a t = 0 := by
        by_contra hne; exact ht (support_testFN_subset a hne)
      rw [this, zero_mul]
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hzero]
    have hc : Continuous fun t ↦ Real.cosh (t / 2) * Real.exp (s * t / 2) := by fun_prop
    exact setIntegral_mono_on hint.integrableOn hc.integrableOn_Icc measurableSet_Icc
      fun t _ ↦ mul_le_mul_of_nonneg_right (testFN_le_cosh a t) (Real.exp_pos _).le

lemma Fplus_bounds (a : ℝ) (ha : 1 / 64 ≤ a) :
    Real.sinh (a - 1 / 64) + (a - 1 / 64) ≤ Fplus a ∧ Fplus a ≤ Real.sinh a + a := by
  have := F_bounds a 1 ha (Or.inl rfl)
  simpa [Fplus] using this

lemma Fminus_bounds (a : ℝ) (ha : 1 / 64 ≤ a) :
    Real.sinh (a - 1 / 64) + (a - 1 / 64) ≤ Fminus a ∧ Fminus a ≤ Real.sinh a + a := by
  have := F_bounds a (-1) ha (Or.inr rfl)
  have e : ∀ t : ℝ, -1 * t / 2 = -t / 2 := fun t ↦ by ring
  simp only [e] at this
  simpa [Fminus] using this

/-- `A(a) ≥ (sinh a' + a')²`. -/
theorem mainA_ge (a : ℝ) (ha : 1 / 64 ≤ a) :
    (Real.sinh (a - 1 / 64) + (a - 1 / 64)) ^ 2 ≤ mainA a := by
  rw [mainA_eq]
  have h1 := Fplus_bounds a ha
  have h2 := Fminus_bounds a ha
  have h0 : 0 ≤ Real.sinh (a - 1 / 64) + (a - 1 / 64) := by
    have := Real.sinh_nonneg_iff.mpr (by linarith : (0 : ℝ) ≤ a - 1 / 64); linarith
  rw [sq]; exact mul_le_mul h1.1 h2.1 h0 (h0.trans h1.1)

/-- `B(a) ≤ 2 (sinh a + a)²`. -/
theorem poleB_le (a : ℝ) (ha : 1 / 64 ≤ a) : poleB a ≤ 2 * (Real.sinh a + a) ^ 2 := by
  rw [poleB_eq]
  have h1 := Fplus_bounds a ha
  have h2 := Fminus_bounds a ha
  have h0 : 0 ≤ Real.sinh (a - 1 / 64) + (a - 1 / 64) := by
    have := Real.sinh_nonneg_iff.mpr (by linarith : (0 : ℝ) ≤ a - 1 / 64); linarith
  have hp : 0 ≤ Fplus a := h0.trans h1.1
  have hm : 0 ≤ Fminus a := h0.trans h2.1
  have : Fplus a * Fminus a ≤ (Real.sinh a + a) ^ 2 := by
    rw [sq]; exact mul_le_mul h1.2 h2.2 hm (hp.trans h1.2)
  linarith

end GRHPseudo.Sharp
