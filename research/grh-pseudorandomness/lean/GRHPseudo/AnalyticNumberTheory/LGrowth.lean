import Mathlib

/-!
# Polynomial growth of nonprincipal Dirichlet L-functions in `Re s ≥ 1/2`

For `χ ≠ 1` modulo `N` and `Re s ≥ 1/2`: `‖L(s, χ)‖ ≤ 1 + 4 N ‖s‖` (`norm_LFunction_le_linear`).
Unconditional (partial summation plus the identity theorem).

Sections `Transform` and the character-mean lemmas are copied from
`grh/src/Lib/Analytic/PrimeNumberTheorem/LFunctionGrowth.lean` of github.com/lsernau/grh-lean
@ 72fead10 (Apache-2.0, readable edition, same Lean/Mathlib pin), namespace changed.
`norm_LFunction_le_linear` is that file's `norm_regularL_le_linear` specialised to `χ ≠ 1`, where
the regularised function is `χ.LFunction` itself; this removes the dependence on the readable
edition's `entireL` and its imports. See `ATTRIBUTION.md`.
-/

noncomputable section

open Complex Real Set Filter Topology MeasureTheory Metric Asymptotics DirichletCharacter
open scoped Classical

namespace GRHPseudo

section Transform

variable {r : ℝ → ℂ} {C : ℝ} {s : ℂ}

/-- If `|r| ≤ C` on `(1, ∞)`, then the integrand of `∫₁^∞ r(t) t ^ (-s - 1) dt` is dominated by
`C t ^ (-re s - 1)`. -/
lemma norm_mul_cpow_neg_add_one_le (h_bound : ∀ t : ℝ, 1 < t → ‖r t‖ ≤ C) {t : ℝ} (ht : 1 < t) :
    ‖r t * t ^ (-(s + 1))‖ ≤ C * t ^ (-(s.re + 1)) := by
  rw [norm_mul, norm_cpow_eq_rpow_re_of_pos (one_pos.trans ht), neg_re, add_re, one_re]
  exact mul_le_mul_of_nonneg_right (h_bound t ht) (by positivity)

/-- For a bounded measurable `r`, the integral `∫₁^∞ r(t) t ^ (-s - 1) dt` converges in
`re s > 0`. -/
lemma integrableOn_mul_cpow_of_bounded (hr : Measurable r) (h_bound : ∀ t : ℝ, 1 < t → ‖r t‖ ≤ C)
    (hs : 0 < s.re) : IntegrableOn (fun t : ℝ ↦ r t * t ^ (-(s + 1))) (Ioi 1) := by
  have h_exp : -(s.re + 1) < -1 := by linarith
  exact ((integrableOn_Ioi_rpow_of_lt h_exp one_pos).const_mul C).mono' (by fun_prop)
    (ae_restrict_of_forall_mem measurableSet_Ioi fun _ ↦ norm_mul_cpow_neg_add_one_le h_bound)

/-- If `|r| ≤ C` on `(1, ∞)`, then `|∫₁^∞ r(t) t ^ (-s - 1) dt| ≤ C / re s` for `re s > 0`. -/
lemma norm_integral_mul_cpow_le (h_bound : ∀ t : ℝ, 1 < t → ‖r t‖ ≤ C) (hs : 0 < s.re) :
    ‖∫ t : ℝ in Ioi (1 : ℝ), r t * t ^ (-(s + 1))‖ ≤ C / s.re := by
  have h_exp : -(s.re + 1) < -1 := by linarith
  calc
    _ ≤ ∫ t in Ioi (1 : ℝ), C * t ^ (-(s.re + 1)) :=
      norm_integral_le_of_norm_le ((integrableOn_Ioi_rpow_of_lt h_exp one_pos).const_mul C)
        (ae_restrict_of_forall_mem measurableSet_Ioi fun _ ↦ norm_mul_cpow_neg_add_one_le h_bound)
    _ = C / s.re := by
      rw [integral_const_mul, integral_Ioi_rpow_of_lt h_exp one_pos, Real.one_rpow, neg_add,
        neg_add_cancel_right, neg_div_neg_eq, mul_one_div]

/-- For a bounded measurable `r`, the integral `∫₁^∞ r(t) t ^ (-s - 1) dt` is holomorphic in
`re s > 0`. -/
lemma differentiableAt_integral_mul_cpow (hr : Measurable r)
    (h_bound : ∀ t : ℝ, 1 < t → ‖r t‖ ≤ C) (hs : 0 < s.re) :
    DifferentiableAt ℂ (fun z : ℂ ↦ ∫ t : ℝ in Ioi (1 : ℝ), r t * t ^ (-(z + 1))) s := by
  -- The integral is the Mellin transform at `-z` of `r` cut off below `1`. This function is
  -- bounded and vanishes near `0`, so its transform is holomorphic to the left of `0`.
  let f : ℝ → ℂ := (Ioi 1).indicator r
  have h_mellin (z : ℂ) : ∫ t in Ioi (1 : ℝ), r t * t ^ (-(z + 1)) = mellin f (-z) := by
    rw [mellin, ← inter_eq_right.2 (Ioi_subset_Ioi zero_le_one),
      ← setIntegral_indicator measurableSet_Ioi]
    simp [f, indicator, mul_comm, sub_eq_add_neg, add_comm]
  have f_bound (t : ℝ) : ‖f t‖ ≤ |C| := by
    by_cases ht : 1 < t <;> simp [f, ht, (h_bound t _).trans (le_abs_self C)]
  have f_loc : LocallyIntegrable f :=
    (locallyIntegrable_const |C|).mono (hr.indicator measurableSet_Ioi).aestronglyMeasurable
      (.of_forall fun t ↦ by simpa using f_bound t)
  have f_top : f =O[atTop] fun t : ℝ ↦ t ^ (-(0 : ℝ)) :=
    .of_bound |C| (.of_forall fun t ↦ by simpa using f_bound t)
  have f_bot : f =O[𝓝[>] 0] fun t : ℝ ↦ t ^ (-(-s.re - 1)) := by
    refine (isBigO_zero _ _).congr' ?_ .rfl
    filter_upwards [mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds one_pos)] with t (ht : t < 1)
    simp [f, ht.le]
  simp only [h_mellin]
  exact (mellin_differentiableAt_of_isBigO_rpow (f_loc.locallyIntegrableOn _) f_top
    (by simpa : (-s).re < 0) f_bot (by simp)).comp s differentiableAt_id.neg

end Transform

variable {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) {s : ℂ} {l : ℝ}

/-- The mean value of a Dirichlet character over the classes modulo `N`. -/
def charMean : ℂ := (∑ a : ZMod N, χ a) / N

/-- The mean value of a Dirichlet character has absolute value at most `1`. -/
lemma norm_charMean_le_one : ‖charMean χ‖ ≤ 1 := by
  have h_sum : ‖∑ a : ZMod N, χ a‖ ≤ N := by
    simpa using norm_sum_le_of_le Finset.univ fun a _ ↦ χ.norm_le_one a
  rw [charMean, norm_div, Complex.norm_natCast]
  exact div_le_one_of_le₀ h_sum N.cast_nonneg

/-- The mean value of a nonprincipal Dirichlet character is `0`. -/
lemma charMean_eq_zero (hχ : χ ≠ 1) : charMean χ = 0 := by
  rw [charMean, MulChar.sum_eq_zero_of_ne_one hχ, zero_div]

/-- A sum of `χ` over `N` consecutive integers is `N` times the mean value `charMean χ` of `χ`,
that is, the sum over all classes modulo `N`. -/
lemma sum_range_char_add (M : ℕ) :
    ∑ n ∈ Finset.range N, χ (M + n : ℕ) = N * charMean χ := by
  rw [charMean, mul_div_cancel₀ _ (NeZero.natCast_ne N ℂ),
    ← Equiv.sum_comp (Equiv.addLeft (M : ZMod N))]
  -- `n ↦ n mod N` is a bijection from `{0, …, N - 1}` to `ZMod N`.
  have val_natCast : ∀ n ∈ Finset.range N, (n : ZMod N).val = n :=
    fun n hn ↦ ZMod.val_natCast_of_lt (Finset.mem_range.1 hn)
  exact Finset.sum_nbij' (fun n ↦ (n : ZMod N)) ZMod.val (by simp) (by simp [ZMod.val_lt])
    val_natCast (fun a _ ↦ ZMod.natCast_zmod_val a) (by simp)

/-- The sum of the values of `χ` up to `x` differs from `x` times the mean value `charMean χ` by at
most `2 N`. -/
lemma norm_sum_char_sub_le {x : ℝ} (hx : 0 ≤ x) :
    ‖∑ n ∈ Finset.Icc 1 ⌊x⌋₊, χ n - charMean χ * x‖ ≤ 2 * N := by
  -- The sums `S M` of `χ` less its mean have period `N`, so fewer than `N` terms count.
  let S (M : ℕ) : ℂ := ∑ n ∈ Finset.range M, (χ (1 + n : ℕ) - charMean χ)
  have S_periodic : Function.Periodic S N := by
    intro M
    -- The `N` terms by which `S (M + N)` exceeds `S M` add up to `0`.
    simp only [S, Finset.sum_range_add, add_eq_left, ← add_assoc]
    rw [Finset.sum_sub_distrib, sum_range_char_add, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul, sub_self]
  have S_le (M : ℕ) : ‖S M‖ ≤ 2 * M := by
    have term_le (n : ℕ) : ‖χ (1 + n : ℕ) - charMean χ‖ ≤ 2 :=
      (norm_sub_le_of_le (χ.norm_le_one _) (norm_charMean_le_one χ)).trans_eq one_add_one_eq_two
    exact (norm_sum_le_of_le (Finset.range M) fun n _ ↦ term_le n).trans_eq (by simp [mul_comm])
  have h_mod : ((⌊x⌋₊ % N : ℕ) : ℝ) + 1 ≤ N := mod_cast Nat.mod_lt _ (NeZero.pos N)
  have h_split : ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, χ n - charMean χ * x =
      S ⌊x⌋₊ - charMean χ * (x - ⌊x⌋₊ : ℝ) := by
    rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
    simp [S, Finset.sum_sub_distrib]
    ring
  calc
    _ ≤ ‖S (⌊x⌋₊ % N)‖ + ‖charMean χ‖ * |x - ⌊x⌋₊| := by
      rw [h_split, S_periodic.map_mod_nat, ← Real.norm_eq_abs, ← norm_real, ← norm_mul]
      exact norm_sub_le _ _
    _ ≤ 2 * (⌊x⌋₊ % N : ℕ) + 1 * 1 := by
      gcongr
      exacts [S_le _, norm_charMean_le_one χ, Nat.abs_sub_floor_le hx]
    _ ≤ 2 * N := by linarith

omit [NeZero N] in
/-- If `re s ≥ 1 + 1 / A` with `A > 0`, then `|L(s, χ)| ≤ 1 + A`, since the Dirichlet series of
`χ` is dominated by `ζ(re s)`. -/
lemma norm_LSeries_char_le {A : ℝ} (hA : 0 < A) (hs : 1 + 1 / A ≤ s.re) :
    ‖LSeries (fun n : ℕ ↦ χ n) s‖ ≤ 1 + A := by
  have hs_one : 1 < s.re := by linarith [one_div_pos.2 hA]
  have h_summable : Summable fun n : ℕ ↦ 1 / (n : ℝ) ^ s.re :=
    Real.summable_one_div_nat_rpow.2 hs_one
  have term_le (n : ℕ) : ‖LSeries.term (χ ·) s n‖ ≤ 1 / (n : ℝ) ^ s.re := by
    rw [LSeries.norm_term_eq]
    split_ifs
    · positivity
    · exact div_le_div_of_nonneg_right (χ.norm_le_one _) (by positivity)
  -- `ζ(σ) - 1 / (σ - 1) = 1 - σ T` with `T ≥ 0`
  have zeta_le : ∑' n : ℕ, 1 / (n + 1 : ℝ) ^ s.re ≤ 1 + 1 / (s.re - 1) := by
    have h_nonneg : 0 ≤ s.re * ZetaAsymptotics.termTSum s.re :=
      mul_nonneg (by linarith) (tsum_nonneg fun n ↦ ZetaAsymptotics.term_nonneg _ _)
    linarith [ZetaAsymptotics.zeta_limit_aux1 hs_one]
  calc
    _ ≤ ∑' n : ℕ, 1 / (n : ℝ) ^ s.re := tsum_of_norm_bounded h_summable.hasSum term_le
    _ = ∑' n : ℕ, 1 / (n + 1 : ℝ) ^ s.re := by
      rw [h_summable.tsum_eq_zero_add]
      simp [Real.zero_rpow (one_pos.trans hs_one).ne']
    _ ≤ 1 + 1 / (s.re - 1) := zeta_le
    _ ≤ 1 + A := by linarith [(one_div_le hA (sub_pos.2 hs_one)).1 (by linarith)]


/-- Partial summation: `‖L(s, χ)‖ ≤ 1 + 4 N ‖s‖` in `re s ≥ 1/2`, for nonprincipal `χ` mod `N`. -/
lemma norm_LFunction_le_linear (hχ : χ ≠ 1) (hs : 1 / 2 ≤ s.re) :
    ‖χ.LFunction s‖ ≤ 1 + 4 * N * ‖s‖ := by
  let κ : ℂ := charMean χ
  have hκ : κ = 0 := charMean_eq_zero χ hχ
  let r (t : ℝ) : ℂ := ∑ n ∈ Finset.Icc 1 ⌊t⌋₊, χ n - κ * t
  let Φ (z : ℂ) : ℂ := ∫ t in Ioi (1 : ℝ), r t * t ^ (-(z + 1))
  have r_meas : Measurable r :=
    ((measurable_of_countable fun M : ℕ ↦ ∑ n ∈ Finset.Icc 1 M, χ n).comp
      Nat.measurable_floor).sub (by fun_prop)
  have r_le (t : ℝ) (ht : 1 < t) : ‖r t‖ ≤ 2 * N := norm_sum_char_sub_le χ (by linarith)
  have series_eq (z : ℂ) (hz : 1 < z.re) :
      LSeries (fun n : ℕ ↦ χ n) z = z * (Φ z + κ / (z - 1)) := by
    have h_exp : (-z).re < -1 := by simpa
    have h_sum : (fun M : ℕ ↦ ∑ n ∈ Finset.Icc 1 M, ‖χ n‖) =O[atTop]
        fun M : ℕ ↦ (M : ℝ) ^ (1 : ℝ) := by
      refine isBigO_of_le _ fun M ↦ ?_
      have sum_le : ∑ n ∈ Finset.Icc 1 M, ‖χ n‖ ≤ M := by
        simpa using (Finset.Icc 1 M).sum_le_card_nsmul _ 1 fun n _ ↦ χ.norm_le_one n
      simpa [abs_of_nonneg, Finset.sum_nonneg] using sum_le
    have h_main : κ / (z - 1) = ∫ t in Ioi (1 : ℝ), κ * t ^ (-z) := by
      rw [integral_const_mul, integral_Ioi_cpow_of_lt h_exp one_pos, ofReal_one, one_cpow,
        neg_add_eq_sub, ← neg_sub z, neg_div_neg_eq, mul_one_div]
    have h_int_r : IntegrableOn (fun t : ℝ ↦ r t * t ^ (-(z + 1))) (Ioi 1) :=
      integrableOn_mul_cpow_of_bounded r_meas r_le (by linarith)
    have h_int_main : IntegrableOn (fun t : ℝ ↦ κ * t ^ (-z)) (Ioi 1) :=
      (integrableOn_Ioi_cpow_of_lt h_exp one_pos).const_mul κ
    rw [LSeries_eq_mul_integral' _ zero_le_one hz h_sum, h_main,
      ← integral_add h_int_r h_int_main]
    congr 1
    refine setIntegral_congr_fun measurableSet_Ioi fun t (ht : 1 < t) ↦ ?_
    have ht_ne : (t : ℂ) ≠ 0 := ofReal_ne_zero.2 (one_pos.trans ht).ne'
    simp only [r, neg_add, cpow_add _ _ ht_ne, cpow_neg_one]
    field
  have far_right (z : ℂ) (hz : 1 < z.re) : χ.LFunction z = Φ z * z := by
    rw [χ.LFunction_eq_LSeries hz, series_eq z hz, hκ]
    ring
  have identity : EqOn χ.LFunction (fun z ↦ Φ z * z) {z : ℂ | 0 < z.re} := by
    have analytic {F : ℂ → ℂ} (hF : ∀ z : ℂ, 0 < z.re → DifferentiableAt ℂ F z) :
        AnalyticOnNhd ℂ F {z : ℂ | 0 < z.re} :=
      DifferentiableOn.analyticOnNhd (fun z hz ↦ (hF z hz).differentiableWithinAt) (isOpen_re_gt 0)
    have h_right : AnalyticOnNhd ℂ (fun z ↦ Φ z * z) {z : ℂ | 0 < z.re} :=
      analytic fun z hz ↦ (differentiableAt_integral_mul_cpow r_meas r_le hz).mul (by fun_prop)
    have h_near_two : χ.LFunction =ᶠ[𝓝 2] fun z ↦ Φ z * z :=
      eventually_of_mem ((isOpen_re_gt 1).mem_nhds (by simp)) far_right
    exact (analytic fun z _ ↦ (differentiable_LFunction hχ) z).eqOn_of_preconnected_of_eventuallyEq
      h_right (convex_halfSpace_re_gt 0).isPreconnected (by simp) h_near_two
  have hs_pos : 0 < s.re := by linarith
  calc
    ‖χ.LFunction s‖ ≤ 1 + ‖Φ s‖ * ‖s‖ := by
      rw [identity hs_pos, norm_mul]
      linarith
    _ ≤ 1 + 2 * N / s.re * ‖s‖ := by
      gcongr
      exact norm_integral_mul_cpow_le r_le hs_pos
    _ ≤ 1 + 2 * N / (1 / 2) * ‖s‖ := by gcongr
    _ = 1 + 4 * N * ‖s‖ := by ring

end GRHPseudo
