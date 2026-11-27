/- Vendored from github.com/AndrewVSutherland/schoenfeld-rh-lean @ 0e52d7b1,
   `SchoenfeldRH/Explicit/Weighted.lean` (Apache-2.0). Only import paths changed. See ATTRIBUTION.md. -/
import GRHPseudo.Vendor.Schoenfeld.Kernel

/-!
# Perron's formula with the weight `1 - (n/N)^μ` for a Dirichlet series

-/

open Complex MeasureTheory Set Filter

namespace SchoenfeldRH.Explicit

noncomputable def Kmu (c μ y t : ℝ) : ℂ :=
  (y : ℂ) ^ ((c : ℂ) + t * I) * (1 / ((c : ℂ) + t * I) - 1 / ((c : ℂ) + t * I + μ))

lemma norm_Kmu {c μ y : ℝ} (hy : 0 < y) (t : ℝ) :
    ‖Kmu c μ y t‖ = y ^ c * ‖1 / ((c : ℂ) + t * I) - 1 / ((c : ℂ) + t * I + μ)‖ := by
  rw [Kmu, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hy]
  simp

lemma integrable_Kmu {c μ : ℝ} (hc : 0 < c) (hμ : 1 < c + μ) {y : ℝ} (hy : 0 < y) :
    Integrable (Kmu c μ y) := by
  have hcont : Continuous fun t : ℝ => (y : ℂ) ^ ((c : ℂ) + t * I) :=
    Continuous.const_cpow (by fun_prop) (Or.inl (by exact_mod_cast hy.ne'))
  refine (integrable_kappa hc hμ).bdd_mul (c := y ^ c) hcont.aestronglyMeasurable ?_
  refine Filter.Eventually.of_forall fun t => ?_
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hy]
  simp

lemma integral_Kmu (y c μ : ℝ) (hy : 0 < y) (hc : 0 < c) (hμ : 1 < c + μ) :
    ∫ t : ℝ, Kmu c μ y t = 2 * Real.pi * (if 1 ≤ y then ((1 - y ^ (-μ) : ℝ) : ℂ) else 0) := by
  have h := perron_kernel y c μ hy hc hμ
  rw [← h]
  have hpi : (2 * Real.pi : ℂ) ≠ 0 := by
    have : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_pos.ne'
    exact mul_ne_zero two_ne_zero this
  rw [← mul_assoc, mul_one_div_cancel hpi, one_mul]
  rfl

lemma cpow_split {N n : ℕ} (hn : n ≠ 0) (s : ℂ) :
    (N : ℂ) ^ s = ((((N : ℝ) / (n : ℝ) : ℝ)) : ℂ) ^ s * (n : ℂ) ^ s := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  rw [← Complex.ofReal_natCast n, ← Complex.mul_cpow_ofReal_nonneg (by positivity) (by positivity)]
  congr 1
  rw [← Complex.ofReal_mul, div_mul_cancel₀ _ hn']
  simp

theorem perron_weighted_mu (a : ℕ → ℂ) (c μ : ℝ) (hc : 0 < c) (hμ : 1 < c + μ)
    (ha : Summable fun n : ℕ => ‖a n‖ / (n : ℝ) ^ c) (N : ℕ) (hN : 1 ≤ N) :
    ∑ n ∈ Finset.Ioo 0 N, a n * ((1 - ((n : ℝ) / N) ^ μ : ℝ) : ℂ)
      = (1 / (2 * Real.pi)) * ∫ t : ℝ, LSeries a ((c : ℂ) + t * I) * ((N : ℂ) ^ ((c : ℂ) + t * I)
          * (1 / ((c : ℂ) + t * I) - 1 / ((c : ℂ) + t * I + μ))) := by
  set F : ℕ → ℝ → ℂ := fun n t => if n = 0 then 0 else a n * Kmu c μ ((N : ℝ) / n) t with hF
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hpos : ∀ n : ℕ, n ≠ 0 → (0 : ℝ) < (N : ℝ) / n := fun n hn =>
    div_pos hNpos (by exact_mod_cast Nat.pos_of_ne_zero hn)
  -- pointwise identity
  have hpt : ∀ t : ℝ, LSeries a ((c : ℂ) + t * I) * ((N : ℂ) ^ ((c : ℂ) + t * I)
          * (1 / ((c : ℂ) + t * I) - 1 / ((c : ℂ) + t * I + μ))) = ∑' n, F n t := by
    intro t
    rw [LSeries, ← tsum_mul_right]
    congr 1
    funext n
    rcases eq_or_ne n 0 with rfl | hn
    · simp [hF]
    · simp only [hF, ite_eq_right hn, LSeries.term_of_ne_zero hn, Kmu]
      have hns : (n : ℂ) ^ ((c : ℂ) + t * I) ≠ 0 := by
        rw [Ne, Complex.cpow_eq_zero_iff]
        exact fun h => hn (by exact_mod_cast h.1)
      rw [cpow_split (N := N) hn, div_mul_eq_mul_div, div_eq_iff hns]
      ring
  have hint : ∀ n, Integrable (F n) := by
    intro n
    rcases eq_or_ne n 0 with rfl | hn
    · simp [hF]
    · simp only [hF, ite_eq_right hn]
      exact (integrable_Kmu hc hμ (hpos n hn)).const_mul _
  set Ik : ℝ := ∫ t : ℝ, ‖1 / ((c : ℂ) + t * I) - 1 / ((c : ℂ) + t * I + μ)‖ with hIk
  have hnorm : ∀ n, ∫ t, ‖F n t‖ = ‖a n‖ / (n : ℝ) ^ c * ((N : ℝ) ^ c * Ik) := by
    intro n
    rcases eq_or_ne n 0 with rfl | hn
    · simp [hF, Real.zero_rpow hc.ne']
    · simp only [hF, ite_eq_right hn, norm_mul, norm_Kmu (hpos n hn)]
      rw [hIk, ← integral_const_mul, ← integral_const_mul]
      congr 1
      funext t
      rw [Real.div_rpow hNpos.le (Nat.cast_nonneg n)]
      ring
  have hsum : Summable fun n => ∫ t, ‖F n t‖ := by
    simp only [hnorm]
    exact ha.mul_right _
  have hkey : ∀ n, (1 / (2 * Real.pi) : ℂ) * ∫ t, F n t
      = if n ∈ Finset.Ioo 0 N then a n * ((1 - ((n : ℝ) / N) ^ μ : ℝ) : ℂ) else 0 := by
    intro n
    rcases eq_or_ne n 0 with rfl | hn
    · simp [hF]
    have hpi : (2 * Real.pi : ℂ) ≠ 0 := by
      have : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_pos.ne'
      exact mul_ne_zero two_ne_zero this
    simp only [hF, ite_eq_right hn]
    rw [integral_const_mul, integral_Kmu _ _ _ (hpos n hn) hc hμ]
    have hn0 : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
    rcases lt_trichotomy n N with h | h | h
    · have hmem : n ∈ Finset.Ioo 0 N := Finset.mem_Ioo.mpr ⟨Nat.pos_of_ne_zero hn, h⟩
      have h1 : 1 ≤ (N : ℝ) / n := by
        rw [le_div_iff₀ hn0, one_mul]; exact_mod_cast (by omega : n ≤ N)
      rw [ite_eq_left h1, ite_eq_left hmem]
      have h2 : ((N : ℝ) / n) ^ (-μ) = ((n : ℝ) / N) ^ μ := by
        rw [Real.rpow_neg (hpos n hn).le, ← Real.inv_rpow (hpos n hn).le, inv_div]
      rw [h2]
      field_simp
    · subst h
      have hmem : n ∉ Finset.Ioo 0 n := by simp
      rw [ite_eq_right hmem, div_self hn0.ne', ite_eq_left le_rfl]
      simp
    · have hmem : n ∉ Finset.Ioo 0 N := by simp; omega
      have h1 : ¬ 1 ≤ (N : ℝ) / n := by
        rw [le_div_iff₀ hn0, one_mul, not_le]; exact_mod_cast h
      rw [ite_eq_right h1, ite_eq_right hmem]
      simp
  rw [funext hpt, ← integral_tsum_of_summable_integral_norm hint hsum, ← tsum_mul_left]
  simp only [hkey]
  rw [tsum_eq_sum (s := Finset.Ioo 0 N)]
  · exact Finset.sum_congr rfl fun n hn => (ite_eq_left hn).symm
  · intro n hn
    exact ite_eq_right hn

end SchoenfeldRH.Explicit
-- stamp: 5
