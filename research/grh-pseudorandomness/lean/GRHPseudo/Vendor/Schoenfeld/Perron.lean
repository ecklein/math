/- Vendored from github.com/AndrewVSutherland/schoenfeld-rh-lean @ 0e52d7b1,
   `SchoenfeldRH/Lemmas/p6/Perron.lean` (Apache-2.0). Only import paths changed. See ATTRIBUTION.md. -/
import Mathlib

/-!
# Helper lemmas for `SchoenfeldRH.Explicit.Kernel` (prover p6)

A Perron-type formula for the difference `1/(s+a) - 1/(s+b)` on a vertical line, obtained from
Mathlib's Mellin inversion theorem, and some elementary estimates.
-/

open Complex MeasureTheory Set

namespace SchoenfeldRH.Lemmas.p6

lemma norm_lb (z : ℂ) {m : ℝ} (hm1 : m ≤ 1) (hre : m ≤ z.re) :
    m / 2 * (1 + |z.im|) ≤ ‖z‖ := by
  have h1 : z.re ≤ ‖z‖ := Complex.re_le_norm z
  have h2 : |z.im| ≤ ‖z‖ := Complex.abs_im_le_norm z
  have h3 : 0 ≤ |z.im| := abs_nonneg _
  nlinarith

lemma integrable_rpow_shift (e r : ℝ) (hr : 1 < r) :
    Integrable (fun t : ℝ => (1 + |t + e|) ^ (-r)) := by
  have := (integrable_one_add_norm (E := ℝ) (μ := volume) (r := r)
    (by simpa using hr)).comp_add_right e
  simpa [Real.norm_eq_abs] using this

lemma integrable_rpow_sub (e r : ℝ) (hr : 1 < r) :
    Integrable (fun t : ℝ => (1 + |t - e|) ^ (-r)) := by
  have := (integrable_one_add_norm (E := ℝ) (μ := volume) (r := r)
    (by simpa using hr)).comp_sub_right e
  simpa [Real.norm_eq_abs] using this

lemma integral_rpow_sub (e r : ℝ) :
    ∫ t : ℝ, (1 + |t - e|) ^ (-r) = ∫ t : ℝ, (1 + |t|) ^ (-r) :=
  integral_sub_right_eq_self (μ := volume) (fun t : ℝ => (1 + |t|) ^ (-r)) e

lemma inv_sq_le (z : ℂ) {m : ℝ} (hm0 : 0 < m) (hm1 : m ≤ 1) (hre : m ≤ z.re) :
    ‖z‖⁻¹ ^ 2 ≤ (2 / m) ^ 2 * (1 + |z.im|) ^ (-(2:ℝ)) := by
  have hlb := norm_lb z hm1 hre
  have hp : 0 < m / 2 * (1 + |z.im|) := by positivity
  have e1 : (2 / m) ^ 2 * (1 + |z.im|) ^ (-(2:ℝ)) = ((m / 2 * (1 + |z.im|)) ^ 2)⁻¹ := by
    rw [Real.rpow_neg (by positivity), Real.rpow_two]
    field_simp
  rw [e1, inv_pow]
  exact inv_anti₀ (by positivity) (pow_le_pow_left₀ hp.le hlb 2)

lemma norm_sub_inv_le (u v : ℂ) (hu : u ≠ 0) (hv : v ≠ 0) :
    ‖1 / u - 1 / v‖ ≤ ‖v - u‖ * (‖u‖⁻¹ ^ 2 + ‖v‖⁻¹ ^ 2) := by
  have e : 1 / u - 1 / v = (v - u) * (u⁻¹ * v⁻¹) := by field_simp
  rw [e, norm_mul, norm_mul, norm_inv, norm_inv]
  gcongr
  nlinarith [sq_nonneg (‖u‖⁻¹ - ‖v‖⁻¹)]

lemma integrable_diff {σ : ℝ} {a b : ℂ} (ha : 0 < σ + a.re) (hb : 0 < σ + b.re) :
    Integrable fun t : ℝ => 1 / ((σ : ℂ) + t * I + a) - 1 / ((σ : ℂ) + t * I + b) := by
  set m := min (min (σ + a.re) (σ + b.re)) 1 with hm
  have hm0 : 0 < m := lt_min (lt_min ha hb) one_pos
  have hm1 : m ≤ 1 := min_le_right _ _
  have hma : m ≤ σ + a.re := (min_le_left _ _).trans (min_le_left _ _)
  have hmb : m ≤ σ + b.re := (min_le_left _ _).trans (min_le_right _ _)
  have hG : Integrable fun t : ℝ => ‖b - a‖ * ((2 / m) ^ 2 * (1 + |t + a.im|) ^ (-(2:ℝ)) +
      (2 / m) ^ 2 * (1 + |t + b.im|) ^ (-(2:ℝ))) :=
    (((integrable_rpow_shift a.im 2 one_lt_two).const_mul _).add
      ((integrable_rpow_shift b.im 2 one_lt_two).const_mul _)).const_mul _
  refine hG.mono' ?_ (Filter.Eventually.of_forall fun t => ?_)
  · exact (by fun_prop : Measurable fun t : ℝ =>
      1 / ((σ : ℂ) + t * I + a) - 1 / ((σ : ℂ) + t * I + b)).aestronglyMeasurable
  · have ra : ((σ : ℂ) + t * I + a).re = σ + a.re := by simp
    have rb : ((σ : ℂ) + t * I + b).re = σ + b.re := by simp
    have ia : ((σ : ℂ) + t * I + a).im = t + a.im := by simp
    have ib : ((σ : ℂ) + t * I + b).im = t + b.im := by simp
    have nza : ((σ : ℂ) + t * I + a) ≠ 0 := fun h => by
      have := congrArg Complex.re h; rw [ra] at this; simp at this; linarith
    have nzb : ((σ : ℂ) + t * I + b) ≠ 0 := fun h => by
      have := congrArg Complex.re h; rw [rb] at this; simp at this; linarith
    refine (norm_sub_inv_le _ _ nza nzb).trans ?_
    have e : ((σ : ℂ) + t * I + b) - ((σ : ℂ) + t * I + a) = b - a := by ring
    rw [e]
    gcongr
    · have := inv_sq_le _ hm0 hm1 (by rw [ra]; exact hma); rwa [ia] at this
    · have := inv_sq_le _ hm0 hm1 (by rw [rb]; exact hmb); rwa [ib] at this

lemma mellin_f_eq {a b s : ℂ} (ha : 0 < s.re + a.re) (hb : 0 < s.re + b.re) :
    HasMellin (fun t : ℝ => indicator (Ioc 0 1) (fun t : ℝ => (t : ℂ) ^ a) t -
      indicator (Ioc 0 1) (fun t : ℝ => (t : ℂ) ^ b) t) s (1 / (s + a) - 1 / (s + b)) := by
  have h1 := hasMellin_cpow_Ioc a ha
  have h2 := hasMellin_cpow_Ioc b hb
  have := hasMellin_sub h1.1 h2.1
  rw [h1.2, h2.2] at this
  exact this

lemma contAt_f {a b : ℂ} {u : ℝ} (hu : 0 < u) :
    ContinuousAt (fun t : ℝ => indicator (Ioc 0 1) (fun t : ℝ => (t : ℂ) ^ a) t -
      indicator (Ioc 0 1) (fun t : ℝ => (t : ℂ) ^ b) t) u := by
  have hm : 0 < min u 1 := lt_min hu one_pos
  have c1 : ContinuousAt (fun t : ℝ => (t : ℂ) ^ a - (t : ℂ) ^ b) (min u 1) :=
    (continuousAt_ofReal_cpow_const _ _ (Or.inr hm.ne')).sub
      (continuousAt_ofReal_cpow_const _ _ (Or.inr hm.ne'))
  have hg : ContinuousAt (fun t : ℝ => ((min t 1 : ℝ) : ℂ) ^ a - ((min t 1 : ℝ) : ℂ) ^ b) u :=
    c1.comp (f := fun t : ℝ => min t 1) (continuous_id.min continuous_const).continuousAt
  refine hg.congr ?_
  filter_upwards [Ioi_mem_nhds hu] with t ht
  rw [mem_Ioi] at ht
  simp only [indicator, mem_Ioc]
  by_cases h1 : t ≤ 1
  · simp [ht, h1]
  · have : min t 1 = 1 := min_eq_right (le_of_not_ge h1)
    simp [this, h1]

/-- Perron's formula for `1/(s+a) - 1/(s+b)` on the line `Re s = σ`, via Mellin inversion. -/
lemma perron_diff {σ : ℝ} {a b : ℂ} (ha : 0 < σ + a.re) (hb : 0 < σ + b.re) {x : ℝ}
    (hx : 0 < x) :
    (1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ, (x : ℂ) ^ ((σ : ℂ) + t * I) *
        (1 / ((σ : ℂ) + t * I + a) - 1 / ((σ : ℂ) + t * I + b))
      = if 1 ≤ x then (x : ℂ) ^ (-a) - (x : ℂ) ^ (-b) else 0 := by
  set f := (fun t : ℝ => indicator (Ioc 0 1) (fun t : ℝ => (t : ℂ) ^ a) t -
      indicator (Ioc 0 1) (fun t : ℝ => (t : ℂ) ^ b) t) with hf
  have hM : ∀ s : ℂ, s.re = σ → mellin f s = 1 / (s + a) - 1 / (s + b) := by
    intro s hs
    exact (mellin_f_eq (by rw [hs]; exact ha) (by rw [hs]; exact hb)).2
  have hconv : MellinConvergent f σ :=
    (mellin_f_eq (s := (σ : ℂ)) (by simpa using ha) (by simpa using hb)).1
  have hvert : VerticalIntegrable (mellin f) σ := by
    unfold VerticalIntegrable
    have : (fun y : ℝ => mellin f ((σ : ℂ) + y * I)) =
        fun y : ℝ => 1 / ((σ : ℂ) + y * I + a) - 1 / ((σ : ℂ) + y * I + b) := by
      funext y; exact hM _ (by simp)
    rw [this]; exact integrable_diff ha hb
  have hxi : 0 < x⁻¹ := inv_pos.mpr hx
  have harg : (x : ℂ).arg ≠ Real.pi := by
    rw [arg_ofReal_of_nonneg hx.le]; exact Real.pi_ne_zero.symm
  have key := mellinInv_mellin_eq σ f hxi hconv hvert (contAt_f hxi)
  rw [mellinInv] at key
  have hint : (fun y : ℝ => ((x⁻¹ : ℝ) : ℂ) ^ (-((σ : ℂ) + y * I)) • mellin f ((σ : ℂ) + y * I)) =
      fun t : ℝ => (x : ℂ) ^ ((σ : ℂ) + t * I) *
        (1 / ((σ : ℂ) + t * I + a) - 1 / ((σ : ℂ) + t * I + b)) := by
    funext y
    rw [hM _ (by simp), smul_eq_mul, ofReal_inv, inv_cpow _ _ harg, cpow_neg, inv_inv]
  rw [hint, Complex.real_smul] at key
  have e2 : (((1 / (2 * Real.pi)) : ℝ) : ℂ) = (1 / (2 * Real.pi) : ℂ) := by push_cast; ring
  rw [e2] at key
  rw [key, hf]
  simp only [indicator, mem_Ioc]
  by_cases h1 : 1 ≤ x
  · have : x⁻¹ ≤ 1 := inv_le_one_of_one_le₀ h1
    simp only [hxi, this, and_self, ite_true, h1]
    rw [ofReal_inv, inv_cpow _ _ harg, inv_cpow _ _ harg, cpow_neg, cpow_neg]
  · have : ¬ x⁻¹ ≤ 1 := by
      rw [not_le] at h1 ⊢; exact (one_lt_inv₀ hx).mpr h1
    simp [this, h1]

/-- `x ^ (-3/2) = (√x ^ 3)⁻¹`. -/
lemma rpow_neg_three_halves {x : ℝ} (hx : 0 ≤ x) : x ^ (-(3 / 2 : ℝ)) = (√x ^ 3)⁻¹ := by
  rw [Real.rpow_neg hx, Real.sqrt_eq_rpow, ← Real.rpow_mul_natCast hx]
  norm_num

/-- The key pointwise inequality behind the `L¹` bound. -/
lemma key_ineq {N A B M m : ℝ} (hm : 0 < m) (hA : m ≤ A) (hB : m ≤ B) (hN : 0 < N)
    (hM : 1 ≤ M) (hNle : N ≤ A + B + M) :
    1 / (N * A * B) ≤ (1 + 1 / √m) * √M *
      (N ^ (-(3 / 2 : ℝ)) * (A ^ (-(3 / 2 : ℝ)) + B ^ (-(3 / 2 : ℝ)))) := by
  have hA0 : 0 < A := hm.trans_le hA
  have hB0 : 0 < B := hm.trans_le hB
  rw [rpow_neg_three_halves hN.le, rpow_neg_three_halves hA0.le, rpow_neg_three_halves hB0.le]
  set n := √N with hn
  set p := √A with hp
  set q := √B with hq
  set r := √M with hr
  set s := √m with hs
  have hn0 : 0 < n := Real.sqrt_pos.mpr hN
  have hp0 : 0 < p := Real.sqrt_pos.mpr hA0
  have hq0 : 0 < q := Real.sqrt_pos.mpr hB0
  have hs0 : 0 < s := Real.sqrt_pos.mpr hm
  have hr1 : 1 ≤ r := by rw [hr]; exact Real.one_le_sqrt.mpr hM
  have hsp : s ≤ p := Real.sqrt_le_sqrt hA
  have hsq : s ≤ q := Real.sqrt_le_sqrt hB
  have eN : N = n ^ 2 := (Real.sq_sqrt hN.le).symm
  have eA : A = p ^ 2 := (Real.sq_sqrt hA0.le).symm
  have eB : B = q ^ 2 := (Real.sq_sqrt hB0.le).symm
  have eM : M = r ^ 2 := (Real.sq_sqrt (by linarith)).symm
  rw [eN, eA, eB, eM] at hNle
  rw [eN, eA, eB]
  have h1 : n ≤ p + q + r := by nlinarith
  have h2 : p ^ 2 * q + p * q ^ 2 ≤ p ^ 3 + q ^ 3 := by nlinarith [sq_nonneg (p - q)]
  have h3 : s * (p * q) ≤ p ^ 3 + q ^ 3 := by
    have : s * p ^ 2 ≤ p ^ 3 := by nlinarith
    have : s * q ^ 2 ≤ q ^ 3 := by nlinarith
    nlinarith [sq_nonneg (p - q)]
  have h4 : n * p * q ≤ (1 + 1 / s) * r * (p ^ 3 + q ^ 3) := by
    have e1 : n * p * q ≤ (p ^ 2 * q + p * q ^ 2) + r * (p * q) := by
      have := mul_le_mul_of_nonneg_right h1 (by positivity : 0 ≤ p * q); nlinarith
    have e2 : r * (p * q) ≤ r * ((p ^ 3 + q ^ 3) / s) := by
      apply mul_le_mul_of_nonneg_left _ (by linarith)
      rw [le_div_iff₀ hs0]; linarith
    have e3 : p ^ 3 + q ^ 3 ≤ r * (p ^ 3 + q ^ 3) := by
      nlinarith [pow_pos hp0 3, pow_pos hq0 3]
    have e4 : (1 + 1 / s) * r * (p ^ 3 + q ^ 3) = r * (p ^ 3 + q ^ 3) + r * ((p ^ 3 + q ^ 3) / s) := by
      ring
    rw [e4]; linarith
  have eL : 1 / (n ^ 2 * p ^ 2 * q ^ 2) = (n * p * q) / (n ^ 3 * p ^ 3 * q ^ 3) := by
    field_simp
  have eR : (1 + 1 / s) * r * ((n ^ 3)⁻¹ * ((p ^ 3)⁻¹ + (q ^ 3)⁻¹)) =
      ((1 + 1 / s) * r * (p ^ 3 + q ^ 3)) / (n ^ 3 * p ^ 3 * q ^ 3) := by
    field_simp
    ring
  rw [eL, eR]
  exact div_le_div_of_nonneg_right h4 (by positivity)

end SchoenfeldRH.Lemmas.p6
-- stamp: 2
