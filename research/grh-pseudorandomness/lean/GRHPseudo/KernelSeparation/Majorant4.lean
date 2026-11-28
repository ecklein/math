import GRHPseudo.KernelSeparation.Window4

/-!
# A positive-definite majorant for the window-4 kernel (paper Prop. 18, the instance)

With `c = acf rData` (`cₘ = ∑ⱼ rⱼ rⱼ₊ₘ`), `h = 1/20`, `D = 100`, and `F = ∑ₘ cₘ Λ(u/h − m)`, put

  `M(u) = (F(u) + F(−u) − c₀ Λ(u/h)) / D`,

the even piecewise-linear function with node values `M(mh) = c_{|m|}/D`, supported in `[−101/20, 101/20]`. Then
`M̂(t) = (h/D) Λ̂(ht) |R(e^{iht})|²` is real and nonnegative (so `M` is positive definite), and
`M̂(t) ≥ |K̂(t)|` for every real `t`, by the certificate. `M(0) = ∑ rⱼ²/D`, and `e · M(0) ≤ (9/8) ∫ K e^{u/2}`.
The general part of Prop. 18 (existence of majorants for any kernel, and the explicit-formula step) stays informal.
-/

namespace GRHPseudo.KernelSeparation

open Complex MeasureTheory Real Set Filter
open Zeta23 (paperFT)

/-! ### `Λ̂` on the whole real line -/

lemma paperFT_triC_zero : paperFT triC 0 = 1 := by
  rw [paperFT_triC_eq_interval]
  have hcont : Continuous fun u : ℝ => triC u * cexp (I * 0 * u) := continuous_triC.mul (by fun_prop)
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := 0)
      (hcont.intervalIntegrable _ _) (hcont.intervalIntegrable _ _)]
  have hL : ∫ u in (-1 : ℝ)..0, triC u * cexp (I * 0 * u) = ∫ u in (-1 : ℝ)..0, (1 + (u : ℂ)) := by
    refine intervalIntegral.integral_congr fun u hu => ?_
    rw [uIcc_of_le (by norm_num)] at hu
    simp only [triC, tri_of_nonpos hu.2 hu.1]; push_cast; simp
  have hR : ∫ u in (0 : ℝ)..1, triC u * cexp (I * 0 * u) = ∫ u in (0 : ℝ)..1, (1 - (u : ℂ)) := by
    refine intervalIntegral.integral_congr fun u hu => ?_
    rw [uIcc_of_le (by norm_num)] at hu
    simp only [triC, tri_of_nonneg hu.1 hu.2]; push_cast; simp
  have d1 : ∀ u : ℝ, HasDerivAt (fun u : ℝ => (u : ℂ) + (u : ℂ) ^ 2 / 2) (1 + (u : ℂ)) u := by
    intro u
    have := ((hasDerivAt_id (u : ℂ)).add ((hasDerivAt_id (u : ℂ)).pow 2 |>.div_const 2))
    convert this.comp_ofReal using 1
    · simp
    · simp only [id_eq, Nat.cast_ofNat]; ring
  have d2 : ∀ u : ℝ, HasDerivAt (fun u : ℝ => (u : ℂ) - (u : ℂ) ^ 2 / 2) (1 - (u : ℂ)) u := by
    intro u
    have := ((hasDerivAt_id (u : ℂ)).sub ((hasDerivAt_id (u : ℂ)).pow 2 |>.div_const 2))
    convert this.comp_ofReal using 1
    · simp
    · simp only [id_eq, Nat.cast_ofNat]; ring
  rw [hL, hR, intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => d1 u)
      ((by fun_prop : Continuous fun u : ℝ => 1 + (u : ℂ)).intervalIntegrable _ _),
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => d2 u)
      ((by fun_prop : Continuous fun u : ℝ => 1 - (u : ℂ)).intervalIntegrable _ _)]
  push_cast; ring

/-- `Λ̂` on the real line: `1` at `0`, `(2 − 2 cos τ)/τ²` elsewhere. -/
noncomputable def triHat (τ : ℝ) : ℝ := if τ = 0 then 1 else triFT τ

lemma paperFT_triC_ofReal (τ : ℝ) : paperFT triC τ = (triHat τ : ℂ) := by
  unfold triHat
  split_ifs with h
  · subst h; simpa using paperFT_triC_zero
  · exact paperFT_tri_real h

lemma triHat_nonneg (τ : ℝ) : 0 ≤ triHat τ := by
  unfold triHat; split_ifs; · norm_num
  · exact triFT_nonneg τ

lemma triHat_neg (τ : ℝ) : triHat (-τ) = triHat τ := by
  unfold triHat triFT; simp [Real.cos_neg]

/-! ### Reflection and conjugation -/

lemma paperFT_comp_neg (g : ℝ → ℂ) (z : ℂ) : paperFT (fun u => g (-u)) z = paperFT g (-z) := by
  rw [Zeta23.paperFT_def, Zeta23.paperFT_def,
    ← integral_neg_eq_self (fun u : ℝ => g u * cexp (I * -z * u))]
  congr 1 with u; push_cast; ring_nf

lemma evC_conj (k : List ℤ) (w : ℂ) : evC k ((starRingEnd ℂ) w) = (starRingEnd ℂ) (evC k w) := by
  induction k with
  | nil => simp
  | cons a as ih => simp [ih]

lemma conj_cexp_I_ofReal (x : ℝ) : (starRingEnd ℂ) (cexp (I * x)) = cexp (I * (-x : ℝ)) := by
  rw [← Complex.exp_conj]; congr 1; simp

/-! ### The majorant -/

/-- `F(u) = ∑ₘ cₘ Λ(u/h − m)` with `c = acf rData`, `h = 1/20`. -/
noncomputable def majF : ℝ → ℝ := pwl (1 / 20) 0 (acf rData)

/-- The even positive-definite majorant `M(u) = (F(u) + F(−u) − c₀ Λ(20u))/D`. -/
noncomputable def majorant4 (u : ℝ) : ℝ :=
  (majF u + majF (-u) - (hd (acf rData) : ℝ) * tri ((u - 0) / (1 / 20))) / dData

lemma acf_rData_length : (acf rData).length = 101 := by decide +kernel

lemma continuous_majorant4 : Continuous majorant4 := by
  unfold majorant4 majF
  have := continuous_pwl (1 / 20) 0 (acf rData)
  have := continuous_tri
  fun_prop

lemma tri_neg (s : ℝ) : tri (-s) = tri s := by unfold tri; rw [abs_neg]

lemma majorant4_even (u : ℝ) : majorant4 (-u) = majorant4 u := by
  unfold majorant4
  rw [neg_neg, show ((-u - 0) / (1 / 20) : ℝ) = -((u - 0) / (1 / 20)) by ring, tri_neg]; ring

lemma majF_eq_zero {u : ℝ} (hu : u ≤ -(1 / 20) ∨ 101 / 20 ≤ u) : majF u = 0 := by
  unfold majF
  refine pwl_eq_zero (by norm_num) _ _ ?_
  rw [acf_rData_length]; push_cast
  rcases hu with h | h
  · left; linarith
  · right; linarith

lemma majorant4_support {u : ℝ} (hu : majorant4 u ≠ 0) : u ∈ Icc (-(101 / 20) : ℝ) (101 / 20) := by
  by_contra h
  rw [mem_Icc, not_and_or, not_le, not_le] at h
  apply hu
  unfold majorant4
  have ht : tri ((u - 0) / (1 / 20)) = 0 := by
    apply tri_eq_zero
    rcases h with h | h
    · rw [abs_of_neg (by linarith)]; linarith
    · rw [abs_of_pos (by linarith)]; linarith
  rw [ht, majF_eq_zero, majF_eq_zero]
  · simp
  · rcases h with h | h
    · right; linarith
    · left; linarith
  · rcases h with h | h
    · left; linarith
    · right; linarith

lemma majorant4_zero : majorant4 0 = 131068564 / 100 := by
  unfold majorant4 majF
  have hF : pwl (1 / 20) 0 (acf rData) 0 = hd (acf rData) := by
    obtain ⟨c, cs, hc⟩ : ∃ c cs, acf rData = c :: cs := by
      cases h : acf rData with
      | nil => have := acf_rData_length; rw [h] at this; simp at this
      | cons c cs => exact ⟨c, cs, rfl⟩
    rw [hc, pwl, pwl_eq_zero (by norm_num) _ _ (Or.inl (by norm_num))]
    simp [hd, tri]
  rw [neg_zero, hF, hd_acf_rData]
  simp [tri, dData]

lemma hasCompactSupport_comp_neg {g : ℝ → ℂ} (hg : HasCompactSupport g) :
    HasCompactSupport fun u => g (-u) :=
  hg.comp_homeomorph (Homeomorph.neg ℝ)

/-- **The transform of the majorant**: `M̂(t) = (h/D) Λ̂(ht) |R(e^{iht})|²` for every real `t`. -/
theorem paperFT_majorant4 (t : ℝ) :
    paperFT (fun u => (majorant4 u : ℂ)) t
      = (((1 / 20) / dData * triHat ((1 / 20) * t) * ‖evC rData (cexp (I * ((1 / 20) * t : ℝ)))‖ ^ 2 : ℝ)
          : ℂ) := by
  set h : ℝ := 1 / 20 with hh_def
  have hh : (0 : ℝ) < h := by norm_num
  set c := acf rData with hc_def
  have i1 : Integrable fun u : ℝ => pwlC h 0 c u * cexp (I * t * u) :=
    integrable_mul_cexp (continuous_pwlC _ _ _) (hasCompactSupport_pwlC hh _ _) t
  have i2 : Integrable fun u : ℝ => pwlC h 0 c (-u) * cexp (I * t * u) :=
    integrable_mul_cexp ((continuous_pwlC _ _ _).comp continuous_neg)
      (hasCompactSupport_comp_neg (hasCompactSupport_pwlC hh _ _)) t
  have i3 := integrable_tri_comp_mul_cexp hh.ne' 0 (t : ℂ)
  have hsplit : (fun u : ℝ => (majorant4 u : ℂ) * cexp (I * t * u))
      = fun u => (dData : ℂ)⁻¹ * ((pwlC h 0 c u * cexp (I * t * u)
          + pwlC h 0 c (-u) * cexp (I * t * u))
          - (hd c : ℂ) * (((tri ((u - 0) / h)) : ℝ) : ℂ) * cexp (I * t * u)) := by
    ext u; simp only [majorant4, majF, pwlC, hh_def, hc_def]; push_cast; ring
  have e1 : paperFT (pwlC h 0 c) t = h * triHat (h * t) * evC c (cexp (I * (h * t : ℝ))) := by
    rw [paperFT_pwl hh, show (h : ℂ) * (t : ℂ) = ((h * t : ℝ) : ℂ) by push_cast; ring,
      paperFT_triC_ofReal]
    push_cast; simp only [mul_zero, Complex.exp_zero, mul_one]; congr 3; ring
  have e2 : paperFT (fun u => pwlC h 0 c (-u)) t
      = h * triHat (h * t) * (starRingEnd ℂ) (evC c (cexp (I * (h * t : ℝ)))) := by
    rw [paperFT_comp_neg, paperFT_pwl hh, show (h : ℂ) * -(t : ℂ) = ((-(h * t) : ℝ) : ℂ) by push_cast; ring,
      paperFT_triC_ofReal, triHat_neg, ← evC_conj, conj_cexp_I_ofReal]
    push_cast; simp only [mul_zero, Complex.exp_zero, mul_one]; congr 3; ring
  have e3 : paperFT (fun u : ℝ => (((tri ((u - 0) / h)) : ℝ) : ℂ)) t = h * triHat (h * t) := by
    rw [paperFT_tri_comp hh, show (h : ℂ) * (t : ℂ) = ((h * t : ℝ) : ℂ) by push_cast; ring,
      paperFT_triC_ofReal]
    simp
  have i12 : Integrable fun u : ℝ => pwlC h 0 c u * cexp (I * t * u)
      + pwlC h 0 c (-u) * cexp (I * t * u) := i1.add i2
  have i3' : Integrable fun u : ℝ => (hd c : ℂ) * (((tri ((u - 0) / h)) : ℝ) : ℂ) * cexp (I * t * u) := by
    simpa [mul_assoc] using i3.const_mul (hd c : ℂ)
  rw [Zeta23.paperFT_def, hsplit, Zeta23.integral_const_mul_C, integral_sub i12 i3',
    integral_add i1 i2, ← Zeta23.paperFT_def, ← Zeta23.paperFT_def (fun u => pwlC h 0 c (-u))]
  have e4 : ∫ u : ℝ, (hd c : ℂ) * (((tri ((u - 0) / h)) : ℝ) : ℂ) * cexp (I * t * u)
      = (hd c : ℂ) * paperFT (fun u : ℝ => (((tri ((u - 0) / h)) : ℝ) : ℂ)) t := by
    rw [Zeta23.paperFT_def, ← Zeta23.integral_const_mul_C]; congr 1 with u; ring
  rw [e4, e1, e2, e3]
  have hw := norm_cexp_I_ofReal (h * t)
  have hn := normSq_evC rData hw
  rw [normSq_eq_norm_sq] at hn
  set X := evC c (cexp (I * (h * t : ℝ)))
  have hX : X + (starRingEnd ℂ) X = ((2 * X.re : ℝ) : ℂ) := by
    rw [Complex.add_conj]
  have hcos : (‖evC rData (cexp (I * (h * t : ℝ)))‖ ^ 2 : ℝ) = 2 * X.re - hd c := by
    rw [hn]; rfl
  rw [hcos]
  push_cast
  rw [show (h : ℂ) * triHat (h * t) * X + h * triHat (h * t) * (starRingEnd ℂ) X
      = h * triHat (h * t) * (X + (starRingEnd ℂ) X) by ring, hX]
  push_cast
  ring

/-- **Paper Prop. 18, the instance (formal).** An even, continuous, compactly supported `M` with
`M̂(t)` real, `M̂(t) ≥ 0` (positive definite) and `M̂(t) ≥ |K̂(t)|` for every real `t`, and
`e^{T/2} M(0) ≤ (9/8) ∫ K e^{u/2}` (`T = 2`), for the window-4 kernel `kernel4`. -/
theorem kernel4_majorant :
    ∃ M : ℝ → ℝ, Continuous M ∧ (∀ u, M (-u) = M u) ∧
      (∀ u, M u ≠ 0 → u ∈ Icc (-(101 / 20) : ℝ) (101 / 20)) ∧ M 0 = 131068564 / 100 ∧
      (∀ t : ℝ, ∃ m : ℝ, paperFT (fun u => (M u : ℂ)) t = m ∧ 0 ≤ m ∧
        ‖paperFT (fun u => (kernel4 u : ℂ)) t‖ ≤ m) ∧
      Real.exp (2 / 2) * M 0 ≤ 9 / 8 * ∫ u : ℝ, kernel4 u * Real.exp (u / 2) := by
  refine ⟨majorant4, continuous_majorant4, majorant4_even, fun u => majorant4_support,
    majorant4_zero, fun t => ⟨_, paperFT_majorant4 t, ?_, ?_⟩, ?_⟩
  · have := triHat_nonneg ((1 / 20) * t); simp only [dData]; positivity
  · set s : ℝ := (1 / 20) * t with hs
    have hw := norm_cexp_I_ofReal s
    set w := cexp (I * (s : ℂ)) with hw_def
    have hcert := certOK_sound (by decide) certOK_data hw
    have hK : ‖paperFT (fun u => (kernel4 u : ℂ)) t‖ = (1 / 20) * triHat s * ‖evC kData w‖ := by
      have : (fun u => (kernel4 u : ℂ)) = pwlC (1 / 20) (-39 / 20) kData := rfl
      rw [this, paperFT_pwl (by norm_num),
        show ((1 / 20 : ℝ) : ℂ) * (t : ℂ) = (s : ℂ) by rw [hs]; push_cast; ring, paperFT_triC_ofReal,
        norm_mul, norm_mul, norm_mul, norm_cexp_I_mul_mul, Complex.norm_real, Complex.norm_real,
        Real.norm_of_nonneg (by norm_num), Real.norm_of_nonneg (triHat_nonneg _), mul_one]
      congr 3; rw [hw_def, hs]; push_cast; ring_nf
    rw [hK]
    have h0 := triHat_nonneg s
    have hD : ((dData : ℤ) : ℝ) = 100 := by simp [dData]
    rw [hD] at hcert ⊢
    calc (1 / 20) * triHat s * ‖evC kData w‖ = (1 / 20) / 100 * triHat s * (100 * ‖evC kData w‖) := by
          ring
      _ ≤ (1 / 20) / 100 * triHat s * ‖evC rData w‖ ^ 2 := by gcongr
  · rw [majorant4_zero]; exact exp_mul_q0_le_mass

end GRHPseudo.KernelSeparation
