import GRHPseudo.KernelSeparation.Triangle

/-!
# Piecewise-linear kernels: transform, mass, and the majorant bound (paper Lemma 16, Prop. 18)

`pwl h u₀ k u = ∑ⱼ kⱼ Λ((u − uⱼ)/h)` with `uⱼ = u₀ + j h`. Then

* `paperFT_pwl`:  `K̂(z) = h Λ̂(hz) e^{izu₀} P(e^{izh})`, `P(w) = ∑ kⱼ wʲ` (`evC k`);
* `integral_pwl_mul_exp`: `∫ K(u) e^{u/2} du = h (sinh(h/4)/(h/4))² e^{u₀/2} P(e^{h/2})`, i.e.
  `h (sinh(h/4)/(h/4))² ∑ⱼ kⱼ e^{uⱼ/2}` (the second identity of paper Lemma 16);
* `integral_norm_paperFT_pwl_le` (majorant bound): if `D |P(w)| ≤ |R(w)|²` on the unit circle, then
  `|K̂|` is integrable and `∫ |K̂| ≤ 2π ∑ rⱼ² / D`.

The first identity of Lemma 16 (`∫ |K̂| = ∫₀^{2π} |P|`, from `∑ₘ Λ̂(θ + 2πm) = 1`) is not formalized; the
majorant bound replaces it and needs only Fourier inversion for `Λ`.
-/

namespace GRHPseudo.KernelSeparation

open Complex MeasureTheory Real Set Filter
open Zeta23 (paperFT)

/-- `K(u) = ∑ⱼ kⱼ Λ((u − (u₀ + j h))/h)`. -/
noncomputable def pwl (h : ℝ) : ℝ → List ℤ → ℝ → ℝ
  | _, [], _ => 0
  | u₀, k :: ks, u => k * tri ((u - u₀) / h) + pwl h (u₀ + h) ks u

/-- Real evaluation `∑ⱼ kⱼ xʲ`. -/
def evR : List ℤ → ℝ → ℝ
  | [], _ => 0
  | a :: as, x => (a : ℝ) + x * evR as x

lemma evC_ofReal (k : List ℤ) (x : ℝ) : evC k (x : ℂ) = (evR k x : ℂ) := by
  induction k with
  | nil => simp [evR]
  | cons a as ih => simp [evR, ih]

lemma continuous_evC (k : List ℤ) : Continuous (evC k) := by
  induction k with
  | nil => exact continuous_const
  | cons a as ih => exact continuous_const.add (continuous_id.mul ih)

lemma continuous_pwl (h u₀ : ℝ) (k : List ℤ) : Continuous (pwl h u₀ k) := by
  induction k generalizing u₀ with
  | nil => exact continuous_const
  | cons a as ih =>
    exact (continuous_const.mul (continuous_tri.comp (by fun_prop))).add (ih _)

lemma pwl_nonneg (h u₀ : ℝ) (k : List ℤ) (hk : ∀ x ∈ k, 0 ≤ x) (u : ℝ) : 0 ≤ pwl h u₀ k u := by
  induction k generalizing u₀ with
  | nil => exact le_rfl
  | cons a as ih =>
    have ha : (0 : ℝ) ≤ a := by exact_mod_cast hk a (by simp)
    exact add_nonneg (mul_nonneg ha (tri_nonneg _)) (ih _ fun x hx => hk x (by simp [hx]))

lemma pwl_eq_zero {h : ℝ} (hh : 0 < h) (u₀ : ℝ) (k : List ℤ) {u : ℝ}
    (hu : u ≤ u₀ - h ∨ u₀ + k.length * h ≤ u) : pwl h u₀ k u = 0 := by
  induction k generalizing u₀ with
  | nil => rfl
  | cons a as ih =>
    simp only [List.length_cons, Nat.cast_add, Nat.cast_one] at hu
    have hlen : (0 : ℝ) ≤ as.length := Nat.cast_nonneg _
    rw [pwl, ih (u₀ + h), tri_eq_zero, mul_zero, add_zero]
    · rw [abs_div, abs_of_pos hh, le_div_iff₀ hh, one_mul]
      rcases hu with hu | hu
      · rw [abs_of_neg (by linarith)]; linarith
      · rw [abs_of_nonneg (by nlinarith)]; nlinarith
    · rcases hu with hu | hu
      · left; linarith
      · right; linarith

/-- The complexified kernel. -/
noncomputable def pwlC (h u₀ : ℝ) (k : List ℤ) (u : ℝ) : ℂ := (pwl h u₀ k u : ℂ)

lemma continuous_pwlC (h u₀ : ℝ) (k : List ℤ) : Continuous (pwlC h u₀ k) :=
  continuous_ofReal.comp (continuous_pwl h u₀ k)

lemma hasCompactSupport_pwlC {h : ℝ} (hh : 0 < h) (u₀ : ℝ) (k : List ℤ) :
    HasCompactSupport (pwlC h u₀ k) := by
  refine HasCompactSupport.intro (isCompact_Icc (a := u₀ - h) (b := u₀ + k.length * h)) fun u hu => ?_
  rw [mem_Icc, not_and_or, not_le, not_le] at hu
  simp only [pwlC, ofReal_eq_zero]
  exact pwl_eq_zero hh u₀ k (hu.imp le_of_lt le_of_lt)

lemma integrable_tri_comp_mul_cexp {h : ℝ} (hh : h ≠ 0) (a : ℝ) (z : ℂ) :
    Integrable fun u : ℝ => ((tri ((u - a) / h) : ℝ) : ℂ) * cexp (I * z * u) := by
  have hcs : HasCompactSupport fun u : ℝ => ((tri ((u - a) / h) : ℝ) : ℂ) := by
    have : (fun u : ℝ => ((tri ((u - a) / h) : ℝ) : ℂ)) = fun u => triC (h⁻¹ * u - h⁻¹ * a) := by
      ext u; simp only [triC]; congr 2; field_simp
    rw [this]
    exact (hasCompactSupport_triC.comp_homeomorph
      ((Homeomorph.mulLeft₀ h⁻¹ (inv_ne_zero hh)).trans (Homeomorph.subRight (h⁻¹ * a))))
  exact integrable_mul_cexp (continuous_ofReal.comp (continuous_tri.comp (by fun_prop))) hcs z

/-- Transform of one translated, dilated triangle: `h e^{iza} Λ̂(hz)`. -/
lemma paperFT_tri_comp {h : ℝ} (hh : 0 < h) (a : ℝ) (z : ℂ) :
    paperFT (fun u : ℝ => ((tri ((u - a) / h) : ℝ) : ℂ)) z
      = h * cexp (I * z * a) * paperFT triC (h * z) := by
  rw [Zeta23.paperFT_def]
  set G : ℝ → ℂ := fun s => triC s * cexp (I * z * (h * s + a))
  have h1 : (fun u : ℝ => ((tri ((u - a) / h) : ℝ) : ℂ) * cexp (I * z * u))
      = fun u => G ((u - a) / h) := by
    ext u; simp only [G, triC]; congr 3
    have : (h : ℂ) ≠ 0 := by exact_mod_cast hh.ne'
    push_cast; field_simp; ring
  rw [h1, integral_sub_right_eq_self (fun v => G (v / h)) a, Measure.integral_comp_div G h,
    abs_of_pos hh, Complex.real_smul, Zeta23.paperFT_def, ← Zeta23.integral_const_mul_C]
  rw [← Zeta23.integral_const_mul_C]
  congr 1 with s
  simp only [G]
  rw [show I * z * ((h : ℂ) * s + a) = I * z * a + I * (h * z) * s by ring, Complex.exp_add]
  ring

/-- **Transform of a piecewise-linear kernel**: `K̂(z) = h Λ̂(hz) e^{izu₀} P(e^{izh})`. -/
theorem paperFT_pwl {h : ℝ} (hh : 0 < h) (u₀ : ℝ) (k : List ℤ) (z : ℂ) :
    paperFT (pwlC h u₀ k) z
      = h * paperFT triC (h * z) * cexp (I * z * u₀) * evC k (cexp (I * z * h)) := by
  induction k generalizing u₀ with
  | nil => simp [pwlC, pwl, Zeta23.paperFT_def]
  | cons a as ih =>
    have hsplit : (fun u : ℝ => pwlC h u₀ (a :: as) u * cexp (I * z * u))
        = fun u => (a : ℂ) * (((tri ((u - u₀) / h) : ℝ) : ℂ) * cexp (I * z * u))
            + pwlC h (u₀ + h) as u * cexp (I * z * u) := by
      ext u; simp only [pwlC, pwl]; push_cast; ring
    have hi2 : Integrable fun u : ℝ => pwlC h (u₀ + h) as u * cexp (I * z * u) :=
      integrable_mul_cexp (continuous_pwlC _ _ _) (hasCompactSupport_pwlC hh _ _) z
    rw [Zeta23.paperFT_def, hsplit,
      integral_add ((integrable_tri_comp_mul_cexp hh.ne' u₀ z).const_mul _) hi2,
      Zeta23.integral_const_mul_C, ← Zeta23.paperFT_def, ← Zeta23.paperFT_def, ih,
      paperFT_tri_comp hh]
    simp only [evC_cons]
    push_cast
    rw [show I * z * ((u₀ : ℂ) + h) = I * z * u₀ + I * z * h by ring, Complex.exp_add]
    ring

/-- `(sinh(h/4)/(h/4))² = 4(e^{h/2} + e^{−h/2} − 2)/h²`. -/
lemma sinh_ratio_sq {h : ℝ} (hh : h ≠ 0) :
    (Real.sinh (h / 4) / (h / 4)) ^ 2 = 4 * (Real.exp (h / 2) + Real.exp (-(h / 2)) - 2) / h ^ 2 := by
  have e1 : Real.exp (h / 2) = Real.exp (h / 4) ^ 2 := by
    rw [← Real.exp_nat_mul]; congr 1; ring
  have e2 : Real.exp (-(h / 2)) = Real.exp (-(h / 4)) ^ 2 := by
    rw [← Real.exp_nat_mul]; congr 1; ring
  have e3 : Real.exp (h / 4) * Real.exp (-(h / 4)) = 1 := by
    rw [← Real.exp_add]; simp
  rw [Real.sinh_eq, e1, e2]
  field_simp
  nlinarith [e3]

/-- **Mass of a piecewise-linear kernel** (paper Lemma 16, second identity):
`∫ K(u) e^{u/2} du = h (sinh(h/4)/(h/4))² e^{u₀/2} P(e^{h/2})`, where
`e^{u₀/2} P(e^{h/2}) = ∑ⱼ kⱼ e^{uⱼ/2}`. -/
theorem integral_pwl_mul_exp {h : ℝ} (hh : 0 < h) (u₀ : ℝ) (k : List ℤ) :
    ∫ u : ℝ, pwl h u₀ k u * Real.exp (u / 2)
      = h * (Real.sinh (h / 4) / (h / 4)) ^ 2 * (Real.exp (u₀ / 2) * evR k (Real.exp (h / 2))) := by
  have hz : (h : ℂ) * (-I / 2) ≠ 0 := by
    have : (h : ℂ) ≠ 0 := by exact_mod_cast hh.ne'
    exact mul_ne_zero this (by simp [I_ne_zero])
  have hF := paperFT_pwl hh u₀ k (-I / 2)
  rw [paperFT_tri hz] at hF
  have hl : paperFT (pwlC h u₀ k) (-I / 2) = ((∫ u : ℝ, pwl h u₀ k u * Real.exp (u / 2) : ℝ) : ℂ) := by
    rw [Zeta23.paperFT_def,
      show ((∫ u : ℝ, pwl h u₀ k u * Real.exp (u / 2) : ℝ) : ℂ)
        = ∫ u : ℝ, ((pwl h u₀ k u * Real.exp (u / 2) : ℝ) : ℂ) from integral_ofReal.symm]
    congr 1 with u
    simp only [pwlC]
    push_cast
    congr 2
    rw [show I * (-I / 2) * (u : ℂ) = -(I * I) * u / 2 by ring, I_mul_I]; ring_nf
  rw [hl] at hF
  have hx : ∀ x : ℝ, cexp (I * (-I / 2) * x) = (Real.exp (x / 2) : ℂ) := by
    intro x; push_cast; congr 1; rw [show I * (-I / 2) * (x : ℂ) = -(I * I) * x / 2 by ring, I_mul_I]
    ring
  have hy : cexp (I * (h * (-I / 2))) = (Real.exp (h / 2) : ℂ) := by
    push_cast; congr 1; rw [show I * ((h : ℂ) * (-I / 2)) = -(I * I) * h / 2 by ring, I_mul_I]; ring
  have hy' : cexp (-(I * (h * (-I / 2)))) = (Real.exp (-(h / 2)) : ℂ) := by
    push_cast; congr 1; rw [show -(I * ((h : ℂ) * (-I / 2))) = (I * I) * h / 2 by ring, I_mul_I]; ring
  rw [hx, hx, hy, hy', evC_ofReal] at hF
  apply Complex.ofReal_injective
  rw [hF, sinh_ratio_sq hh.ne']
  have hh2 : (h : ℂ) ≠ 0 := by exact_mod_cast hh.ne'
  push_cast
  field_simp
  rw [I_sq]
  ring

/-! ### The majorant bound -/

lemma norm_cexp_I_ofReal (x : ℝ) : ‖cexp (I * x)‖ = 1 := by
  rw [mul_comm]; exact Complex.norm_exp_ofReal_mul_I x

lemma norm_cexp_I_mul_mul (a b : ℝ) : ‖cexp (I * a * b)‖ = 1 := by
  rw [mul_assoc, ← ofReal_mul]; exact norm_cexp_I_ofReal _

lemma integrable_triFT_mul {φ : ℝ → ℂ} (hφ : Continuous φ) {C : ℝ} (hC : ∀ τ, ‖φ τ‖ ≤ C) :
    Integrable fun τ : ℝ => (triFT τ : ℂ) * φ τ :=
  integrable_triFT.ofReal.mul_bdd hφ.aestronglyMeasurable (Eventually.of_forall hC)

lemma integral_triFT_pow_evC (cs : List ℤ) (m : ℕ) :
    ∫ τ : ℝ, (triFT τ : ℂ) * (cexp (I * τ) ^ m * evC cs (cexp (I * τ)))
      = 2 * π * (if m = 0 then (hd cs : ℂ) else 0) := by
  induction cs generalizing m with
  | nil => simp [hd]
  | cons c cs ih =>
    have hsplit : (fun τ : ℝ => (triFT τ : ℂ) * (cexp (I * τ) ^ m * evC (c :: cs) (cexp (I * τ))))
        = fun τ => (c : ℂ) * ((triFT τ : ℂ) * cexp (I * τ) ^ m)
            + (triFT τ : ℂ) * (cexp (I * τ) ^ (m + 1) * evC cs (cexp (I * τ))) := by
      ext τ; simp only [evC_cons]; ring
    have i1 : Integrable fun τ : ℝ => (triFT τ : ℂ) * cexp (I * τ) ^ m :=
      integrable_triFT_mul (C := 1) (by fun_prop) fun τ => by
        rw [norm_pow, norm_cexp_I_ofReal, one_pow]
    have i2 : Integrable fun τ : ℝ => (triFT τ : ℂ) * (cexp (I * τ) ^ (m + 1) * evC cs (cexp (I * τ))) :=
      integrable_triFT_mul (C := absSum cs)
        (by have := continuous_evC cs; fun_prop) fun τ => by
          rw [norm_mul, norm_pow, norm_cexp_I_ofReal, one_pow, one_mul]
          exact norm_evC_le cs (norm_cexp_I_ofReal τ).le
    rw [hsplit, integral_add (i1.const_mul _) i2, Zeta23.integral_const_mul_C,
      integral_triFT_mul_exp, ih]
    simp only [hd, Nat.add_one_ne_zero, ite_false, mul_zero, add_zero]
    split_ifs <;> ring

lemma integral_triFT : ∫ τ : ℝ, triFT τ = 2 * π := by
  have h := integral_triFT_mul_exp 0
  simp only [pow_zero, mul_one, ite_true] at h
  rw [integral_complex_ofReal] at h
  exact_mod_cast h

/-- `∫ Λ̂(τ) C(e^{iτ}) dτ = 2π c₀` for a cosine form `C = c₀ + 2 ∑ cₘ Re wᵐ`. -/
theorem integral_triFT_cosForm (cs : List ℤ) :
    ∫ τ : ℝ, triFT τ * cosForm cs (cexp (I * τ)) = 2 * π * hd cs := by
  have hi : Integrable fun τ : ℝ => (triFT τ : ℂ) * evC cs (cexp (I * τ)) :=
    integrable_triFT_mul (C := absSum cs) (by have := continuous_evC cs; fun_prop) fun τ =>
      norm_evC_le cs (norm_cexp_I_ofReal τ).le
  have hre : ∫ τ : ℝ, ((triFT τ : ℂ) * evC cs (cexp (I * τ))).re = 2 * π * hd cs := by
    have e : ∫ τ : ℝ, ((triFT τ : ℂ) * evC cs (cexp (I * τ))).re
        = (∫ τ : ℝ, (triFT τ : ℂ) * evC cs (cexp (I * τ))).re := integral_re hi
    rw [e]
    have := integral_triFT_pow_evC cs 0
    simp only [pow_zero, one_mul, ite_true] at this
    rw [this]; simp
  have hpt : (fun τ : ℝ => triFT τ * cosForm cs (cexp (I * τ)))
      = fun τ => 2 * ((triFT τ : ℂ) * evC cs (cexp (I * τ))).re - hd cs * triFT τ := by
    ext τ; simp only [cosForm, re_ofReal_mul]; ring
  have hire : Integrable fun τ : ℝ => ((triFT τ : ℂ) * evC cs (cexp (I * τ))).re := hi.re
  rw [hpt, integral_sub (hire.const_mul 2) (integrable_triFT.const_mul _), integral_const_mul,
    integral_const_mul, hre, integral_triFT]
  ring

/-- Pointwise form of the transform on the real line, `t ≠ 0`. -/
lemma norm_paperFT_pwl {h : ℝ} (hh : 0 < h) (u₀ : ℝ) (k : List ℤ) {t : ℝ} (ht : t ≠ 0) :
    ‖paperFT (pwlC h u₀ k) t‖ = h * triFT (h * t) * ‖evC k (cexp (I * (h * t : ℝ)))‖ := by
  rw [paperFT_pwl hh, show (h : ℂ) * (t : ℂ) = ((h * t : ℝ) : ℂ) by push_cast; ring,
    paperFT_tri_real (mul_ne_zero hh.ne' ht), norm_mul, norm_mul, norm_mul, norm_cexp_I_mul_mul,
    Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg hh.le,
    Real.norm_of_nonneg (triFT_nonneg _), mul_one]
  congr 3; push_cast; ring_nf

/-- **Majorant bound.** If `D |P(w)| ≤ |R(w)|²` on the unit circle (`P = evC k`, `R = evC r`), then
`|K̂|` is integrable and `∫ |K̂| ≤ 2π (∑ rⱼ²)/D`; here `hd (acf r) = ∑ rⱼ²`. -/
theorem integral_norm_paperFT_pwl_le {h : ℝ} (hh : 0 < h) (u₀ : ℝ) {k r : List ℤ} {D : ℤ}
    (hD : 0 < D) (hcert : ∀ w : ℂ, ‖w‖ = 1 → (D : ℝ) * ‖evC k w‖ ≤ ‖evC r w‖ ^ 2) :
    Integrable (fun t : ℝ => ‖paperFT (pwlC h u₀ k) t‖) ∧
      ∫ t : ℝ, ‖paperFT (pwlC h u₀ k) t‖ ≤ 2 * π * hd (acf r) / D := by
  have hDr : (0 : ℝ) < D := by exact_mod_cast hD
  set g : ℝ → ℝ := fun τ => triFT τ * ‖evC r (cexp (I * τ))‖ ^ 2 with hg
  have hgi : Integrable g := by
    refine integrable_triFT.mul_bdd (c := (absSum r : ℝ) ^ 2)
      (show Continuous (fun τ : ℝ => ‖evC r (cexp (I * τ))‖ ^ 2) by
        have := continuous_evC r; fun_prop).aestronglyMeasurable (Eventually.of_forall fun τ => ?_)
    rw [Real.norm_of_nonneg (by positivity)]
    gcongr; exact norm_evC_le r (norm_cexp_I_ofReal τ).le
  have hgint : ∫ τ, g τ = 2 * π * hd (acf r) := by
    rw [← integral_triFT_cosForm]
    congr 1 with τ
    simp only [hg]; rw [← normSq_evC r (norm_cexp_I_ofReal τ), normSq_eq_norm_sq]
  set B : ℝ → ℝ := fun t => h / D * g (h * t)
  have hBi : Integrable B := (hgi.comp_mul_left' hh.ne').const_mul _
  have hBint : ∫ t, B t = 2 * π * hd (acf r) / D := by
    simp only [B]
    rw [integral_const_mul, Measure.integral_comp_mul_left (fun τ => g τ) h, hgint, abs_inv,
      abs_of_pos hh, smul_eq_mul]
    field_simp
  set F : ℝ → ℝ := fun t => h * triFT (h * t) * ‖evC k (cexp (I * (h * t : ℝ)))‖
  have hne : ∀ᵐ t : ℝ ∂volume, t ≠ 0 := by simp [ae_iff]
  have hFae : (fun t : ℝ => ‖paperFT (pwlC h u₀ k) t‖) =ᵐ[volume] F := by
    filter_upwards [hne] with t ht using norm_paperFT_pwl hh u₀ k ht
  have hFB : ∀ t, F t ≤ B t := by
    intro t
    simp only [F, B, hg]
    have hc := hcert _ (norm_cexp_I_ofReal (h * t))
    have h0 := triFT_nonneg (h * t)
    rw [div_mul_eq_mul_div, le_div_iff₀ hDr]
    calc h * triFT (h * t) * ‖evC k (cexp (I * ↑(h * t)))‖ * D
        = h * triFT (h * t) * (D * ‖evC k (cexp (I * ↑(h * t)))‖) := by ring
      _ ≤ h * triFT (h * t) * ‖evC r (cexp (I * ↑(h * t)))‖ ^ 2 := by gcongr
      _ = _ := by ring
  have hFm : AEStronglyMeasurable F := by
    have := continuous_evC k
    exact ((measurable_triFT.comp (measurable_const_mul h)).const_mul h).aestronglyMeasurable.mul
      (by fun_prop : Continuous fun t : ℝ => ‖evC k (cexp (I * (h * t : ℝ)))‖).aestronglyMeasurable
  have hFi : Integrable F := by
    refine hBi.mono' hFm (Eventually.of_forall fun t => ?_)
    rw [Real.norm_of_nonneg (by simp only [F]; have := triFT_nonneg (h * t); positivity)]
    exact hFB t
  refine ⟨hFi.congr hFae.symm, ?_⟩
  rw [integral_congr_ae hFae, ← hBint]
  exact integral_mono hFi hBi hFB

end GRHPseudo.KernelSeparation
