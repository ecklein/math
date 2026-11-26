import Mathlib.Analysis.Complex.BorelCaratheodory
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.Complex.Liouville

/-!
# Borel–Carathéodory bounds for logarithmic derivatives

The two lemmas below are copied verbatim (apart from the namespace and imports) from
`RHPrimeError/LogDeriv.lean` of the rh-prime-error project (Apache-2.0), which targets the same
Lean v4.35.0 / Mathlib `56a00585`. They use only Mathlib's `Complex.borelCaratheodory` and
`DifferentiableOn.isExactOn_ball`. See `ATTRIBUTION.md`.
-/

open Complex

namespace GRHPseudo.Vendored

open Metric Set
/-- The Borel–Carathéodory theorem on a disc centred at `c`, for a function vanishing at `c`. -/
lemma borelCaratheodory_closedBall {f : ℂ → ℂ} {c : ℂ} {M R r : ℝ} (hM : 0 < M)
    (hf : DifferentiableOn ℂ f (ball c R)) (hfc : f c = 0)
    (hre : ∀ z ∈ ball c R, (f z).re ≤ M)
    (hr : 0 ≤ r) (hrR : r < R) {z : ℂ} (hz : z ∈ closedBall c r) :
    ‖f z‖ ≤ 2 * M * r / (R - r) := by
  have hR : 0 < R := hr.trans_lt hrR
  have hmaps : Set.MapsTo (fun w : ℂ ↦ w + c) (ball 0 R) (ball c R) := by
    intro w hw
    simpa [dist_eq_norm] using hw
  have hF : DifferentiableOn ℂ (fun w : ℂ ↦ f (w + c)) (ball 0 R) :=
    hf.comp (by fun_prop) hmaps
  have hx : ‖z - c‖ ≤ r := by simpa [dist_eq_norm] using hz
  have hzc : z - c ∈ ball (0 : ℂ) R := by
    simpa using hx.trans_lt hrR
  have key := Complex.borelCaratheodory (f := fun w : ℂ ↦ f (w + c)) hM hF
    (fun w hw ↦ hre _ (hmaps hw)) hR hzc
  simp only [sub_add_cancel, zero_add, hfc, norm_zero, zero_mul, zero_div, add_zero] at key
  refine key.trans ?_
  have hd : 0 < R - r := by linarith
  have hx0 : 0 ≤ ‖z - c‖ := norm_nonneg _
  gcongr

open Metric Set in
/-- If `f` is holomorphic and zero-free on `ball c r₂` and bounded by `B` there, then on the
smaller closed disc `closedBall c r₁` its logarithmic derivative is bounded by
`8 * r₂ / (r₂ - r₁) ^ 2 * log (B / ‖f c‖)`. -/
theorem norm_deriv_div_le_of_forall_mem_ball_ne_zero {f : ℂ → ℂ} {c : ℂ} {r₁ r₂ B : ℝ}
    (hr₁ : 0 < r₁) (h12 : r₁ < r₂) (hf : DifferentiableOn ℂ f (ball c r₂))
    (hne : ∀ z ∈ ball c r₂, f z ≠ 0) (hB : ∀ z ∈ ball c r₂, ‖f z‖ ≤ B) {z : ℂ}
    (hz : z ∈ closedBall c r₁) :
    ‖deriv f z / f z‖ ≤ 8 * r₂ / (r₂ - r₁) ^ 2 * Real.log (B / ‖f c‖) := by
  have hr₂ : 0 < r₂ := hr₁.trans h12
  have hcB : c ∈ ball c r₂ := mem_ball_self hr₂
  have hfc : 0 < ‖f c‖ := norm_pos_iff.2 (hne c hcB)
  have hBpos : 0 < B := hfc.trans_le (hB c hcB)
  have hE : 0 ≤ Real.log (B / ‖f c‖) :=
    Real.log_nonneg ((one_le_div hfc).2 (hB c hcB))
  set d : ℝ := (r₂ - r₁) / 2 with hd
  have hd0 : 0 < d := by rw [hd]; linarith
  have hfd : DifferentiableOn ℂ (fun s ↦ deriv f s / f s) (ball c r₂) :=
    (hf.deriv isOpen_ball).div hf hne
  obtain ⟨g, hgc, hgd⟩ := hfd.isExactOn_ball.with_val_at c (Complex.log (f c))
  -- `f * exp (-g)` is constant
  have hFd : ∀ s ∈ ball c r₂, HasDerivAt (fun s ↦ f s * Complex.exp (-g s)) 0 s := by
    intro s hs
    have h1 := (hf.differentiableAt (isOpen_ball.mem_nhds hs)).hasDerivAt
    have h2 : HasDerivAt (fun x ↦ Complex.exp (-g x))
        (Complex.exp (-g s) * -(deriv f s / f s)) s := (hgd s hs).neg.cexp
    have h3 := h1.mul h2
    have h0 := hne s hs
    refine h3.congr_deriv ?_
    have e : f s * (Complex.exp (-g s) * -(deriv f s / f s))
        = -(deriv f s * Complex.exp (-g s)) := by
      field_simp
    rw [e]; ring
  have hexp : ∀ s ∈ ball c r₂, Complex.exp (g s) = f s := by
    intro s hs
    have hconst := isOpen_ball.is_const_of_deriv_eq_zero (convex_ball c r₂).isPreconnected
      (fun x hx ↦ (hFd x hx).differentiableAt.differentiableWithinAt)
      (fun x hx ↦ (hFd x hx).deriv) hs hcB
    have hc1 : f c * Complex.exp (-g c) = 1 := by
      rw [hgc, Complex.exp_neg, Complex.exp_log (hne c hcB), mul_inv_cancel₀ (hne c hcB)]
    rw [hc1] at hconst
    have : f s * Complex.exp (-g s) * Complex.exp (g s) = Complex.exp (g s) := by
      rw [hconst, one_mul]
    rw [← this, mul_assoc, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, mul_one]
  have hgre : ∀ s ∈ ball c r₂, (g s).re = Real.log ‖f s‖ := by
    intro s hs
    rw [← hexp s hs, Complex.norm_exp, Real.log_exp]
  have hgdiff : DifferentiableOn ℂ g (ball c r₂) := fun s hs ↦
    (hgd s hs).differentiableAt.differentiableWithinAt
  set h : ℂ → ℂ := fun s ↦ g s - g c with hh
  have hhdiff : DifferentiableOn ℂ h (ball c r₂) := hgdiff.sub_const _
  have hhc : h c = 0 := by simp [hh]
  have hzc : dist z c ≤ r₁ := mem_closedBall.1 hz
  have hzB : z ∈ ball c r₂ := mem_ball.2 (hzc.trans_lt h12)
  have hderiv : deriv h z = deriv f z / f z := ((hgd z hzB).sub_const (g c)).deriv
  have hsub : closedBall z d ⊆ closedBall c (r₁ + d) := by
    intro w hw
    rw [mem_closedBall] at hw ⊢
    linarith [dist_triangle w z c]
  have hsub' : closedBall c (r₁ + d) ⊆ ball c r₂ := closedBall_subset_ball (by rw [hd]; linarith)
  -- bound for every `M` larger than `log (B / ‖f c‖)`
  have key : ∀ M : ℝ, Real.log (B / ‖f c‖) < M →
      ‖deriv f z / f z‖ ≤ 8 * r₂ / (r₂ - r₁) ^ 2 * M := by
    intro M hM
    have hMpos : 0 < M := hE.trans_lt hM
    have hre : ∀ s ∈ ball c r₂, (h s).re ≤ M := by
      intro s hs
      have hfs : 0 < ‖f s‖ := norm_pos_iff.2 (hne s hs)
      simp only [hh, sub_re]
      rw [hgre s hs, hgre c hcB, ← Real.log_div hfs.ne' hfc.ne']
      refine (Real.log_le_log (div_pos hfs hfc) ?_).trans hM.le
      gcongr
      exact hB s hs
    have hbc : ∀ w ∈ closedBall c (r₁ + d), ‖h w‖ ≤ 2 * M * (r₁ + d) / d := by
      intro w hw
      have := borelCaratheodory_closedBall hMpos hhdiff hhc hre
        (by positivity : (0 : ℝ) ≤ r₁ + d) (by rw [hd]; linarith) hw
      have e : r₂ - (r₁ + d) = d := by rw [hd]; ring
      rwa [e] at this
    have hcauchy := norm_deriv_le_of_forall_mem_sphere_norm_le hd0
      (hhdiff.diffContOnCl_ball (hsub.trans hsub'))
      (fun w hw ↦ hbc w (hsub (sphere_subset_closedBall hw)))
    rw [hderiv] at hcauchy
    refine hcauchy.trans ?_
    have e : 2 * M * (r₁ + d) / d / d = 8 * (r₁ + d) / (r₂ - r₁) ^ 2 * M := by
      rw [hd]; field_simp; ring
    rw [e]
    have : 0 < (r₂ - r₁) ^ 2 := by nlinarith
    gcongr
    rw [hd]; linarith
  have hK : 0 < 8 * r₂ / (r₂ - r₁) ^ 2 := by
    have : 0 < (r₂ - r₁) ^ 2 := by nlinarith
    positivity
  refine le_of_forall_pos_le_add fun ε hε ↦ ?_
  have := key (Real.log (B / ‖f c‖) + ε / (8 * r₂ / (r₂ - r₁) ^ 2))
    (lt_add_of_pos_right _ (div_pos hε hK))
  rwa [mul_add, mul_div_cancel₀ _ hK.ne'] at this


end GRHPseudo.Vendored
