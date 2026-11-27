import GRHPseudo.AnalyticNumberTheory.Sharp.FiniteSums

/-!
# Positivity with a positive-definite majorant (convolution squares)

The positivity step of `TwoSided` and `MainTerm` only uses `‖k̂(γ)‖` on real `γ`. So it applies to
any kernel `K` whose transform has the same modulus as that of `M = f ⋆ f̃`, i.e.
`‖K̂(r)‖ = ‖f̂(r)‖²` for real `r`. The main example is the convolution square
`K = f ⋆ f = weilTest f (tilde f)`, with `K̂ = f̂²` (`paperFT_convSq`). Such kernels need not be
even, which is what lets them beat the cosh kernel (paper, Section 6).

Results, for `K ∈ C_c²` with `‖K̂(r)‖ = ‖f̂(r)‖²` (`f ∈ C_c²`):
* `norm_primeSide_twist_le_maj`: `‖P_χ(K_y)‖ ≤ ‖Γ_χ(K_y)‖ + Re(Γ_χ(M) − P_χ(M))` (GRH);
* `primeSideZeta_twist_eq_maj`: `P_ζ(K_y) = Pole(K_y) + Γ_ζ(K_y) − E`,
  `‖E‖ ≤ Re(Pole(M) − P_ζ(M) + Γ_ζ(M))` (RH);
* `norm_gammaSide_twist_le_maj` (if `K(−y) = 0`) and `norm_gammaSideZeta_twist_le_maj`.
-/

noncomputable section

open Complex MeasureTheory Zeta23 Zeta23.EF Zeta23.ThmE
open scoped Real ComplexConjugate

namespace GRHPseudo.Sharp

/-- The transform of a convolution square: `(f ⋆ f)^ = f̂²`. -/
lemma paperFT_convSq {f : ℝ → ℂ} (hf : Continuous f) (hfs : HasCompactSupport f) (z : ℂ) :
    paperFT (weilTest f (tilde f)) z = paperFT f z ^ 2 := by
  rw [paperFT_weilTest hf (continuous_tilde hf) hfs (hasCompactSupport_tilde hfs), paperFT_tilde,
    Complex.conj_conj, Complex.conj_conj, sq]

lemma norm_paperFT_convSq {f : ℝ → ℂ} (hf : Continuous f) (hfs : HasCompactSupport f) (r : ℝ) :
    ‖paperFT (weilTest f (tilde f)) (r : ℂ)‖ = ‖paperFT f (r : ℂ)‖ ^ 2 := by
  rw [paperFT_convSq hf hfs, norm_pow]

variable {f K : ℝ → ℂ}

lemma norm_exp_I_real_mul (r y : ℝ) : ‖Complex.exp (I * (r : ℂ) * (y : ℂ))‖ = 1 := by
  rw [Complex.norm_exp]; simp

lemma norm_paperFT_twist_maj (hKf : ∀ r : ℝ, ‖paperFT K (r : ℂ)‖ = ‖paperFT f (r : ℂ)‖ ^ 2)
    (y r : ℝ) : ‖paperFT (twist K y) (r : ℂ)‖ = ‖paperFT f (r : ℂ)‖ ^ 2 := by
  rw [paperFT_twist, norm_mul, norm_exp_I_real_mul, one_mul, hKf]

variable {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}

/-- **Two-sided positivity bound with a majorant.** -/
theorem norm_primeSide_twist_le_maj (hZ : GRHMiller.DirichletLZerosOnLine) (hq : 1 < q)
    (hprim : χ.IsPrimitive) (hf : ContDiff ℝ 2 f) (hfs : HasCompactSupport f)
    (hK : ContDiff ℝ 2 K) (hKs : HasCompactSupport K)
    (hKf : ∀ r : ℝ, ‖paperFT K (r : ℂ)‖ = ‖paperFT f (r : ℂ)‖ ^ 2) (y : ℝ) :
    ‖primeSide (coeff χ) (twist K y)‖ ≤
      ‖gammaSide (parity χ) q (twist K y)‖ +
        (gammaSide (parity χ) q (weilTest f f) - primeSide (coeff χ) (weilTest f f)).re := by
  set k := weilTest f f with hkdef
  have hk : ContDiff ℝ 2 k := weilTest_contDiff hf hf.continuous hfs
  have hks : HasCompactSupport k := weilTest_hasCompactSupport hfs hfs
  set Z := LZeros (LSeam_of hq hprim)
  obtain ⟨hsum0, hEF0⟩ := EF_lit_chi_L hq hprim k hk hks
  obtain ⟨-, hEFy⟩ := EF_lit_chi_L hq hprim (twist K y) (contDiff_twist hK y)
    (hasCompactSupport_twist hKs y)
  rw [literatureRHSchi_eq] at hEF0 hEFy
  set g : Z.carrier → ℝ := fun ρ ↦ (Z.mult ρ : ℝ) * ‖paperFT f (((ρ : ℂ).im : ℝ) : ℂ)‖ ^ 2
  have hγ : ∀ ρ : Z.carrier, gammaOf (ρ : ℂ) = (((ρ : ℂ).im : ℝ) : ℂ) := by
    rintro ⟨ρ, hρ⟩
    have hz : IsNontrivialZeroL χ ρ := hρ
    exact GRHMiller.gammaOf_eq_im_of_re (hZ q χ ρ hz.2.1 hz.2.2 hz.1)
  have hterm0 : ∀ ρ : Z.carrier, (Z.mult ρ : ℂ) * paperFT k (gammaOf ρ) = (g ρ : ℂ) := by
    intro ρ
    rw [hγ ρ, hkdef, GRHMiller.paperFT_weilTest_self_ofReal hf.continuous hfs]
    simp only [g]; push_cast; rfl
  have hg0 : ∀ ρ, 0 ≤ g ρ := fun ρ ↦ by positivity
  have hgsum : Summable g := by
    rw [← Complex.summable_ofReal]
    exact hsum0.congr hterm0
  have hnormy : ∀ ρ : Z.carrier,
      ‖(Z.mult ρ : ℂ) * paperFT (twist K y) (gammaOf ρ)‖ = g ρ := by
    intro ρ
    rw [norm_mul, hγ ρ, norm_paperFT_twist_maj hKf]
    simp [g]
  set S := ∑' ρ, g ρ
  have hS : (∑' ρ : Z.carrier, (Z.mult ρ : ℂ) * paperFT k (gammaOf ρ)) = (S : ℂ) := by
    rw [tsum_congr hterm0, Complex.ofReal_tsum]
  have hZy : ‖∑' ρ : Z.carrier, (Z.mult ρ : ℂ) * paperFT (twist K y) (gammaOf ρ)‖ ≤ S := by
    calc _ ≤ ∑' ρ : Z.carrier, ‖(Z.mult ρ : ℂ) * paperFT (twist K y) (gammaOf ρ)‖ :=
          norm_tsum_le_tsum_norm (hgsum.congr fun ρ ↦ (hnormy ρ).symm)
      _ = S := tsum_congr hnormy
  have hSre : S = (gammaSide (parity χ) q k - primeSide (coeff χ) k).re := by
    have h := hS.symm.trans hEF0
    have := congrArg Complex.re h
    simp only [Complex.ofReal_re] at this
    rw [this]; congr 1; ring
  have hPy : primeSide (coeff χ) (twist K y) = gammaSide (parity χ) q (twist K y) -
      ∑' ρ : Z.carrier, (Z.mult ρ : ℂ) * paperFT (twist K y) (gammaOf ρ) := by
    rw [hEFy]; ring
  rw [hPy, ← hSre]
  exact (norm_sub_le _ _).trans (by linarith)

/-- **Main-term identity with a majorant** (RH). -/
theorem primeSideZeta_twist_eq_maj (hRH : RiemannHypothesis) (hf : ContDiff ℝ 2 f)
    (hfs : HasCompactSupport f) (hK : ContDiff ℝ 2 K) (hKs : HasCompactSupport K)
    (hKf : ∀ r : ℝ, ‖paperFT K (r : ℂ)‖ = ‖paperFT f (r : ℂ)‖ ^ 2) (y : ℝ) :
    ∃ E : ℂ, ‖E‖ ≤ (poleSide (weilTest f f) - primeSideZeta (weilTest f f) +
        gammaSideZeta (weilTest f f)).re ∧
      primeSideZeta (twist K y) = poleSide (twist K y) + gammaSideZeta (twist K y) - E := by
  set k := weilTest f f with hkdef
  have hk : ContDiff ℝ 2 k := weilTest_contDiff hf hf.continuous hfs
  have hks : HasCompactSupport k := weilTest_hasCompactSupport hfs hfs
  set Z := zetaZeroConfig
  obtain ⟨hsum0, hEF0⟩ := WeilEF.EF_lit_zetaZeroConfig k hk hks
  obtain ⟨-, hEFy⟩ := WeilEF.EF_lit_zetaZeroConfig (twist K y) (contDiff_twist hK y)
    (hasCompactSupport_twist hKs y)
  rw [literatureRHS_eq] at hEF0 hEFy
  set g : Z.carrier → ℝ := fun ρ ↦ (Z.mult ρ : ℝ) * ‖paperFT f (((ρ : ℂ).im : ℝ) : ℂ)‖ ^ 2
  have hγ : ∀ ρ : Z.carrier, gammaOf (ρ : ℂ) = (((ρ : ℂ).im : ℝ) : ℂ) := by
    rintro ⟨ρ, hρ⟩
    have hz : IsNontrivialZero ρ := hρ
    refine GRHMiller.gammaOf_eq_im_of_re (hRH ρ hz.1 ?_ ?_)
    · rintro ⟨n, rfl⟩
      have := hz.2.1
      simp at this
      linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    · rintro rfl
      have := hz.2.2
      norm_num at this
  have hterm0 : ∀ ρ : Z.carrier, (Z.mult ρ : ℂ) * paperFT k (gammaOf ρ) = (g ρ : ℂ) := by
    intro ρ
    rw [hγ ρ, hkdef, GRHMiller.paperFT_weilTest_self_ofReal hf.continuous hfs]
    simp only [g]; push_cast; rfl
  have hgsum : Summable g := by
    rw [← Complex.summable_ofReal]
    exact hsum0.congr hterm0
  have hnormy : ∀ ρ : Z.carrier,
      ‖(Z.mult ρ : ℂ) * paperFT (twist K y) (gammaOf ρ)‖ = g ρ := by
    intro ρ
    rw [norm_mul, hγ ρ, norm_paperFT_twist_maj hKf]
    simp [g]
  set S := ∑' ρ, g ρ
  have hS : (∑' ρ : Z.carrier, (Z.mult ρ : ℂ) * paperFT k (gammaOf ρ)) = (S : ℂ) := by
    rw [tsum_congr hterm0, Complex.ofReal_tsum]
  have hZy : ‖∑' ρ : Z.carrier, (Z.mult ρ : ℂ) * paperFT (twist K y) (gammaOf ρ)‖ ≤ S := by
    calc _ ≤ ∑' ρ : Z.carrier, ‖(Z.mult ρ : ℂ) * paperFT (twist K y) (gammaOf ρ)‖ :=
          norm_tsum_le_tsum_norm (hgsum.congr fun ρ ↦ (hnormy ρ).symm)
      _ = S := tsum_congr hnormy
  have hSre : S = (poleSide k - primeSideZeta k + gammaSideZeta k).re := by
    have := congrArg Complex.re (hS.symm.trans hEF0)
    simpa using this
  refine ⟨∑' ρ : Z.carrier, (Z.mult ρ : ℂ) * paperFT (twist K y) (gammaOf ρ), ?_, ?_⟩
  · rw [← hSre]; exact hZy
  · rw [hEFy]; ring

/-- Fourier inversion at `−y` for a kernel with `‖K̂‖ = ‖f̂‖²`. -/
lemma integral_paperFT_twist_maj (hf : ContDiff ℝ 2 f) (hfs : HasCompactSupport f)
    (hK : ContDiff ℝ 2 K) (hKs : HasCompactSupport K)
    (hKf : ∀ r : ℝ, ‖paperFT K (r : ℂ)‖ = ‖paperFT f (r : ℂ)‖ ^ 2) (y : ℝ) :
    (1 / (2 * π) : ℂ) * ∫ r : ℝ, paperFT (twist K y) (r : ℂ) = K (-y) := by
  have hKi : Integrable K := hK.continuous.integrable_of_hasCompactSupport hKs
  have hcont : Continuous fun r : ℝ ↦ paperFT K (r : ℂ) :=
    (WeilEF.differentiable_paperFT hK.continuous hKs).continuous.comp Complex.continuous_ofReal
  have hPi : Integrable (fun r : ℝ ↦ paperFT K (r : ℂ)) :=
    (integrable_normSq_paperFT hf hfs).mono' hcont.aestronglyMeasurable
      (Filter.Eventually.of_forall fun r ↦ (hKf r).le)
  have hFk : Integrable (FourierTransform.fourier K) := by
    have h := hPi.comp_mul_left' (show (-(2 * π) : ℝ) ≠ 0 by have := Real.pi_pos; linarith)
    refine h.congr (Filter.Eventually.of_forall fun w ↦ ?_)
    show paperFT K ((-(2 * π) * w : ℝ) : ℂ) = _
    rw [EF.paperFT_ofReal_eq_fourier]
    congr 1
    field_simp
  have hpt : ∀ r : ℝ, paperFT (twist K y) (r : ℂ) =
      paperFT K (r : ℂ) * Complex.exp (-I * (r : ℂ) * ((-y : ℝ) : ℂ)) := by
    intro r; rw [paperFT_twist, mul_comm]; congr 2; push_cast; ring
  simp_rw [hpt]
  exact (paper_inversion hK.continuous hKi hFk (-y)).symm

/-- **Twisted χ gamma side with a majorant.** -/
theorem norm_gammaSide_twist_le_maj (hf : ContDiff ℝ 2 f) (hfs : HasCompactSupport f)
    (hK : ContDiff ℝ 2 K) (hKs : HasCompactSupport K)
    (hKf : ∀ r : ℝ, ‖paperFT K (r : ℂ)‖ = ‖paperFT f (r : ℂ)‖ ^ 2) {κ q : ℕ}
    (hκ : κ ≤ 1) {y : ℝ} (hy : K (-y) = 0) :
    ‖gammaSide κ q (twist K y)‖ ≤ Ilog f 5 / (2 * π) := by
  set P : ℝ → ℂ := fun r ↦ paperFT (twist K y) (r : ℂ)
  set ψ : ℝ → ℝ := fun r ↦ (Complex.digamma (1 / 4 + (κ : ℂ) / 2 + I * r / 2)).re
  set L : ℝ := Real.log (q / π)
  have hPn : ∀ r, ‖P r‖ = ‖paperFT f (r : ℂ)‖ ^ 2 := norm_paperFT_twist_maj hKf y
  have hmeasP : AEStronglyMeasurable P := by
    have hc : Continuous fun r : ℝ ↦ paperFT (twist K y) (r : ℂ) := by
      have := (WeilEF.differentiable_paperFT
        (hK.continuous.comp (continuous_id.sub continuous_const)) (hasCompactSupport_twist hKs y))
      exact this.continuous.comp Complex.continuous_ofReal
    exact hc.aestronglyMeasurable
  have hPint : Integrable P :=
    (integrable_normSq_paperFT hf hfs).mono' hmeasP
      (Filter.Eventually.of_forall fun r ↦ (hPn r).le)
  have hdom := GRHMiller.integrable_normSq_paperFT_mul_log hf hfs 1 5
  have hψcont : Continuous fun r : ℝ ↦ ((ψ r : ℝ) : ℂ) := by
    have := GRHMiller.continuous_gammaDensity κ q
    have h2 : Continuous ψ :=
      (this.sub (continuous_const (y := Real.log (q / π)))).congr fun r ↦ by
        simp only [Pi.sub_apply, GRHMiller.gammaDensity, ψ]; ring
    exact Complex.continuous_ofReal.comp h2
  have hPψ : Integrable fun r ↦ P r * ((ψ r : ℝ) : ℂ) := by
    refine hdom.mono' (hmeasP.mul hψcont.aestronglyMeasurable)
      (Filter.Eventually.of_forall fun r ↦ ?_)
    rw [norm_mul, hPn, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (by rw [one_mul]; exact abs_re_digamma_le κ hκ r) (by positivity)
  have hsplit : (∫ r : ℝ, P r * (((ψ r + L : ℝ)) : ℂ)) =
      (∫ r : ℝ, P r * ((ψ r : ℝ) : ℂ)) + (L : ℂ) * ∫ r : ℝ, P r := by
    rw [← integral_const_mul, ← integral_add hPψ (hPint.const_mul _)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun r ↦ ?_)
    simp only [Complex.ofReal_add]; ring
  have hzero : (∫ r : ℝ, P r) = 0 := by
    have h := integral_paperFT_twist_maj hf hfs hK hKs hKf y
    rw [hy] at h
    have hpi : (1 / (2 * π) : ℂ) ≠ 0 := by
      have := Real.pi_pos; simp only [ne_eq, one_div, inv_eq_zero, mul_eq_zero, OfNat.ofNat_ne_zero,
        Complex.ofReal_eq_zero, false_or]; exact this.ne'
    exact (mul_eq_zero.mp h).resolve_left hpi
  unfold gammaSide
  change ‖(1 / (2 * π) : ℂ) * ∫ r : ℝ, P r * (((ψ r + L : ℝ)) : ℂ)‖ ≤ _
  rw [hsplit, hzero, mul_zero, add_zero, norm_mul]
  have hc : ‖(1 / (2 * π) : ℂ)‖ = 1 / (2 * π) := by
    rw [norm_div, norm_one, norm_mul, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos Real.pi_pos]
  rw [hc, div_eq_mul_one_div (Ilog f 5), mul_comm (Ilog f 5)]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine norm_integral_le_of_norm_le hdom (Filter.Eventually.of_forall fun r ↦ ?_)
  rw [norm_mul, hPn, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (by rw [one_mul]; exact abs_re_digamma_le κ hκ r) (by positivity)

/-- **Twisted ζ gamma side with a majorant.** -/
theorem norm_gammaSideZeta_twist_le_maj (hf : ContDiff ℝ 2 f) (hfs : HasCompactSupport f)
    (hKf : ∀ r : ℝ, ‖paperFT K (r : ℂ)‖ = ‖paperFT f (r : ℂ)‖ ^ 2) (y : ℝ) :
    ‖gammaSideZeta (twist K y)‖ ≤ Ilog f (5 + Real.log π) / (2 * π) := by
  have hPn := norm_paperFT_twist_maj hKf y
  have hdom := GRHMiller.integrable_normSq_paperFT_mul_log hf hfs 1 (5 + Real.log π)
  unfold gammaSideZeta
  rw [norm_mul]
  have hc : ‖(1 / (2 * π) : ℂ)‖ = 1 / (2 * π) := by
    rw [norm_div, norm_one, norm_mul, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos Real.pi_pos]
  rw [hc, div_eq_mul_one_div (Ilog f _), mul_comm (Ilog f _)]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine norm_integral_le_of_norm_le hdom (Filter.Eventually.of_forall fun r ↦ ?_)
  rw [norm_mul, hPn, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (by rw [one_mul]; exact abs_gammaBracket_le r) (by positivity)

/-- Twisted prime side as a finite sum, for a kernel supported in `[−L, 0]`. -/
theorem primeSide_twist_eq_sum_left (c : ℕ → ℂ) (hK0 : ∀ u, 0 < u → K u = 0)
    {L : ℝ} (hKL : ∀ u, u < -L → K u = 0) {y : ℝ} (hy : L < y) :
    primeSide c (twist K y) = ∑ n ∈ Finset.range (⌊Real.exp y⌋₊ + 1),
      ((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ) * (c n * K (Real.log n - y)) := by
  unfold primeSide twist
  have hleg : ∀ n : ℕ, K (-Real.log n - y) = 0 := fun n ↦
    hKL _ (by linarith [log_natCast_nonneg' n])
  simp_rw [hleg, mul_zero, add_zero]
  refine tsum_eq_sum fun n hn ↦ ?_
  rw [Finset.mem_range, not_lt] at hn
  have := log_gt_of_ge_floor_succ hn
  rw [hK0 _ (by linarith), mul_zero, mul_zero]

end GRHPseudo.Sharp
