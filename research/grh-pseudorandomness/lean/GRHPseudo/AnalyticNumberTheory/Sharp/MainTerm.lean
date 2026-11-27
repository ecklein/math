import GRHPseudo.AnalyticNumberTheory.Sharp.TwoSided

/-!
# Main term for twisted prime sums from RH (obligation D4)

For `k = f ⋆ f̃` the explicit formula for `ζ` reads `Σ_ρ m_ρ k̂(γ_ρ) = k̂(i/2) + k̂(−i/2) − P_ζ(k)
+ Γ_ζ(k)`, where `P_ζ(k) = Σ_n Λ(n) n^{-1/2} (k(log n) + k(−log n))` (`literatureRHS`). Under RH,
the zero sum for the twisted kernel has norm at most `S_ζ = Re(zero sum for k)`. Since
`k̂_y(∓i/2) = e^{±y/2} k̂(∓i/2)`,

    P_ζ(k_y) = e^{y/2} k̂(−i/2) + e^{−y/2} k̂(i/2) + Γ_ζ(k_y) − Z_ζ(k_y),  ‖Z_ζ(k_y)‖ ≤ S_ζ.

`k̂(−i/2) = ∫ k(u) e^{u/2} du` is the main term.
-/

noncomputable section

open Complex MeasureTheory Zeta23 Zeta23.EF
open scoped Real ComplexConjugate

namespace GRHPseudo.Sharp

/-- Prime side of the explicit formula for `ζ`. -/
def primeSideZeta (k : ℝ → ℂ) : ℂ :=
  ∑' n : ℕ, ((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ)
    * (k (Real.log n) + k (-Real.log n))

/-- Gamma side of the explicit formula for `ζ`. -/
def gammaSideZeta (k : ℝ → ℂ) : ℂ :=
  (1 / (2 * π) : ℂ) * ∫ r : ℝ, paperFT k r * (gammaBracket r : ℂ)

/-- Pole terms. -/
def poleSide (k : ℝ → ℂ) : ℂ := paperFT k (I / 2) + paperFT k (-I / 2)

lemma literatureRHS_eq (k : ℝ → ℂ) :
    literatureRHS k = poleSide k - primeSideZeta k + gammaSideZeta k := rfl

lemma poleSide_twist (k : ℝ → ℂ) (y : ℝ) :
    poleSide (twist k y) = (Real.exp (-y / 2) : ℂ) * paperFT k (I / 2) +
      (Real.exp (y / 2) : ℂ) * paperFT k (-I / 2) := by
  unfold poleSide
  rw [paperFT_twist, paperFT_twist]
  congr 2
  · rw [Complex.ofReal_exp]; congr 1; push_cast; ring_nf; rw [I_sq]; ring
  · rw [Complex.ofReal_exp]; congr 1; push_cast; ring_nf; rw [I_sq]; ring

/-- **Main-term identity with error control under RH.** -/
theorem primeSideZeta_twist_eq (hRH : RiemannHypothesis) {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f)
    (hfs : HasCompactSupport f) (y : ℝ) :
    ∃ E : ℂ, ‖E‖ ≤ (poleSide (weilTest f f) - primeSideZeta (weilTest f f) +
        gammaSideZeta (weilTest f f)).re ∧
      primeSideZeta (twist (weilTest f f) y) =
        poleSide (twist (weilTest f f) y) + gammaSideZeta (twist (weilTest f f) y) - E := by
  set k := weilTest f f with hkdef
  have hk : ContDiff ℝ 2 k := weilTest_contDiff hf hf.continuous hfs
  have hks : HasCompactSupport k := weilTest_hasCompactSupport hfs hfs
  set Z := zetaZeroConfig
  obtain ⟨hsum0, hEF0⟩ := WeilEF.EF_lit_zetaZeroConfig k hk hks
  obtain ⟨-, hEFy⟩ := WeilEF.EF_lit_zetaZeroConfig (twist k y) (contDiff_twist hk y)
    (hasCompactSupport_twist hks y)
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
  have hg0 : ∀ ρ, 0 ≤ g ρ := fun ρ ↦ by positivity
  have hgsum : Summable g := by
    rw [← Complex.summable_ofReal]
    exact hsum0.congr hterm0
  have hnormy : ∀ ρ : Z.carrier,
      ‖(Z.mult ρ : ℂ) * paperFT (twist k y) (gammaOf ρ)‖ = g ρ := by
    intro ρ
    rw [paperFT_twist, ← mul_assoc, mul_comm (Z.mult ρ : ℂ), mul_assoc, norm_mul, hterm0,
      hγ ρ, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hg0 ρ)]
    have : ‖Complex.exp (I * (((ρ : ℂ).im : ℝ) : ℂ) * (y : ℂ))‖ = 1 := by
      rw [Complex.norm_exp]; simp
    rw [this, one_mul]
  set S := ∑' ρ, g ρ
  have hS : (∑' ρ : Z.carrier, (Z.mult ρ : ℂ) * paperFT k (gammaOf ρ)) = (S : ℂ) := by
    rw [tsum_congr hterm0, Complex.ofReal_tsum]
  have hZy : ‖∑' ρ : Z.carrier, (Z.mult ρ : ℂ) * paperFT (twist k y) (gammaOf ρ)‖ ≤ S := by
    calc _ ≤ ∑' ρ : Z.carrier, ‖(Z.mult ρ : ℂ) * paperFT (twist k y) (gammaOf ρ)‖ :=
          norm_tsum_le_tsum_norm (hgsum.congr fun ρ ↦ (hnormy ρ).symm)
      _ = S := tsum_congr hnormy
  have hSre : S = (poleSide k - primeSideZeta k + gammaSideZeta k).re := by
    have := congrArg Complex.re (hS.symm.trans hEF0)
    simpa using this
  refine ⟨∑' ρ : Z.carrier, (Z.mult ρ : ℂ) * paperFT (twist k y) (gammaOf ρ), ?_, ?_⟩
  · rw [← hSre]; exact hZy
  · rw [hEFy]; ring

end GRHPseudo.Sharp
