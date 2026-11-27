import GRHPseudo.Vendor.GRHMiller.Ankeny
import GRHPseudo.AnalyticNumberTheory.Sharp.Twist

/-!
# Two-sided positivity bound for twisted prime sums (obligation D2; uses GRH)

For primitive `χ` mod `q > 1` and `k = f ⋆ f̃` with `f ∈ C_c²`, write the explicit formula as
`Σ_ρ m_ρ k̂(γ_ρ) = −P(k) + Γ(k)` (`literatureRHSchi`). Under GRH every `γ_ρ` is real, so for the
twisted kernel `k_y = k(· − y)`

    Σ_ρ m_ρ k̂_y(γ_ρ) = Σ_ρ m_ρ e^{iγ_ρ y} |f̂(γ_ρ)|²,

which has norm at most `S = Σ_ρ m_ρ |f̂(γ_ρ)|² = Re(Γ(k) − P(k))`. Hence

    ‖P(k_y)‖ ≤ ‖Γ(k_y)‖ + Re(Γ(k) − P(k)).
-/

noncomputable section

open Complex MeasureTheory Zeta23 Zeta23.EF Zeta23.ThmE
open scoped Real ComplexConjugate

namespace GRHPseudo.Sharp

/-- Prime side of the explicit formula for coefficients `c`. -/
def primeSide (c : ℕ → ℂ) (k : ℝ → ℂ) : ℂ :=
  ∑' n : ℕ, ((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ)
    * (c n * k (Real.log n) + conj (c n) * k (-Real.log n))

/-- Gamma (archimedean) side of the explicit formula for a character of parity `κ` mod `q`. -/
def gammaSide (κ q : ℕ) (k : ℝ → ℂ) : ℂ :=
  (1 / (2 * π) : ℂ) * ∫ r : ℝ, paperFT k r
    * ((((Complex.digamma (1 / 4 + (κ : ℂ) / 2 + I * r / 2)).re + Real.log (q / π) : ℝ)) : ℂ)

lemma literatureRHSchi_eq (κ q : ℕ) (c : ℕ → ℂ) (k : ℝ → ℂ) :
    literatureRHSchi κ q c k = -primeSide c k + gammaSide κ q k := rfl

lemma contDiff_twist {k : ℝ → ℂ} (hk : ContDiff ℝ 2 k) (y : ℝ) : ContDiff ℝ 2 (twist k y) :=
  hk.comp (contDiff_id.sub contDiff_const)

lemma hasCompactSupport_twist {k : ℝ → ℂ} (hk : HasCompactSupport k) (y : ℝ) :
    HasCompactSupport (twist k y) :=
  hk.comp_homeomorph (Homeomorph.subRight y)

variable {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}

/-- **Two-sided positivity bound.** -/
theorem norm_primeSide_twist_le (hZ : GRHMiller.DirichletLZerosOnLine) (hq : 1 < q)
    (hprim : χ.IsPrimitive) {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f) (hfs : HasCompactSupport f)
    (y : ℝ) :
    ‖primeSide (coeff χ) (twist (weilTest f f) y)‖ ≤
      ‖gammaSide (parity χ) q (twist (weilTest f f) y)‖ +
        (gammaSide (parity χ) q (weilTest f f) - primeSide (coeff χ) (weilTest f f)).re := by
  set k := weilTest f f with hkdef
  have hk : ContDiff ℝ 2 k := weilTest_contDiff hf hf.continuous hfs
  have hks : HasCompactSupport k := weilTest_hasCompactSupport hfs hfs
  set Z := LZeros (LSeam_of hq hprim)
  obtain ⟨hsum0, hEF0⟩ := EF_lit_chi_L hq hprim k hk hks
  obtain ⟨-, hEFy⟩ := EF_lit_chi_L hq hprim (twist k y) (contDiff_twist hk y)
    (hasCompactSupport_twist hks y)
  rw [literatureRHSchi_eq] at hEF0 hEFy
  -- the untwisted zero terms are the nonnegative reals `g ρ`
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
      ‖(Z.mult ρ : ℂ) * paperFT (twist k y) (gammaOf ρ)‖ = g ρ := by
    intro ρ
    rw [paperFT_twist, ← mul_assoc, mul_comm (Z.mult ρ : ℂ), mul_assoc, norm_mul, hterm0,
      hγ ρ, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hg0 ρ)]
    have : ‖Complex.exp (I * (((ρ : ℂ).im : ℝ) : ℂ) * (y : ℂ))‖ = 1 := by
      rw [Complex.norm_exp]
      simp
    rw [this, one_mul]
  -- `S = Σ g`
  set S := ∑' ρ, g ρ
  have hS : (∑' ρ : Z.carrier, (Z.mult ρ : ℂ) * paperFT k (gammaOf ρ)) = (S : ℂ) := by
    rw [tsum_congr hterm0, Complex.ofReal_tsum]
  have hZy : ‖∑' ρ : Z.carrier, (Z.mult ρ : ℂ) * paperFT (twist k y) (gammaOf ρ)‖ ≤ S := by
    calc _ ≤ ∑' ρ : Z.carrier, ‖(Z.mult ρ : ℂ) * paperFT (twist k y) (gammaOf ρ)‖ :=
          norm_tsum_le_tsum_norm (hgsum.congr fun ρ ↦ (hnormy ρ).symm)
      _ = S := tsum_congr hnormy
  have hSre : S = (gammaSide (parity χ) q k - primeSide (coeff χ) k).re := by
    have h := hS.symm.trans hEF0
    have := congrArg Complex.re h
    simp only [Complex.ofReal_re] at this
    rw [this]; congr 1; ring
  -- P_y = Γ_y − Z_y
  have hPy : primeSide (coeff χ) (twist k y) = gammaSide (parity χ) q (twist k y) -
      ∑' ρ : Z.carrier, (Z.mult ρ : ℂ) * paperFT (twist k y) (gammaOf ρ) := by
    rw [hEFy]; ring
  rw [hPy, ← hSre]
  exact (norm_sub_le _ _).trans (by linarith)

end GRHPseudo.Sharp
