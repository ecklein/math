import GRHPseudo.AnalyticNumberTheory.Sharp.ConvKernel
import GRHPseudo.Pseudorandomness.Bias

/-!
# The sharp bias theorem for the convolution-square kernel

Kernel `K_A = f_A ⋆ f_A` (`ConvKernel`), supported in `[−2A, 0]`, with majorant `M_A = f_A ⋆ f̃_A`.

Sample space, for a modulus `q` and twist `y > 2A` (`x = e^y`): the integers `n ≤ x` coprime to
`q`, with weights `w(n) = Λ(n) K_A(log n − y) / √n`. They are supported on prime powers in
`[x e^{−2A}, x]`; the top of the support is `x` itself.

**Theorem** (`bias_sharp`). Assume zeros of Dirichlet L-functions in the strip lie on the line
and RH. For every `q ≥ 1`, every `χ ≠ 1` mod `q`, every `A ≥ 0` and `y > 2A`, if `Den > 0` then
`bias ≤ Num / Den`, where

    Num = M_A(0) log(q/π) + SP(A) + (I(5) + I(1/2))/(2π) + U,
    Den = e^{y/2} F₊² − 2 F₊ F₋ − (I(5 + log π) + I(1/2))/(2π) − U,

with `F₊ = ∫ f_A e^{t/2}`, `F₋ = ∫ f_A e^{−t/2}`, `SP(A)` the small-prime sum of `M_A` and `U` the
weight of non-units. The leading term is `M_A(0) log q / (√x F₊²) ≈ log q / (√x (1 − e^{−A}))`.
-/

noncomputable section

open Complex Finset MeasureTheory Zeta23 Zeta23.EF Zeta23.ThmE
open scoped Real ComplexConjugate

namespace GRHPseudo.Sharp.Conv

/-- Cutoff `⌊e^y⌋ + 1`. -/
def cutoff (y : ℝ) : ℕ := ⌊Real.exp y⌋₊ + 1

/-- Weights `w(n) = Λ(n) K_A(log n − y)/√n`. -/
def wt (A y : ℝ) (n : ℕ) : ℝ :=
  ArithmeticFunction.vonMangoldt n * (K A (Real.log n - y)).re / Real.sqrt n

/-- Units mod `q` below the cutoff. -/
def sampleSpace (q : ℕ) (y : ℝ) : Finset ℕ :=
  (range (cutoff y)).filter fun n ↦ Nat.Coprime n q

/-- Weight of non-units mod `q`. -/
def nonunitWt (q : ℕ) (A y : ℝ) : ℝ :=
  ∑ n ∈ (range (cutoff y)).filter (fun n ↦ ¬ Nat.Coprime n q), |wt A y n|

/-- Small-prime sum of the majorant, `Σ_{n ≤ e^A} Λ(n) (|M(log n)| + |M(−log n)|)/√n`. -/
def smallPrimes (A : ℝ) : ℝ :=
  ∑ n ∈ range (⌊Real.exp A⌋₊ + 1), ArithmeticFunction.vonMangoldt n / Real.sqrt n *
    (‖M A (Real.log n)‖ + ‖M A (-Real.log n)‖)

/-- Numerator of the bias bound. -/
def sharpNum (q : ℕ) (A y : ℝ) : ℝ :=
  (M A 0).re * Real.log (q / π) + smallPrimes A +
    (Ilog (f A) 5 + Ilog (f A) (1 / 2)) / (2 * π) + nonunitWt q A y

/-- Denominator of the bias bound. -/
def sharpDen (q : ℕ) (A y : ℝ) : ℝ :=
  Real.exp (y / 2) * Fp A ^ 2 - 2 * (Fp A * Fm A) -
    (Ilog (f A) (5 + Real.log π) + Ilog (f A) (1 / 2)) / (2 * π) - nonunitWt q A y

lemma re_primeSideZeta_M_nonneg (A : ℝ) (hA : 0 ≤ A) : 0 ≤ (primeSideZeta (M A)).re := by
  rw [primeSideZeta_eq, primeSide_eq_sum (L := A) _ fun u hu ↦ M_eq_zero hu, Complex.re_sum]
  refine sum_nonneg fun n _ ↦ ?_
  simp only [map_one, one_mul]
  rw [Complex.re_ofReal_mul, Complex.add_re]
  exact mul_nonneg (div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _))
    (add_nonneg (M_re_nonneg _ _) (M_re_nonneg _ _))

variable {q : ℕ} [NeZero q]

/-- **Sharp bounds:** the character sum is at most `sharpNum` and the mass at least `sharpDen`. -/
theorem sharp_charSum_mass (hZ : GRHMiller.DirichletLZerosOnLine) (hRH : RiemannHypothesis)
    {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) {A y : ℝ} (hA : 0 ≤ A) (hy : 2 * A < y) :
    ‖charSum (sampleSpace q y) (wt A y) χ‖ ≤ sharpNum q A y ∧
      sharpDen q A y ≤ mass (sampleSpace q y) (wt A y) := by
  have hf : ContDiff ℝ 2 (f A) := contDiff_f A
  have hfs : HasCompactSupport (f A) := hasCompactSupport_f A
  have hK : ContDiff ℝ 2 (K A) := contDiff_K A
  have hKs : HasCompactSupport (K A) := hasCompactSupport_K A
  have hKf : ∀ r : ℝ, ‖paperFT (K A) (r : ℂ)‖ = ‖paperFT (f A) (r : ℂ)‖ ^ 2 := norm_paperFT_K A
  have hM_eq : weilTest (f A) (f A) = M A := rfl
  set Mc := cutoff y
  have hK0 : ∀ u, 0 < u → K A u = 0 := fun u hu ↦ K_eq_zero_of_pos hu
  have hKL : ∀ u, u < -(2 * A) → K A u = 0 := fun u hu ↦ K_eq_zero_of_lt hu
  have hky : K A (-y) = 0 := hKL _ (by linarith)
  have hMs : ∀ u, A < |u| → M A u = 0 := fun u hu ↦ M_eq_zero hu
  -- primitive character
  set χ' := χ.primitiveCharacter
  haveI : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have hprim : χ'.IsPrimitive := DirichletCharacter.primitiveCharacter_isPrimitive χ
  have hq' : 1 < χ.conductor := by
    have h0 := χ.conductor_ne_zero
    have h1 : χ.conductor ≠ 1 := fun h ↦ hχ (DirichletCharacter.eq_one_iff_conductor_eq_one.mpr h)
    omega
  have hcop : ∀ n : ℕ, Nat.Coprime n q → χ' n = χ n := by
    intro n hn
    have h := DirichletCharacter.primitiveCharacter_apply_of_isCoprime χ (a := (n : ℤ))
      (Nat.isCoprime_iff_coprime.mpr hn)
    simpa using h
  -- the twisted prime sum for χ'
  set T := primeSide (coeff χ') (twist (K A) y)
  have hTsum : T = ∑ n ∈ range Mc, ((wt A y n : ℝ) : ℂ) * χ' n := by
    show primeSide (coeff χ') (twist (K A) y) = _
    rw [primeSide_twist_eq_sum_left _ hK0 hKL hy]
    refine sum_congr rfl fun n _ ↦ ?_
    simp only [coeff, wt]
    conv_lhs => rw [show K A (Real.log n - y) = (((K A (Real.log n - y)).re : ℝ) : ℂ) from K_real A _]
    push_cast; ring
  have hsplit : charSum (sampleSpace q y) (wt A y) χ =
      T - ∑ n ∈ (range Mc).filter (fun n ↦ ¬ Nat.Coprime n q), ((wt A y n : ℝ) : ℂ) * χ' n := by
    rw [hTsum, ← sum_filter_add_sum_filter_not (range Mc) (fun n ↦ Nat.Coprime n q),
      add_sub_cancel_right]
    unfold charSum sampleSpace
    refine sum_congr rfl fun n hn ↦ ?_
    rw [hcop n (mem_filter.mp hn).2]
  have hnonunit : ‖∑ n ∈ (range Mc).filter (fun n ↦ ¬ Nat.Coprime n q),
      ((wt A y n : ℝ) : ℂ) * χ' n‖ ≤ nonunitWt q A y := by
    refine (norm_sum_le _ _).trans (sum_le_sum fun n _ ↦ ?_)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_of_le_one_right (abs_nonneg _) (χ'.norm_le_one _)
  -- bound on T
  have hparity : parity χ' ≤ 1 := by unfold parity; split_ifs <;> norm_num
  have hT := norm_primeSide_twist_le_maj hZ hq' hprim hf hfs hK hKs hKf y
  have hΓy := norm_gammaSide_twist_le_maj hf hfs hK hKs hKf hparity (q := χ.conductor) hky
  have hΓ0 := re_gammaSide_le hf hfs hparity (q := χ.conductor)
  rw [hM_eq] at hT hΓ0
  have hP0 : -(primeSide (coeff χ') (M A)).re ≤ smallPrimes A := by
    rw [primeSide_eq_sum (L := A) _ hMs]
    refine (neg_le_abs _).trans ((Complex.abs_re_le_norm _).trans ((norm_sum_le _ _).trans
      (sum_le_sum fun n _ ↦ ?_)))
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _))]
    refine mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans (add_le_add ?_ ?_))
      (div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _))
    · rw [norm_mul]; exact mul_le_of_le_one_left (norm_nonneg _) (χ'.norm_le_one _)
    · rw [norm_mul, Complex.norm_conj]; exact mul_le_of_le_one_left (norm_nonneg _) (χ'.norm_le_one _)
  have hlogq : (M A 0).re * Real.log (χ.conductor / π) ≤ (M A 0).re * Real.log (q / π) := by
    refine mul_le_mul_of_nonneg_left ?_ (M_re_nonneg A 0)
    have hc : (0 : ℝ) < χ.conductor := by exact_mod_cast Nat.pos_of_ne_zero χ.conductor_ne_zero
    apply Real.log_le_log (div_pos hc Real.pi_pos)
    apply div_le_div_of_nonneg_right _ Real.pi_pos.le
    exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne q)) χ.conductor_dvd_level
  have hnum : ‖charSum (sampleSpace q y) (wt A y) χ‖ ≤ sharpNum q A y := by
    rw [hsplit]
    refine (norm_sub_le _ _).trans ?_
    unfold sharpNum
    have hT' := hT
    rw [Complex.sub_re] at hT'
    have hdiv : (Ilog (f A) 5 + Ilog (f A) (1 / 2)) / (2 * π) =
        Ilog (f A) 5 / (2 * π) + Ilog (f A) (1 / 2) / (2 * π) := add_div _ _ _
    linarith
  -- mass
  have hmassSplit : mass (sampleSpace q y) (wt A y) =
      ∑ n ∈ range Mc, wt A y n -
        ∑ n ∈ (range Mc).filter (fun n ↦ ¬ Nat.Coprime n q), wt A y n := by
    unfold mass sampleSpace
    rw [← sum_filter_add_sum_filter_not (range Mc) (fun n ↦ Nat.Coprime n q), add_sub_cancel_right]
  have hnon' : ∑ n ∈ (range Mc).filter (fun n ↦ ¬ Nat.Coprime n q), wt A y n ≤ nonunitWt q A y :=
    sum_le_sum fun n _ ↦ le_abs_self _
  have hall : ∑ n ∈ range Mc, wt A y n = (primeSideZeta (twist (K A) y)).re := by
    rw [primeSideZeta_eq, primeSide_twist_eq_sum_left _ hK0 hKL hy, Complex.re_sum]
    refine sum_congr rfl fun n _ ↦ ?_
    simp only [wt, one_mul]
    rw [Complex.re_ofReal_mul]
    ring
  obtain ⟨E, hE, hPζ⟩ := primeSideZeta_twist_eq_maj hRH hf hfs hK hKs hKf y
  have hΓζy := norm_gammaSideZeta_twist_le_maj hf hfs hKf y
  have hΓζ0 := re_gammaSideZeta_le hf hfs
  rw [hM_eq] at hE hΓζ0
  have hpole := poleSide_twist (K A) y
  have hPζ0 := re_primeSideZeta_M_nonneg A hA
  have hKI : (paperFT (K A) (I / 2)).re = Fm A ^ 2 := by
    rw [paperFT_K_I_half, Complex.ofReal_re]
  have hKnI : (paperFT (K A) (-I / 2)).re = Fp A ^ 2 := by
    rw [paperFT_K_neg_I_half, Complex.ofReal_re]
  have hpoleM : (poleSide (M A)).re = 2 * (Fp A * Fm A) := by
    rw [poleSide_M, Complex.ofReal_re]
  have hmass : sharpDen q A y ≤ mass (sampleSpace q y) (wt A y) := by
    rw [hmassSplit, hall, hPζ, Complex.sub_re, Complex.add_re, hpole, Complex.add_re,
      Complex.re_ofReal_mul, Complex.re_ofReal_mul, hKI, hKnI]
    have h1' := neg_le_abs (gammaSideZeta (twist (K A) y)).re
    have h1'' := Complex.abs_re_le_norm (gammaSideZeta (twist (K A) y))
    have h2 := Complex.re_le_norm E
    have hexp : 0 ≤ Real.exp (-y / 2) * Fm A ^ 2 := by positivity
    unfold sharpDen
    rw [Complex.add_re, Complex.sub_re, hpoleM] at hE
    have hdiv : (Ilog (f A) (5 + Real.log π) + Ilog (f A) (1 / 2)) / (2 * π) =
        Ilog (f A) (5 + Real.log π) / (2 * π) + Ilog (f A) (1 / 2) / (2 * π) := add_div _ _ _
    linarith
  exact ⟨hnum, hmass⟩

/-- **Sharp bias theorem for the convolution-square kernel.** -/
theorem bias_sharp (hZ : GRHMiller.DirichletLZerosOnLine) (hRH : RiemannHypothesis)
    {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) {A y : ℝ} (hA : 0 ≤ A) (hy : 2 * A < y)
    (hden : 0 < sharpDen q A y) :
    bias (sampleSpace q y) (wt A y) χ ≤ sharpNum q A y / sharpDen q A y := by
  obtain ⟨hnum, hmass⟩ := sharp_charSum_mass hZ hRH hχ hA hy
  exact bias_le_of_bounds _ _ _ hnum hden hmass

end GRHPseudo.Sharp.Conv
