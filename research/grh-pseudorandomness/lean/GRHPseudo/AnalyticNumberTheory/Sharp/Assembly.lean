import GRHPseudo.AnalyticNumberTheory.Sharp.FiniteSums
import GRHPseudo.Pseudorandomness.Bias

/-!
# The sharp bias theorem, Layer 1 (obligations D5, D6)

Kernel: `k_a = f_a ⋆ f̃_a` with `f_a = testFnN a = cosh(t/2) · cutoff_a(t)` (grh-miller). It is
real, nonnegative, and vanishes for `|u| > 2a`.

Sample space, for a modulus `q` and twist `y > 2a` (i.e. `x = e^y`): the integers
`n ≤ e^{y+2a}` coprime to `q`, with weights `w(n) = Λ(n) k_a(log n − y) / √n`. They are
supported on prime powers in `[x e^{−2a}, x e^{2a}]`.

**Theorem** (`bias_sharp`). Assume zeros of Dirichlet L-functions in the strip lie on the line
and RH. For every `q ≥ 1`, every `χ ≠ 1` mod `q` (primitive or not), every `a ≥ 0` and every
`y > 2a`, if `Den > 0` then `bias ≤ Num / Den`, where

    Num = k_a(0) log(q/π) + SP(a) + (I(5) + I(1/2))/(2π) + U,
    Den = e^{y/2} A(a) − B(a) − (I(5 + log π) + I(1/2))/(2π) − U,

with `A(a) = Re k̂_a(−i/2) = ∫ k_a(u) e^{u/2} du`, `B(a) = Re(k̂_a(i/2) + k̂_a(−i/2))`, `I(B)` the
integrals of `GammaBounds`, `SP(a)` the small-prime sum, and `U` the weight of non-units mod `q`.
The leading term of `Num/Den` is `k_a(0) log q / (√x A(a))`.
-/

noncomputable section

open Complex Finset MeasureTheory Zeta23 Zeta23.EF Zeta23.ThmE
open scoped Real ComplexConjugate

namespace GRHPseudo.Sharp

/-! ### The kernel -/

/-- The test function `f_a`. -/
def testF (a : ℝ) : ℝ → ℂ := GRHMiller.Narrow.testFnN a

/-- The kernel `k_a = f_a ⋆ f̃_a`. -/
def kern (a : ℝ) : ℝ → ℂ := weilTest (testF a) (testF a)

lemma contDiff_testF (a : ℝ) : ContDiff ℝ 2 (testF a) := GRHMiller.Narrow.contDiff_testFnN a
lemma hasCompactSupport_testF (a : ℝ) : HasCompactSupport (testF a) :=
  GRHMiller.Narrow.hasCompactSupport_testFnN a

lemma kern_eq_zero {a : ℝ} {u : ℝ} (hu : 2 * a < |u|) : kern a u = 0 := by
  have hs : tsupport (testF a) ⊆ Set.Icc (-(2 * a / 2)) (2 * a / 2) := by
    rw [show 2 * a / 2 = a by ring]; exact GRHMiller.Narrow.tsupport_testFnN_subset a
  have hk := tsupport_weilTest_subset hs hs
  apply image_eq_zero_of_notMem_tsupport
  intro hmem
  have := hk hmem
  rw [Set.mem_Icc, ← abs_le] at this
  linarith

lemma kern_real (a u : ℝ) : kern a u = ((kern a u).re : ℂ) := by
  unfold kern testF
  rw [GRHMiller.Narrow.weilTest_testFnN]
  simp

lemma kern_re_nonneg (a u : ℝ) : 0 ≤ (kern a u).re :=
  GRHMiller.Narrow.weilTest_testFnN_re_nonneg a u

/-! ### Sample space and named constants -/

/-- Cutoff `M = ⌊e^{y+2a}⌋ + 1`. -/
def cutoff (a y : ℝ) : ℕ := ⌊Real.exp (y + 2 * a)⌋₊ + 1

/-- Weights `w(n) = Λ(n) k_a(log n − y)/√n`. -/
def wt (a y : ℝ) (n : ℕ) : ℝ :=
  ArithmeticFunction.vonMangoldt n * (kern a (Real.log n - y)).re / Real.sqrt n

/-- Units mod `q` below the cutoff. -/
def sampleSpace (q : ℕ) (a y : ℝ) : Finset ℕ :=
  (range (cutoff a y)).filter fun n ↦ Nat.Coprime n q

/-- Weight of non-units mod `q`. -/
def nonunitWt (q : ℕ) (a y : ℝ) : ℝ :=
  ∑ n ∈ (range (cutoff a y)).filter (fun n ↦ ¬ Nat.Coprime n q), |wt a y n|

/-- Small-prime sum `Σ_{n ≤ e^{2a}} Λ(n) (|k(log n)| + |k(−log n)|)/√n`. -/
def smallPrimes (a : ℝ) : ℝ :=
  ∑ n ∈ range (⌊Real.exp (2 * a)⌋₊ + 1), ArithmeticFunction.vonMangoldt n / Real.sqrt n *
    (‖kern a (Real.log n)‖ + ‖kern a (-Real.log n)‖)

/-- `A(a) = Re k̂(−i/2) = ∫ k(u) e^{u/2} du`. -/
def mainA (a : ℝ) : ℝ := (paperFT (kern a) (-I / 2)).re

/-- `B(a) = Re(k̂(i/2) + k̂(−i/2))`. -/
def poleB (a : ℝ) : ℝ := (poleSide (kern a)).re

/-- Numerator of the bias bound. -/
def sharpNum (q : ℕ) (a y : ℝ) : ℝ :=
  (kern a 0).re * Real.log (q / π) + smallPrimes a +
    (Ilog (testF a) 5 + Ilog (testF a) (1 / 2)) / (2 * π) + nonunitWt q a y

/-- Denominator of the bias bound. -/
def sharpDen (q : ℕ) (a y : ℝ) : ℝ :=
  Real.exp (y / 2) * mainA a - poleB a -
    (Ilog (testF a) (5 + Real.log π) + Ilog (testF a) (1 / 2)) / (2 * π) - nonunitWt q a y

/-! ### Auxiliary positivity -/

lemma re_paperFT_I_half_nonneg (a : ℝ) : 0 ≤ (paperFT (kern a) (I / 2)).re := by
  have hk : Continuous (kern a) :=
    (weilTest_contDiff (contDiff_testF a) (contDiff_testF a).continuous
      (hasCompactSupport_testF a)).continuous
  have hks : HasCompactSupport (kern a) :=
    weilTest_hasCompactSupport (hasCompactSupport_testF a) (hasCompactSupport_testF a)
  have hpt : ∀ u : ℝ, kern a u * Complex.exp (I * (I / 2) * (u : ℂ)) =
      (((kern a u).re * Real.exp (-u / 2) : ℝ) : ℂ) := by
    intro u
    rw [kern_real a u]
    have : I * (I / 2) * (u : ℂ) = ((-u / 2 : ℝ) : ℂ) := by
      push_cast; ring_nf; rw [I_sq]; ring
    rw [this, ← Complex.ofReal_exp]
    push_cast; simp
  unfold paperFT
  simp_rw [hpt]
  rw [integral_complex_ofReal, Complex.ofReal_re]
  exact integral_nonneg fun u ↦ mul_nonneg (kern_re_nonneg a u) (Real.exp_pos _).le

lemma re_primeSideZeta_kern_nonneg (a : ℝ) : 0 ≤ (primeSideZeta (kern a)).re := by
  rw [primeSideZeta_eq, primeSide_eq_sum (L := 2 * a) _ fun u hu ↦ kern_eq_zero hu,
    Complex.re_sum]
  refine sum_nonneg fun n _ ↦ ?_
  simp only [map_one, one_mul]
  rw [Complex.re_ofReal_mul, Complex.add_re]
  exact mul_nonneg (div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _))
    (add_nonneg (kern_re_nonneg _ _) (kern_re_nonneg _ _))

/-! ### The theorem -/

variable {q : ℕ} [NeZero q]

/-- **Sharp bounds (Layer 1):** the character sum is at most `sharpNum` and the mass is at least
`sharpDen`. -/
theorem sharp_charSum_mass (hZ : GRHMiller.DirichletLZerosOnLine) (hRH : RiemannHypothesis)
    {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) {a y : ℝ} (ha : 0 ≤ a) (hy : 2 * a < y) :
    ‖charSum (sampleSpace q a y) (wt a y) χ‖ ≤ sharpNum q a y ∧
      sharpDen q a y ≤ mass (sampleSpace q a y) (wt a y) := by
  set f := testF a with hfdef
  have hf : ContDiff ℝ 2 f := contDiff_testF a
  have hfs : HasCompactSupport f := hasCompactSupport_testF a
  set k := kern a with hkdef
  set M := cutoff a y
  have hk_eq : weilTest f f = k := rfl
  have hK : ∀ u, 2 * a < |u| → k u = 0 := fun u hu ↦ kern_eq_zero hu
  have hky : k (-y) = 0 := hK _ (by rw [abs_neg, abs_of_pos (by linarith)]; exact hy)
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
  set T := primeSide (coeff χ') (twist k y)
  have hTsum : T = ∑ n ∈ range M, ((wt a y n : ℝ) : ℂ) * χ' n := by
    show primeSide (coeff χ') (twist k y) = _
    rw [primeSide_twist_eq_sum (L := 2 * a) _ hK hy]
    refine sum_congr rfl fun n _ ↦ ?_
    simp only [coeff, wt]
    rw [show k (Real.log n - y) = (((kern a (Real.log n - y)).re : ℝ) : ℂ) from kern_real a _]
    push_cast; ring
  -- character sum over units = T − (non-units)
  have hsplit : charSum (sampleSpace q a y) (wt a y) χ =
      T - ∑ n ∈ (range M).filter (fun n ↦ ¬ Nat.Coprime n q), ((wt a y n : ℝ) : ℂ) * χ' n := by
    rw [hTsum, ← sum_filter_add_sum_filter_not (range M) (fun n ↦ Nat.Coprime n q), add_sub_cancel_right]
    unfold charSum sampleSpace
    refine sum_congr rfl fun n hn ↦ ?_
    rw [hcop n (mem_filter.mp hn).2]
  have hnonunit : ‖∑ n ∈ (range M).filter (fun n ↦ ¬ Nat.Coprime n q),
      ((wt a y n : ℝ) : ℂ) * χ' n‖ ≤ nonunitWt q a y := by
    refine (norm_sum_le _ _).trans (sum_le_sum fun n _ ↦ ?_)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_of_le_one_right (abs_nonneg _) (χ'.norm_le_one _)
  -- bound on T
  have hparity : parity χ' ≤ 1 := by unfold parity; split_ifs <;> norm_num
  have hT := norm_primeSide_twist_le hZ hq' hprim hf hfs y
  have hΓy := norm_gammaSide_twist_le hf hfs hparity (q := χ.conductor) hky
  have hΓ0 := re_gammaSide_le hf hfs hparity (q := χ.conductor)
  rw [hk_eq] at hT hΓy hΓ0
  have hP0 : -(primeSide (coeff χ') k).re ≤ smallPrimes a := by
    rw [primeSide_eq_sum (L := 2 * a) _ hK]
    refine (neg_le_abs _).trans ((Complex.abs_re_le_norm _).trans ((norm_sum_le _ _).trans
      (sum_le_sum fun n _ ↦ ?_)))
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _))]
    refine mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans (add_le_add ?_ ?_))
      (div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _))
    · rw [norm_mul]; exact mul_le_of_le_one_left (norm_nonneg _) (χ'.norm_le_one _)
    · rw [norm_mul, Complex.norm_conj]; exact mul_le_of_le_one_left (norm_nonneg _) (χ'.norm_le_one _)
  have hlogq : (k 0).re * Real.log (χ.conductor / π) ≤ (k 0).re * Real.log (q / π) := by
    refine mul_le_mul_of_nonneg_left ?_ (kern_re_nonneg a 0)
    have hc : (0 : ℝ) < χ.conductor := by exact_mod_cast Nat.pos_of_ne_zero χ.conductor_ne_zero
    apply Real.log_le_log (div_pos hc Real.pi_pos)
    apply div_le_div_of_nonneg_right _ Real.pi_pos.le
    exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne q)) χ.conductor_dvd_level
  have hnum : ‖charSum (sampleSpace q a y) (wt a y) χ‖ ≤ sharpNum q a y := by
    rw [hsplit]
    refine (norm_sub_le _ _).trans ?_
    unfold sharpNum
    rw [← hkdef, ← hfdef]
    have hT' := hT
    rw [Complex.sub_re] at hT'
    have hTT : ‖T‖ = ‖primeSide (coeff χ') (twist k y)‖ := rfl
    have hdiv : (Ilog f 5 + Ilog f (1 / 2)) / (2 * π) = Ilog f 5 / (2 * π) + Ilog f (1 / 2) / (2 * π) :=
      add_div _ _ _
    linarith
  -- mass
  have hmassSplit : mass (sampleSpace q a y) (wt a y) =
      ∑ n ∈ range M, wt a y n -
        ∑ n ∈ (range M).filter (fun n ↦ ¬ Nat.Coprime n q), wt a y n := by
    unfold mass sampleSpace
    rw [← sum_filter_add_sum_filter_not (range M) (fun n ↦ Nat.Coprime n q), add_sub_cancel_right]
  have hnon' : ∑ n ∈ (range M).filter (fun n ↦ ¬ Nat.Coprime n q), wt a y n ≤ nonunitWt q a y :=
    sum_le_sum fun n _ ↦ le_abs_self _
  have hall : ∑ n ∈ range M, wt a y n = (primeSideZeta (twist k y)).re := by
    rw [primeSideZeta_eq, primeSide_twist_eq_sum (L := 2 * a) _ hK hy, Complex.re_sum]
    refine sum_congr rfl fun n _ ↦ ?_
    simp only [wt, one_mul]
    rw [Complex.re_ofReal_mul]
    ring
  obtain ⟨E, hE, hPζ⟩ := primeSideZeta_twist_eq hRH hf hfs y
  have hΓζy := norm_gammaSideZeta_twist_le hf hfs y
  have hΓζ0 := re_gammaSideZeta_le hf hfs
  rw [hk_eq] at hE hPζ hΓζy hΓζ0
  have hpole := poleSide_twist k y
  have hA' := re_paperFT_I_half_nonneg a
  have hPζ0 := re_primeSideZeta_kern_nonneg a
  rw [← hkdef] at hA' hPζ0
  have hmass : sharpDen q a y ≤ mass (sampleSpace q a y) (wt a y) := by
    rw [hmassSplit, hall, hPζ, Complex.sub_re, Complex.add_re, hpole, Complex.add_re,
      Complex.re_ofReal_mul, Complex.re_ofReal_mul]
    have h1 := Complex.re_le_norm (gammaSideZeta (twist k y))
    have h2 := Complex.re_le_norm E
    have h1' := neg_le_abs (gammaSideZeta (twist k y)).re
    have h1'' := Complex.abs_re_le_norm (gammaSideZeta (twist k y))
    have hexp : 0 ≤ Real.exp (-y / 2) * (paperFT k (I / 2)).re :=
      mul_nonneg (Real.exp_pos _).le hA'
    unfold sharpDen mainA poleB
    rw [← hkdef, ← hfdef]
    rw [Complex.add_re, Complex.sub_re] at hE
    have hdiv : (Ilog f (5 + Real.log π) + Ilog f (1 / 2)) / (2 * π) =
        Ilog f (5 + Real.log π) / (2 * π) + Ilog f (1 / 2) / (2 * π) := add_div _ _ _
    have hpole0 : (poleSide k).re = (paperFT k (I / 2)).re + (paperFT k (-I / 2)).re := by
      unfold poleSide; rw [Complex.add_re]
    linarith
  exact ⟨hnum, hmass⟩

/-- **Sharp bias theorem (Layer 1).** -/
theorem bias_sharp (hZ : GRHMiller.DirichletLZerosOnLine) (hRH : RiemannHypothesis)
    {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) {a y : ℝ} (ha : 0 ≤ a) (hy : 2 * a < y)
    (hden : 0 < sharpDen q a y) :
    bias (sampleSpace q a y) (wt a y) χ ≤ sharpNum q a y / sharpDen q a y := by
  obtain ⟨hnum, hmass⟩ := sharp_charSum_mass hZ hRH hχ ha hy
  exact bias_le_of_bounds _ _ _ hnum hden hmass

end GRHPseudo.Sharp
