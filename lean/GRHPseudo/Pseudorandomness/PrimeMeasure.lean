import GRHPseudo.AnalyticNumberTheory.PrimeCharSum
import GRHPseudo.Pseudorandomness.Bias

/-!
# The prime-power sample space and its bias (Theorem T1-formal)

**Sample space.** For a modulus `q` and cutoff `N`, the sample space is the set `S_q(N)` of
`n ∈ (0, N)` coprime to `q`, with weight `w_N(n) = Λ(n) (1 − n/N)`. It is supported on prime
powers `n < N` that are units mod `q`; it does not depend on `χ`, and depends on `q` only through
the coprimality filter.

**Theorem** (`bias_primeMeasure_le`). Assume `GRHHyp`. For `q ≥ 1`, nonprincipal `χ` mod `q`, and
`N ≥ 3` such that `L := (⌊N/2⌋ log 2 − log(⌊N/2⌋ + 1))/2 − log q · log₂ N > 0`,

    bias(S_q(N), w_N, χ) ≤ (48 e/π) log² N √N (π log(2 + 8q) + J) / L.

Mass lower bound: `Σ_{n<N} Λ(n)(1 − n/N) ≥ ψ(⌊N/2⌋)/2` with Mathlib's Chebyshev bound
`psi_ge`. Removing non-units costs at most `log q · log₂ N`, since each non-unit prime power
`n = p^k < N` has `p ∣ q` and `k ≤ log₂ N`.
-/

noncomputable section

open Finset Real ArithmeticFunction

namespace GRHPseudo

/-- Weight `Λ(n)(1 − n/N)`. -/
def primeWeight (N : ℕ) (n : ℕ) : ℝ := Λ n * (1 - (n : ℝ) / N)

/-- `S_q(N)`: integers in `(0, N)` coprime to `q`. -/
def unitSupport (q N : ℕ) : Finset ℕ := (Ioo 0 N).filter fun n ↦ Nat.Coprime n q

lemma primeWeight_nonneg {N n : ℕ} (hn : n ∈ Ioo 0 N) : 0 ≤ primeWeight N n := by
  have hnN : (n : ℝ) < N := by exact_mod_cast (mem_Ioo.mp hn).2
  have hN : (0 : ℝ) < N := lt_of_le_of_lt (Nat.cast_nonneg n) hnN
  unfold primeWeight
  have : (n : ℝ) / N < 1 := (div_lt_one hN).mpr hnN
  exact mul_nonneg vonMangoldt_nonneg (by linarith)

lemma primeWeight_le_vonMangoldt {N n : ℕ} (hn : n ∈ Ioo 0 N) : primeWeight N n ≤ Λ n := by
  unfold primeWeight
  have : 0 ≤ (n : ℝ) / N := by positivity
  nlinarith [vonMangoldt_nonneg (n := n)]

variable {q : ℕ} [NeZero q]

/-- The character sum over units equals the sum over all `n`, since `χ` vanishes on non-units. -/
lemma charSum_unitSupport (χ : DirichletCharacter ℂ q) (N : ℕ) :
    charSum (unitSupport q N) (primeWeight N) χ =
      ∑ n ∈ Ioo 0 N, χ n * (Λ n : ℂ) * (((1 - (n : ℝ) / N : ℝ)) : ℂ) := by
  unfold charSum unitSupport
  rw [sum_filter]
  refine sum_congr rfl fun n _ ↦ ?_
  split_ifs with h
  · simp only [primeWeight, Complex.ofReal_mul]; ring
  · have hu : ¬ IsUnit (n : ZMod q) := by rwa [ZMod.isUnit_iff_coprime]
    simp [MulChar.map_nonunit χ hu]

/-- Lower bound for the full mass. -/
lemma mass_all_ge {N : ℕ} (hN : 2 ≤ N) :
    ((N / 2 : ℕ) * Real.log 2 - Real.log ((N / 2 : ℕ) + 1)) / 2 ≤
      ∑ n ∈ Ioo 0 N, primeWeight N n := by
  have hψ := Chebyshev.psi_ge (N / 2)
  rw [Chebyshev.psi, Nat.floor_natCast] at hψ
  have hsub : Ioc 0 (N / 2) ⊆ Ioo 0 N := by
    intro n hn
    simp only [mem_Ioc, mem_Ioo] at hn ⊢
    exact ⟨hn.1, by omega⟩
  calc ((N / 2 : ℕ) * Real.log 2 - Real.log ((N / 2 : ℕ) + 1)) / 2
      ≤ (∑ n ∈ Ioc 0 (N / 2), Λ n) / 2 := by linarith
    _ = ∑ n ∈ Ioc 0 (N / 2), Λ n * (1 / 2) := by rw [← sum_mul]; ring
    _ ≤ ∑ n ∈ Ioc 0 (N / 2), primeWeight N n := by
        refine sum_le_sum fun n hn ↦ ?_
        unfold primeWeight
        have hn2 : 2 * n ≤ N := by have := (mem_Ioc.mp hn).2; omega
        have hNr : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
        have : (n : ℝ) / N ≤ 1 / 2 := by
          rw [div_le_iff₀ hNr]; have : (2 * n : ℝ) ≤ N := by exact_mod_cast hn2
          linarith
        exact mul_le_mul_of_nonneg_left (by linarith) vonMangoldt_nonneg
    _ ≤ ∑ n ∈ Ioo 0 N, primeWeight N n :=
        sum_le_sum_of_subset_of_nonneg hsub fun n hn _ ↦ primeWeight_nonneg hn

/-- Non-unit prime powers below `N` carry von Mangoldt mass at most `log q · log₂ N`. -/
lemma sum_vonMangoldt_nonunit_le (N : ℕ) :
    ∑ n ∈ (Ioo 0 N).filter (fun n ↦ ¬ Nat.Coprime n q), Λ n ≤ Real.log q * Nat.log 2 N := by
  set T := ((Ioo 0 N).filter (fun n ↦ ¬ Nat.Coprime n q)).filter IsPrimePow
  have hsplit : ∑ n ∈ (Ioo 0 N).filter (fun n ↦ ¬ Nat.Coprime n q), Λ n =
      ∑ n ∈ T, Real.log n.minFac := by
    rw [← sum_filter_of_ne (p := IsPrimePow) (fun n _ h ↦ vonMangoldt_ne_zero_iff.mp h)]
    refine sum_congr rfl fun n hn ↦ ?_
    rw [vonMangoldt_apply, if_pos (mem_filter.mp hn).2]
  rw [hsplit]
  have hmaps : ∀ n ∈ T, n.minFac ∈ q.primeFactors := by
    intro n hn
    rw [mem_filter, mem_filter] at hn
    obtain ⟨⟨-, hcop⟩, hpp⟩ := hn
    have hp : n.minFac.Prime := Nat.minFac_prime (IsPrimePow.ne_one hpp)
    rw [Nat.mem_primeFactors]
    refine ⟨hp, ?_, NeZero.ne q⟩
    -- `n` is a power of `minFac n`; a common factor of `n` and `q` is a power of it
    by_contra hnd
    apply hcop
    have hcop' : Nat.Coprime n.minFac q := (Nat.Prime.coprime_iff_not_dvd hp).mpr hnd
    rw [← hpp.minFac_pow_factorization_eq]
    exact Nat.Coprime.pow_left _ hcop'
  rw [← sum_fiberwise_of_maps_to hmaps]
  have hfib : ∀ p ∈ q.primeFactors,
      ∑ n ∈ T.filter (fun n ↦ n.minFac = p), Real.log n.minFac ≤ Real.log p * Nat.log 2 N := by
    intro p hp
    have hpprime := Nat.prime_of_mem_primeFactors hp
    rw [sum_congr rfl (fun n hn ↦ by rw [(mem_filter.mp hn).2]), sum_const, nsmul_eq_mul]
    rw [mul_comm]
    refine mul_le_mul_of_nonneg_left ?_ (Real.log_nonneg (by exact_mod_cast hpprime.one_le))
    -- the fibre injects into `Icc 1 (log₂ N)` via `n ↦ v_p(n)`
    have hcard : (T.filter (fun n ↦ n.minFac = p)).card ≤ (Icc 1 (Nat.log 2 N)).card := by
      refine card_le_card_of_injOn (fun n ↦ n.factorization p) (fun n hn ↦ ?_) ?_
      · rw [mem_coe, mem_filter, mem_filter, mem_filter, mem_Ioo] at hn
        rw [mem_coe]
        obtain ⟨⟨⟨⟨hn0, hnN⟩, -⟩, hpp⟩, hmin⟩ := hn
        have heq : p ^ n.factorization p = n := by
          rw [← hmin]; exact hpp.minFac_pow_factorization_eq
        have hk : 1 ≤ n.factorization p := by
          by_contra h0
          push_neg at h0
          have : n.factorization p = 0 := by omega
          rw [this, pow_zero] at heq
          exact hpp.ne_one heq.symm
        refine mem_Icc.mpr ⟨hk, ?_⟩
        apply Nat.le_log_of_pow_le one_lt_two
        calc 2 ^ n.factorization p ≤ p ^ n.factorization p :=
              Nat.pow_le_pow_left hpprime.two_le _
          _ = n := heq
          _ ≤ N := hnN.le
      · intro m hm n hn hmn
        rw [mem_coe, mem_filter, mem_filter] at hm hn
        have hm' : p ^ m.factorization p = m := by
          rw [← hm.2]; exact hm.1.2.minFac_pow_factorization_eq
        have hn' : p ^ n.factorization p = n := by
          rw [← hn.2]; exact hn.1.2.minFac_pow_factorization_eq
        simp only at hmn
        rw [← hm', ← hn', hmn]
    rw [Nat.card_Icc, Nat.add_sub_cancel] at hcard
    exact_mod_cast hcard
  calc ∑ p ∈ q.primeFactors, ∑ n ∈ T.filter (fun n ↦ n.minFac = p), Real.log n.minFac
      ≤ ∑ p ∈ q.primeFactors, Real.log p * Nat.log 2 N := sum_le_sum hfib
    _ = Real.log (∏ p ∈ q.primeFactors, (p : ℝ)) * Nat.log 2 N := by
        rw [← sum_mul, Real.log_prod]
        intro p hp
        exact_mod_cast (Nat.prime_of_mem_primeFactors hp).ne_zero
    _ ≤ Real.log q * Nat.log 2 N := by
        refine mul_le_mul_of_nonneg_right ?_ (Nat.cast_nonneg _)
        apply Real.log_le_log
        · exact prod_pos fun p hp ↦ by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).pos
        · rw [← Nat.cast_prod]
          exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne q))
            (Nat.prod_primeFactors_dvd q)

/-- Lower bound for the mass of the unit sample space. -/
def massLower (q N : ℕ) : ℝ :=
  ((N / 2 : ℕ) * Real.log 2 - Real.log ((N / 2 : ℕ) + 1)) / 2 - Real.log q * Nat.log 2 N

lemma massLower_le_mass {N : ℕ} (hN : 2 ≤ N) :
    massLower q N ≤ mass (unitSupport q N) (primeWeight N) := by
  have hall := mass_all_ge hN
  have hnon := sum_vonMangoldt_nonunit_le (q := q) N
  have hsplit : ∑ n ∈ Ioo 0 N, primeWeight N n =
      mass (unitSupport q N) (primeWeight N) +
        ∑ n ∈ (Ioo 0 N).filter (fun n ↦ ¬ Nat.Coprime n q), primeWeight N n := by
    unfold mass unitSupport
    rw [sum_filter_add_sum_filter_not]
  have hle : ∑ n ∈ (Ioo 0 N).filter (fun n ↦ ¬ Nat.Coprime n q), primeWeight N n ≤
      ∑ n ∈ (Ioo 0 N).filter (fun n ↦ ¬ Nat.Coprime n q), Λ n :=
    sum_le_sum fun n hn ↦ primeWeight_le_vonMangoldt (mem_filter.mp hn).1
  unfold massLower
  linarith

/-- The analytic bound of `norm_sum_vonMangoldt_char_le`. -/
def charSumBound (q N : ℕ) : ℝ :=
  48 * Real.exp 1 / Real.pi * Real.log N ^ 2 * Real.sqrt N *
    (Real.pi * Real.log (2 + 8 * q) + Jconst)

/-- **Theorem T1-formal (conditional on GRH).** Explicit bias bound for the prime-power sample
space `S_q(N)` with weights `Λ(n)(1 − n/N)`, uniform over all moduli and all nonprincipal
characters. -/
theorem bias_primeMeasure_le (hGRH : GRHHyp) {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1)
    {N : ℕ} (hN : 3 ≤ N) (hL : 0 < massLower q N) :
    bias (unitSupport q N) (primeWeight N) χ ≤ charSumBound q N / massLower q N := by
  apply bias_le_of_bounds _ _ _ _ hL (massLower_le_mass (by omega))
  rw [charSum_unitSupport]
  exact norm_sum_vonMangoldt_char_le hGRH hχ hN

end GRHPseudo
