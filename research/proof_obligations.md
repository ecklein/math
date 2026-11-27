# Proof obligations

Each obligation lists: statement, informal proof sketch, inputs, Lean status.
Status legend: `open`, `informal-done`, `lean-stated`, `lean-done` (no `sorry`, axioms audited).

## A. Analytic layer: from zero location to a uniform prime character-sum bound

The GRH dependency gives only `L(s, χ) ≠ 0` for `Re s > 1/2`. Every pseudorandomness statement
needs a bound uniform in the modulus. The route below avoids the explicit formula, zero
counting, Hadamard products and the functional equation. It uses only nonvanishing, a crude
polynomial upper bound for `|L|`, Borel–Carathéodory, and one contour shift.

### A1. Crude upper bound (unconditional)
For `χ ≠ χ₀ mod q`, `σ = Re s > 0`: `|L(s, χ)| ≤ q |s| / σ`.
*Proof.* `A(t) = Σ_{n ≤ t} χ(n)` satisfies `|A(t)| ≤ q` (sum over a full period vanishes).
Partial summation gives `L(s, χ) = s ∫_1^∞ A(t) t^{-s-1} dt` for `σ > 0`, where the right side is
analytic in `σ > 0` and agrees with the Dirichlet series for `σ > 1`. Identity theorem.
*Lean:* **lean-done** for `σ ≥ 1/2` with constant `1 + 4q|s|`: `GRHPseudo.norm_LFunction_le_linear`
(`lean/GRHPseudo/AnalyticNumberTheory/LGrowth.lean`), adapted from the readable GRH edition.

### A2. Value at the centre (unconditional)
For `Re s ≥ 2`: `|log L(s, χ)| ≤ log ζ(2) < 1/2` and `|L'/L(s, χ)| ≤ -ζ'/ζ(2) < 0.57`.
Status: the needed lower bound `‖L(s, χ)‖ ≥ 1/2` on `Re s ≥ 2` is **lean-done**
(`GRHPseudo.one_half_le_norm_LFunction`, via `L(s,χ) L(s,χμ) = 1`).

### A3. Log-derivative bound right of 1/2 (uses GRH)
For `χ ≠ χ₀ mod q`, `0 < δ ≤ 1/2`, `1/2 + δ ≤ σ ≤ 2`, all real `t`:
`|L'/L(σ + i t, χ)| ≤ (c₁/δ²) (log q + log(|t| + 3) + c₂)`.
*Proof.* Take the disc centred at `s₀ = 2 + i t` of radius `R = 3/2 − δ/2`. Its closure lies in
`Re s > 1/2`, where `L` has no zeros (GRH, `χ ≠ 1`), so `f = log L` is holomorphic there with
`f(s₀)` the principal branch from A2. By A1, `Re f = log |L| ≤ log(q |s| / σ) ≤ M :=
log q + log(|t| + 3) + log 8` on the disc (there `σ ≥ 1/2`, `|s| ≤ |t| + 4`). Borel–Carathéodory
for the derivative: on `|s − s₀| ≤ r = 3/2 − δ`,
`|f'(s)| ≤ 2R (M − Re f(s₀)) / (R − r)² ≤ 12 (M + 1/2) / δ²`.
*Variant (A3').* Borel–Carathéodory for `f` itself gives `|log L(s)| ≤ (6/δ)(M + 1)`, losing
only `1/δ`. This is the version to use if the sampler weights primes by `1` rather than `log p`.
*Lean:* **lean-done (conditional on `GRHHyp`)** with explicit constant:
`GRHPseudo.norm_logDeriv_LFunction_le : ‖L'/L(s,χ)‖ ≤ 48/ε² · log(2(1 + 4N(|Im s|+4)))` for
`1/2 + ε ≤ Re s ≤ 2`, `0 < ε ≤ 1`. Uses Mathlib's `Complex.borelCaratheodory` through the vendored
rh-prime-error lemma. Axioms: propext, Classical.choice, Quot.sound.

### A4. Smoothed Perron identity (unconditional)
*Formal route:* weight `(1 − n/N)`, kernel `N^s (1/s − 1/(s+1))`, via schoenfeld-rh-lean's
Mathlib-only `perron_weighted_mu`, vendored in `lean/GRHPseudo/Vendor/Schoenfeld/`. **lean-done.**
For `k ≥ 2`, `c > 1`, `x ≥ 1`, and `a_n` with `Σ |a_n| n^{-c} < ∞`:
`Σ_{n ≤ x} a_n log^k(x/n) = (k!/2πi) ∫_{(c)} F(s) x^s s^{-k-1} ds`, `F(s) = Σ a_n n^{-s}`.
The integral converges absolutely for `k ≥ 1`; `k = 2` makes the contour shift clean.
*Proof.* Termwise, from `(1/2πi) ∫_{(c)} y^s s^{-k-1} ds = log^k(y)/k!` for `y ≥ 1` and `0` for
`y < 1`, by shifting left/right respectively (residue at `s = 0`). Status: open.

### A5. Contour shift (uses A3)
With `a_n = Λ(n) χ(n)`, `F = −L'/L`, shift from `Re s = 2` to `Re s = 1/2 + δ`. No poles in the
strip because `χ ≠ 1` and GRH. Horizontal segments vanish (`|F| ≪ log(q|t|)/δ²`, kernel `|s|^{-3}`).
Result, for `χ ≠ χ₀ mod q`, `x ≥ 3`, `δ = 1/log x`:
`|Σ_{n ≤ x} Λ(n) χ(n) log²(x/n)| ≤ C √x (log x)² (log q + 1)`
with `C` explicit (≈ `e · 12 · ∫ (log(|t|+3)+…) |1/2+δ+it|^{-3} dt / π`, to be computed).
**lean-done (conditional on `GRHHyp`)** in the formal weight:
`GRHPseudo.norm_sum_vonMangoldt_char_le`:
`‖Σ_{0<n<N} χ(n)Λ(n)(1 − n/N)‖ ≤ (48e/π) log²N √N (π log(2+8q) + J)` for all `q ≥ 1`, `χ ≠ 1`,
`N ≥ 3`; `J = ∫ log(4+|t|)/(1+t²) dt ≈ 5.6262` (numerical). The contour shift is
`GRHPseudo.integral_vertical_eq` (from Mathlib's rectangle theorem).

### A6. Main term (unconditional, elementary)
`Σ_{n ≤ x, (n,q)=1} Λ(n) log²(x/n) ≥ 2x − C' √x log² x − log² x · log q` for `x ≥ x₀`.
This needs a Chebyshev-type lower bound `ψ(y) ≥ y − O(√y log² y)` only in integrated form. The
Schoenfeld repository proves `|ψ(x) − x| < √x log² x / (8π)` for `x ≥ 73.2` from RH; a weaker
unconditional `ψ(y) ≥ c y` suffices if we accept constant-factor losses.
**lean-done (elementary):** `massLower_le_mass`, with
`massLower q N = (⌊N/2⌋ log 2 − log(⌊N/2⌋+1))/2 − log q · log₂N`, from Mathlib's `Chebyshev.psi_ge`.
Non-units cost ≤ `log q · log₂N` (`sum_vonMangoldt_nonunit_le`).

## B. Pseudorandomness layer (finite, GRH-independent)

B1. Bias of a weighted measure from A5 + A6. **lean-done (conditional):**
`GRHPseudo.bias_primeMeasure_le`; unconditional form `GRHPseudo.Main.bias_primeMeasure` (pending
the GRH build).
B2. Bias ⇒ second eigenvalue of the weighted Cayley graph on `G_q`. **lean-done** (eigenvector
half): `charSum_eq_eigenvalue`. Completeness of characters as an eigenbasis is not yet stated.
B3. Bias ⇒ density bounds for cosets of subgroups and for arbitrary sets (Parseval).
Status: open.

## C. Candidate-specific obligations
To be filled after candidate selection (see `conjectures.md`, `novelty_assessment.md`).

## D. Sharp route (explicit formula + positivity), for T1(a)

Inputs: zeta-23-lean's `EF_lit_chi_L` (primitive χ, q > 1) and `EF_lit_zetaZeroConfig`, ported
to our pin (`lean/Zeta23/`). grh-miller's `Ankeny.lean` supplies the positivity and gamma-side
lemmas. GRH enters via `DirichletLZerosOnLine` (`LFunction_eq_zero_re`), RH via `riemannHypothesis`.

D1. *Twist.* For `k_y(u) = k(u − y)`: `paperFT k_y z = exp(i z y) · paperFT k z`. **lean-done** (`Sharp.paperFT_twist`).
D2. *Two-sided positivity.* For primitive χ mod q > 1, real f ∈ C_c², supp f ⊆ [−a, a],
    k = weilTest f f, y > 2a, under GRH:
    `|Σ_n Λ(n) χ(n) k(log n − y)/√n| ≤ Re literatureRHSchi(k) + |twisted gamma term|`.
    Proof: EF at k_y; the χ̄-leg vanishes since −log n − y < −2a; `|Σ m e^{iγy}|f̂|²| ≤ Σ m|f̂|²`
    = EF at k. **lean-done (conditional on zeros-on-line)** (`Sharp.norm_primeSide_twist_le`).
D3. *Gamma side.* `Re literatureRHSchi(k) ≤ k(0) log(q/π) + 2 Σ_{n ≤ e^{2a}} Λ(n)|k(log n)|/√n
    + G(f)`, with G explicit via `integral_normSq_paperFT_mul_le`. **lean-done** (`Sharp.GammaBounds`: twisted side ≤ I(5)/2π with the log q part killed by Fourier inversion; untwisted ≤ k(0)log(q/π) + I(1/2)/2π; ζ analogues).
D4. *Main term from RH.* `Σ_n Λ(n) k(log n − y)/√n ≥ e^{y/2} ∫ k(u)e^{u/2} du − (lower order)`,
    via `EF_lit` for ζ, the same positivity, and the pole term `paperFT k_y (−i/2)`. **lean-done (conditional on RH)** (`Sharp.primeSideZeta_twist_eq`).
D5. *Imprimitive reduction.* On n coprime to q, χ = χ* (primitive inducing character, conductor
    q* | q, q* > 1). **lean-done** (inside `Sharp.bias_sharp`, via `primitiveCharacter_apply_of_isCoprime`).
D6. *Assembly.* Bias of μ(n) ∝ Λ(n) k(log(n/x))/√n on units mod q, with the cosh test function
    `testFnN a` (smoothed cutoff, transition width 1/64). **lean-done (Layer 1)**: `Sharp.bias_sharp` proves bias ≤ `sharpNum/sharpDen`.
D7. *Layer 2 (open).* Closed-form bounds on the constants in `sharpNum/sharpDen`: an A(a) lower bound, B(a) = 2A(a) (or an upper bound), I(B) ≤ (C₀²+C₁²)(J + Bπ), J ≤ π(log 4 + 1/√2), and the small-prime sum. Then a machine-checked numeric certificate for chosen (q, ε).
