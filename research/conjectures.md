# Candidate theorems

Notation. `G_q = (Z/qZ)^×`. For a probability measure μ on positive integers whose support is
coprime to q, its bias is `λ_*(q, μ) = max_{χ ≠ χ₀ mod q} |E_{n∼μ} χ(n)|`. This is exactly the
second-largest eigenvalue modulus of the weighted Cayley graph Cay(G_q, μ mod q).
Pseudorandomness notion: **ε-bias against the test class of nontrivial multiplicative
characters of G_q**. This is statistical, not cryptographic. Seeds are uniform bit strings,
and outputs are deterministic functions of the seed.

## T1 (selected). Explicit, method-optimal spectral gap for prime Cayley graphs on G_q

Fix a > 0. Let f_a(v) = cosh(v/2) 1_{[−a,a]}(v), k_a = f_a ⋆ f̃_a (supported on [−2a, 2a],
k̂_a = |f̂_a|² ≥ 0), and define
`μ_{q,x,a}(n) ∝ Λ(n) k_a(log(n/x)) n^{-1/2}` on n coprime to q
(support: prime powers in [x e^{−2a}, x e^{2a}]).

**T1(a) (explicit bound).** For all q ≥ 3, all x ≥ x₀(a), and all χ ≠ χ₀ mod q (primitive or not):
`|E_μ χ| ≤ (log(q/π) + G(a) + P(a) + E(x, a, q)) / (√x (a + sinh a))`, where
`G(a) = k_a(0)^{-1} (1/2π) ∫ |f̂_a(t)|² max_κ Re ψ((1/2+κ+it)/2) dt` (negative, about −0.45 to −0.67
for a ∈ [1, 2]), `P(a) = 2 k_a(0)^{-1} Σ_{n ≤ e^{2a}} Λ(n) k_a(log n) n^{-1/2} = (1 + o(1)) e^a`
(the small-prime term), and E the twisted gamma term, which is explicit and → 0 as x → ∞.
*Correction (2026-11-26):* an earlier draft had `2a` in place of P(a). That draft dropped the
`(a − |u|/2) cosh(u/2)` part of k_a. The numerics in `experiments/cosh_kernel_check.py` exposed it.
In support-normalised form, with X = x e^{2a}, a → ∞ and e^a = o(log q):
`λ_*(q, μ) ≤ (2 + o(1)) log q / √X`. Equivalently, X ≥ (4 + o(1)) log² q / ε² gives ε-bias.

**T1(b) (optimality within the positivity method).** For any admissible kernel k, i.e. k
positive definite, C², supported on [−2a, 2a], the leading coefficient that the
positivity-plus-explicit-formula method yields is `k(0) / ∫ k(u) e^{u/2} du`. This is
≥ 1/(a + sinh a), with equality iff k = c · k_a. The proof factors k = f ⋆ f̃ with
supp f ⊂ [−a, a] (Boas–Kac–Krein). The quantity becomes ‖f‖² / (⟨f, e^{v/2}⟩⟨f, e^{−v/2}⟩),
a rank-two quadratic form whose extremal value is (‖α‖‖β‖ + ⟨α, β⟩)/2 = sinh a + a.

Why GRH is essential: all zeros are needed on the line for |Σ_ρ x^{iγ} k̂(γ)| ≤ Σ_ρ k̂(γ).
Without GRH, a zero at β + iγ with β > 1/2 contributes x^{β−1/2} to the bias.
Unconditional polylog-support statements are not known for G_q, since they would imply polylog
least non-residue bounds.

## T1-formal (the first end-to-end formal target). Crude explicit version
For all q ≥ 1, χ ≠ 1 mod q, and integers N ≥ 3:
`|Σ_{n<N} Λ(n) χ(n) (1 − n/N)| ≤ C √N (log N)² log(3q(…))`, with C explicit.
Hence the measure ν_N(n) ∝ Λ(n)(1 − n/N) 1_{(n,q)=1} has `λ_*(q, ν_N) ≤ C' (log N)² log(qN)/√N`.
The route (Borel–Carathéodory, no explicit formula) is entirely on the pinned environment.
See `proof_obligations.md` §A.

## T2. GRH ⟺ spectral pseudorandomness of primes (characterization)
For every ε > 0 there is C_ε such that for all q, all χ ≠ χ₀ and all x:
`|Σ_{n≤x} Λ(n) χ(n)(1 − n/x)| ≤ C_ε x^{1/2+ε} log(q+1)`. This is **equivalent** to
`DirichletLNonvanishingRightOfHalf`. (⇐) is T1-formal. (⇒): a bound of this shape makes
∫_1^∞ S(x) x^{-s-2} dx = (−L'/L)(s)/(s(s+1)) holomorphic on Re s > 1/2 + ε, so L has no zeros
there. This is Landau-type and elementary, but formalizing it as an iff in the style of
`schoenfeld_strict_bound_iff_riemannHypothesis` is new.

## T3. Modulus-oblivious ε-biased generators and samplers, with seed accounting
One explicit distribution on primes ≤ X is simultaneously ε-biased for **every** modulus q with
log q ≤ ℓ, when X ≥ (4 + o(1)) ℓ² / ε². Consequences, with explicit constants:
- Expander-walk sampler (hitting and Chernoff) on G_q with seed log₂ φ(q) + t · log₂(X) bits,
  without factoring q or knowing φ(q).
- Coset hitting: every coset of every subgroup of index m < 1/ε receives mass ≥ (1 − ε(m−1))/m.
- Implicit moduli (SLP-given integers): attributed corollary (Gaillard–Jindal), now unconditional.
Novelty here is mostly in packaging; T3 is a corollary section, not the headline.

## T4 (rejected). Universal (log q)^{1+o(1)} support. See failed_approaches F1.

## Ranking

| | Novelty | Significance | Feasibility | GRH-dependence | Usefulness | Lean difficulty |
|---|---|---|---|---|---|---|
| T1(a,b) sharp | medium | medium | high (informal) | essential | medium | high (needs explicit formula port, ~43k lines) |
| T1-formal | low–medium | medium | high | essential | medium | medium (~1–2k lines, all on pin) |
| T2 iff | medium (as a formal statement) | low–medium | medium | is GRH | low | medium |
| T3 | low | medium | high | essential | high | low–medium |

**Selected:** T1 as the mathematical headline, with T1-formal + T3 as the first end-to-end formal
deliverable. T1(b) is a short, self-contained, fully formalizable lemma (finite-dimensional
Cauchy–Schwarz, apart from the Krein factorization step, which we state as a hypothesis on k
of the form f ⋆ f̃). T2 is second.
