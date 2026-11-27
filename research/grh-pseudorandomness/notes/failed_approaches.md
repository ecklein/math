# Failed approaches and barriers

## F1. Beating the (log q)² support barrier with primes
Goal: an explicit ε-biased set for G_q of size (log q)^{1+o(1)} ε^{-2} (Alon–Roichman order).
Obstruction: the explicit formula's error comes from the ~(log q)/(2π) zeros per unit height.
Any weight w on primes gives a guaranteed bias of order log q / √X with support ≈ X / log X.
We checked that spreading the weight over all scales (w(n) ∝ n^{-1/2}) leaves the product
(number of effective zeros) × (per-zero error / main term) unchanged. Beating this is
equivalent in strength to improving the least prime non-residue beyond (log q)², which is open
even under GRH (Montgomery's lower bound is log q log log q). **Abandoned as a goal.**

## F2. Amplification by products of primes or expander walks on the generator set
μ^{*k} has bias λ^k and support |P|^k, so the exponent log(1/λ)/log|supp| is unchanged.
Ta-Shma / Jalan–Moshkovitz amplification gives support |P| · ε^{-2-o(1)}. Direct primes
already achieve X ≈ 4 log² q / ε², i.e. ε^{-2} with only the log q dependence suboptimal.
Amplification helps only the ε-exponent, which is already optimal. **No gain.**

## F3. Integers instead of primes (no primality test)
Uniform n ≤ X has bias at least the density of y-smooth numbers when χ(p) = 1 for p ≤ y, and
Granville–Soundararajan-type behaviour forces X = (log q)^{A(ε)} with A(ε) → ∞ as ε → 0.
Quasi-polynomial in log q for ε = 1/log q. **Worse than primes.**

## F4. Monomial constructions for G_q^m from k < m prime draws
Outputs g_i = Π_j p_j^{a_ij} induce Ĝ^m → Ĝ^k, χ ↦ (Π_i χ_i^{a_ij})_j. This is non-injective
for k < m on any cyclic factor. Integer codes that stay good modulo every small prime are needed
even for k ≥ m. **Shelved:** generic small-bias amplification, not a number-theoretic novelty.

## F5. SLP perfect-square testing as the main result
Randomized test: (N mod p / p) for a random prime p ≤ C (log N)², with log N up to 2^s.
Already in Gaillard–Jindal 2023 (under GRH). Now unconditional, but **not novel**.
Kept as an attributed corollary/remark only.

## F6. Kernel x^s / s³ (weight log²(x/n)) for the formal Perron step
Needs a new Mellin computation. The pinned ecosystem already has the weight (1 − n/N) with
kernel N^s/(s(s+1)) (schoenfeld-rh-lean `perron_weighted_mu`). **Switched weights** in the
formal route. The informal sharp route uses the Weil explicit formula instead.
