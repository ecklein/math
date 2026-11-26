# Novelty assessment

Method: for each candidate we compare it with its closest prior results (see
`literature_review.md`), ask whether it follows trivially, and look for counterexamples and
lower bounds. We do **not** claim uniqueness: the search covered arXiv, Google Scholar and
Semantic Scholar via web search, plus GitHub. MathSciNet and zbMATH were not accessible.

## T1 — explicit, method-optimal spectral gap for prime Cayley graphs on G_q

**Closest results.**
1. Jao–Miller–Venkatesan (2009), K = Q case: |λ| = O(x^{1/2} log(xq)) for primes ≤ x, under GRH,
   with non-explicit constants.
2. Bach (1990) and LLS (2015): explicit *one-sided* statements. The least n or prime outside a
   subgroup is < 2 log² q, resp. ≤ (log q + B(q))². These give connectivity and diameter, not a
   spectral bound. A subgroup-escape statement does not imply small bias.
3. Carneiro–Milinovich–Quesada-Herrera–Ramos (2024): Fourier optimisation of the constant for the
   one-sided least-non-residue problem.
4. grh-miller (2026): the same positivity inequality, one-sided, formalized.

**What would be new.**
- (a) A fully explicit **two-sided** bound on |E_μ χ| valid for every nonprincipal χ mod every q,
  i.e. an explicit second-eigenvalue bound for weighted prime Cayley graphs. The leading
  constant is 2 in the support-normalised form (2 + o(1)) log q / √X.
- (b) The exact optimum of the leading constant over all admissible positive-definite kernels
  with prescribed support, by reduction to a rank-two extremal problem. The extremal
  kernel is cosh(v/2)-based. That test function is the one Ankeny/Bach-type arguments use
  (and grh-miller), but we found no statement that it is *optimal* for the two-sided spectral
  problem, or any computation of the optimal constant there.

**Does it follow trivially?** (a) follows by a known method (the Weil explicit formula plus
positivity), but the two-sided form needs two extra observations. First, the twisted gamma term
vanishes to leading order when the twist lies outside the kernel's support. Second, the
untwisted zero sum is controlled by the same explicit formula at x = 1. These are standard
moves, so honestly (a) is **routine-but-unrecorded**. (b) is short, and to our knowledge new in
this spectral setting. CMQR solve a different extremal problem (one-sided, with sign constraints
on k̂ − ...), with a different answer (0.7615 vs our 2-type constant), so (b) does not follow
from them.

**Counterexamples / lower bounds checked.**
- Alon–Roichman/Welch: any measure with support size S has λ_* ≥ (1 − o(1)) S^{-1/2} when
  S ≪ φ(q). The bound log q/√X is within a factor ≈ √(log q · log X) of this.
- CRT/prescribed-residue constructions give q with λ_* ≥ c log q / X for X ≫ log q, so the
  log q dependence cannot be removed entirely.
- Experiments (`experiments/prime_bias.py`, `adversarial_q.py`): for q ≤ 4·10⁶ the observed
  λ_* √x / log q ranges over 0.39–1.49 across weights.
- `experiments/cosh_kernel_check.py`: in 36 cases (q ≤ 3.8·10⁶, a ∈ {1, 1.5, 2}) the measured bias
  is 0.50–0.74 of the predicted T1(a) bound, with no violation. Primes are
  empirically as good as random multisets (`rand_norm` ≈ 0.85–0.95). This is not evidence that
  the constant 2 is sharp; it reflects only the *method's* limit.

**Verdict.** Accept, with an honest framing: a modest contribution. It consists of an explicit
and formally verified spectral theorem, now unconditional, plus a short optimality lemma. It is
not a new barrier-breaking construction.

## T2 — GRH ⟺ spectral pseudorandomness
Closest: the classical equivalence GRH(χ) ⟺ ψ(x, χ) ≪ x^{1/2+ε} for each fixed χ, and
schoenfeld-rh-lean's formal iff for ζ. New only as a uniform-in-q, pseudorandomness-phrased,
formally verified equivalence. **Accept as secondary.**

## T3 — modulus-oblivious generators, samplers
Closest: standard expander-walk samplers (Gillman, AKS) applied to JMV graphs, and Gaillard–Jindal
for SLP squareness. Novelty: low (packaging and explicit seed accounting). **Accept as
corollaries only, clearly attributed.**

## Rejected
T4 (universal (log q)^{1+o(1)} support) is out of reach (see F1). SLP squareness as a headline
result is known (F5).
