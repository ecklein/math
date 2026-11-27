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
  i.e. an explicit second-eigenvalue bound for weighted prime Cayley graphs. In the
  support-normalised form the leading constant is c* = 2/a*² ≈ 1.2236 (a* ≈ 1.2785 the root of
  a = 1 + e^{−a}). An earlier draft said 2, which is only the a → ∞ limit.
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
on k̂ − ...), with a different answer (0.7615 vs our 1.2236), so (b) does not follow
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

## Update (2026-11-27): targeted prior-art re-check

- **Lamzouri–Li–Soundararajan, Lemma 6.1** (arXiv:1309.3595, §6 "Asymptotic bounds"; read in full text).
  - Under GRH, for general kernels K and non-principal χ: Re Σ Λ(n)χ(n)n^{−1/2}K̃(n/x) = θ(1+o(1))(log q/2π)∫|K(it)|dt + O(1 + log q log x/√x).
  - The principal character gives K(1/2)√x.
  - This is the **asymptotic, per-character form of our Theorem 4's leading term**. Our contribution there is narrowed to: fully explicit constants with no o(1), the |·| (not Re) form, the explicit mass bound via RH, the closed form, the certificate, and the formalization.
  - Their §6.2 kernel is the indicator case f = 1_{[−α,α]}.
- **Ernvall-Hytönen–Palojärvi**, Math. Comp. 91 (2022). This is an explicit GRH bound for ψ(x;q,a), uniform in q. A bias bound follows mechanically but with much weaker constants at x ≈ (log q)^{2+δ}. They do not state it.
- **Bach**, as presented by McGown–Treviño (Contemp. Math. 775, 2021, Lemma 7.2): the weight is Λ(n)(n/x)^a log(x/n). It is not cosh, and there is no optimality claim.
- **Kernel optimality** (Proposition 8): no prior statement found. Its scope is positive-definite kernels only.
- **Correction (2026-11-27).** c* is *not* the limit of the method. Convolution squares f ⋆ f (Prop 14) use the same positivity
  step and give c(L) = 1/(1 − e^{−L/2}) → 1. Every kernel has c ≥ 1 (Prop 15, an elementary Fourier identity), with equality in
  the limit for the classical weight Λ(n) log(x/n). Novelty of Prop 15: none claimed. It is a sharp point evaluation, and CMQR's
  one-sided C(∞) = 1 has the same extremal. The modest new content is the observation that convolution squares fit the positivity
  method and reach the limit, which makes explicit constants near 1 possible.
- **Hanke repository**: not found publicly. The same-name repo by UyNewNas only defines GRH.
- **Overall**: modest novelty. The explicit theorem is new as stated but close to known machinery (LLS §6). The optimality lemma appears new but is short. The end-to-end formal verification and certificate are the most distinctive part.

## External review (2026-11-27) and follow-up checks
An external review of `main` @ 162027b found errors in informal claims (fixed on branch `grh-paper-fixes`; see the research
log) and sharpened the prior-art picture. Checked here:
- **JMV** (arXiv HTML v2, read): Thm 1.1 bounds *unnormalized* nontrivial eigenvalues by O(n x^{1/2} log(xq)) with degree
  2 li(x) + O(·); normalized, that is O(x^{−1/2} log x log(qx)). Our abstract had dropped the log x. JMV §1 also notes, citing
  Garaev (Monatsh. Math. 148 (2006), Thm 3; reference seen only in their bibliography), that the large sieve gives unconditional
  expansion outside a sparse set of moduli. **So direction 2 ("almost all moduli") has a clear precursor**; it needs a
  quantitatively stronger target to be worth doing.
- **LLS Lemma 6.1** was corrected (arXiv v3, 8 Dec 2016; corrigendum Math. Comp. 86 (2017) 2551–2554, doi:10.1090/mcom/3261,
  Crossref-verified). The v3 statement still has leading term θ(1 + o(1))(log q/2π)∫|K(it)|dt, so our comparison stands against
  the corrected lemma. LLS v3 §6.1 also records a limitation of their one-sided method via K̃(u) ≤ (1/2π)∫|K(it)|dt; the paper
  now cites it next to Prop 15.
- **CMQR**: the reviewer also identifies the same rational extremizer after a change of conventions (consistent with our note).
- **Framing.** The project is an explicit, formally verified refinement of classical GRH constructions (JMV, LLS). Neither the
  expander construction nor the limiting constant 1 should be advertised as new. The most distinctive parts are the explicit bounds
  and the Lean certificates (n ≤ 48400 for all q ≤ 2⁶⁴); no matching prior result was found, which does not establish priority.

## Second external review (2026-11-27)
- **Certified separation (new candidate result).** At window length 4, a nonnegative piecewise-linear kernel has c ≤ 1.10814
  < 1/(1 − e^{−2}) (Prop. "separation", computer-assisted, two independent interval certificates). This is the first rigorous
  statement that general nonnegative kernels beat convolution squares at a fixed window. The periodization identity is classical in
  substance. **Priority not yet checked**: search CMQR, Carneiro et al. Fourier-optimization papers, and Beurling–Selberg-type
  extremal literature for the one-sided-support, ∫|K̂| / ∫K e^{u/2} problem before claiming it.
- **BKMT (arXiv:2607.08261)**: O(ε⁻² log|G|) weighted sparsifiers for every abelian Cayley graph. With Alon–Roichman this makes clear
  that small cardinality is not a novelty claim; ours are the small integer cutoff, explicit constants uniform in q, the access model
  (no factorization of q), and the formal verification.
