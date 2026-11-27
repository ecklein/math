# Directions for making the project more novel (brainstorm, 2026-11-27)

## Where the current results stand

These are the starting points for the directions below.
- The leading term of Thm 4 is, asymptotically, Lemma 6.1 of Lamzouri–Li–Soundararajan (LLS 2015). Our
  contribution there is the fully explicit, formally verified version and the q ≤ 2⁶⁴ certificate.
- Our kernel optimality (Prop 7, c* = 2/a*² ≈ 1.2236) holds only among *positive-definite* kernels,
  which are automatically even.
- The (log q)² support barrier is untouched, and is likely untouchable with GRH alone.

## Ranked directions

### 1. Beyond positivity: the optimal nonnegative kernel (most promising)
**Idea.** Only k ≥ 0 is needed for the weights to form a probability measure. Positive-definiteness was a
convenience: it bounds the zero sum by positivity. LLS bound it instead by Σ_γ|k̂(γ)| ≈ (log q/2π)∫|k̂|, which
allows *asymmetric* nonnegative kernels. Because the main term weights the window by e^{u/2}, mass near the
top of the window pays off.

**Extremal problem.**
```
R(a) = inf { (1/2π)∫|k̂| / ∫k(u)e^{u/2}du : k ≥ 0, supp k ⊆ [−2a, 2a] }
c(a) = e^a R(a)
```
Here c(a) is the support-normalized constant: bias ≈ c log q/√X.

**Numerical evidence** (`experiments/kernel_lp.py`, an LP over piecewise-linear k ≥ 0; stable under
doubling the resolution and extending the |k̂| integral to t = 4000):

| a | c(a), nonnegative (LP) | c_PD(a) = e^a/(a + sinh a) |
|---|---|---|
| 1.0 | 1.103 | 1.250 |
| 1.2785 (= a*) | 1.047 | 1.2236 (= c*) |
| 1.5 | 1.024 | 1.235 |
| 2.0 | 1.006 | 1.313 |
| 3.0 | 1.000 | 1.543 |
| 4.0 | 1.002 | 1.745 |

The optimum appears to decrease to **1** as a grows. The optimal kernels are asymmetric: at a = 3, 44% of
the mass lies in the top quarter of the window. Smaller a (e.g. 0.75) is not resolved by the current
discretization: the LP value and the exact value of its solution disagree there.

**Candidate theorems.**
- (1a) c(a) → 1 as a → ∞, with an explicit near-extremal family.
- (1b) The matching barrier: c(a) ≥ 1 − o(1) for every nonnegative kernel. That would make 1 the exact
  limit of the explicit-formula method for prime-supported small-bias sets, i.e. support
  (1 + o(1)) log²q/ε² against our current 1.497.

A proof route for (1b) is duality. For k ≥ 0 and any φ ≥ e^{u/2} on [−2a, 2a],
∫k e^{u/2} ≤ ∫kφ ≤ (1/2π)∫|k̂|·sup|φ̂|. So R(a) ≥ 1/inf{sup|φ̂| : φ ≥ e^{u/2} on [−2a, 2a]}, a Beurling-type
majorant problem.

**Prior art (must position against it).** Carneiro–Milinovich–Quesada-Herrera–Ramos (Math. Comp. 2025,
arXiv:2404.08380) recast LLS with general test functions for the *one-sided* least-non-residue problem.
Their extremal constant has the known endpoints C(0) = 2 and C(∞) = 1. They note that the extremizers
change sign and are asymmetric. Our problem differs in three ways: it is two-sided (all characters, a
bias), it requires k ≥ 0 so that k defines a measure, and it fixes the support. A limit of 1 matching their
C(∞) = 1 is suggestive, so check whether their methods give (1a)/(1b) directly. Our trivial bound is
c ≥ e^a/(4 sinh a) → 1/2, which is far from the numerics.

**Formal path.** Turning this into explicit, verified theorems needs an explicit bound on Σ_γ |k̂(γ)|, i.e.
explicit local zero counts for L(s, χ), uniform in q. The ported zeta-23 library has
`ThmE/LocalCountChi` and `CountByIntegralChi`: check what they state. This is the main formal cost.
**Value: high** (a new extremal theorem with a clean answer, plus an improved certified constant).

### 2. Unconditional results for almost all moduli (clarifies what GRH buys)
For all but o(Q) moduli q ≤ Q, primes p ≤ (log Q)^{2+o(1)} ε^{−4} should be ε-biased *unconditionally*. The
route is moments of the large sieve over (q, χ) in the style of Duke–Kowalski: a back-of-envelope count gives
the (log Q)² scale with an ε^{−4} loss. This would make the story "GRH is needed only for the worst-case
moduli". The prior-art check found no small-bias or expander version stated, though the method is
classical. **Value: medium**, as a section or short companion paper; informal at first.
**Update (2026-11-27): precursor exists.** JMV §1 already notes unconditional expansion outside a sparse set of moduli via the
large sieve (Garaev, Thm 3). Pursue only with a quantitatively stronger target (exceptional-set size, support exponent, explicit
constants). **Value lowered to low–medium.**

### 3. Explicit nonabelian expanders: the affine group Aff(ℤ/pℤ)
Generators: multiplication by small primes, and translation by ±1. The semidirect-product/zig-zag theorem
of Alon–Lubotzky–Wigderson combines our q ≤ 2⁶⁴ (or general) bias bound for (ℤ/pℤ)^× with the
(near-complete) orbit graph on ℤ/p. That gives explicit polylog-degree expanders on Aff(ℤ/pℤ), unconditional
now. No prior art found for this specific construction. Composite q needs care: for even q, the unit orbit
graph on ℤ/q is bipartite-like. **Value: medium** (breadth; direct application, explicit parameters).

### 4. Certified samplers: formal expander-walk Chernoff and hitting bounds in Lean
These are formalized in Isabelle (Karayel, AFP "Expander_Graphs", 2023) but essentially absent from Lean
and Mathlib. Porting them and combining with Cor 6 would give a machine-checked sampler on (ℤ/qℤ)^× for
every 64-bit q: explicit seed length, walk length and error. **Value: medium** (formal and practical; the
mathematics is not new).

### 5. Engineering improvements (lower novelty, quick wins)
- Tighten the closed form, which loses about 4× in support against the quadrature constants. Use the
  actual Λ(n), k(log n) values in the small-prime term and sharper Fourier-decay constants.
- Certify more instances (q ≤ 2¹⁰²⁴; ε = 0.01).
- Formalize the L² instance of Prop 7.

### Not recommended
- Breaking the (log q)² barrier for all q. It is equivalent in strength to improving the GRH bound on the
  least prime outside a subgroup.
- Bias for G_q^m via monomial constructions (failed approach F4).
- SLP squareness as a headline result (already known; F5).

## Suggested plan
1. Direction 1, numerically and informally: refine the LP (wider a range, find the shape of the optimal
   kernels, and test the duality lower bound numerically). Then read CMQR closely to see what transfers,
   and attempt (1a) and (1b).
2. If (1a)/(1b) hold, decide on the formal route: explicit zero counting for L(s, χ) via the zeta-23 local
   count modules.
3. Directions 2–3 make natural extra sections for the paper. Direction 4 is a separate formal deliverable.

## Update (2026-11-27, later): direction 1 resolved, with a correction

Checks are in `experiments/barrier_check.py` and `experiments/kernel_lp.py`.

1. **Barrier, valid for every kernel (nonnegative or not, positive-definite or not).** Shift the window so
   its top is at 0, so supp g ⊆ (−∞, 0]. Then ĝ extends to an H¹ function on the lower half-plane, and the
   main term is ∫g e^{v/2} = ĝ(−i/2). The sharp point evaluation |F(x − iy)| ≤ ‖F‖₁/(4πy) at y = 1/2 gives
   ∫g e^{v/2} ≤ (1/2π)∫|ĝ|, i.e. **c ≥ 1**. Numerically, 40 random kernels gave a minimum ratio of 3.41.
2. **Equality holds for g(v) = |v| e^{v/2} (v ≤ 0)**, i.e. the weights Λ(n) log(X/n)/√X on n ≤ X. This is
   the **classical Riesz weight**, used by Bach and by LLS (Lemma 2.2). So the limit c = 1 is attained by a
   classical weight, and that part is not new.
3. **Convolution squares.** g = e ⋆ e with e = e^{v/2} on v ≤ 0, so |ĝ| = |ê|² = (e ⋆ ẽ)^, which is
   positive definite. For any f, the zero sum of f ⋆ f is therefore majorized by that of f ⋆ f̃: our
   positivity argument applies **unchanged** to convolution squares. Cauchy–Schwarz gives the best one on a
   window of length L: f = e^{t/2} on [−L/2, 0], with c(L) = 1/(1 − e^{−L/2}) (1.157 at L = 4, 1.019 at
   L = 8). The numerics match to within 0.1%.
4. **The full ordering.** General nonnegative kernels (LP) do slightly better at finite L: 1 < c_LP(L) <
   c_conv(L), e.g. 1.103 < 1.157 at L = 4 and 1.006 < 1.019 at L = 8. All converge to 1.

**Correction to the paper.** The abstract and introduction say the cosh kernel is optimal "within the
positivity method" and that "no kernel does better within this method". That is **wrong as framed**:
convolution squares use the same positivity step and reach c → 1. Prop 7 is correct as literally stated
(among positive-definite kernels k = f ⋆ f̃), but its significance must be restated. The "c* ≈ 1.2236
optimal constant" headline should be replaced by "c = 1 is the sharp limit (H¹ barrier), attained
asymptotically by the classical Riesz weight".

**Novelty, honestly.** The barrier is a one-line consequence of the H¹ point-evaluation inequality. CMQR's
known endpoint C(∞) = 1 for their one-sided problem may come from the same idea; read their proof before
claiming anything. The attaining weight is classical. The practical gain is real: re-basing the explicit
theorem and the certificate on a convolution-square kernel should cut the leading coefficient from 1.2626
(the formal cosh kernel) to about 1.02, so the support for the same bias shrinks by about 1.5×. The Lean
changes are small: the twisted kernel becomes `weilTest f (tilde f)` = f ⋆ f, and the zero-sum majorant
stays the zero sum of f ⋆ f̃.

## Update (2026-11-27, later still): re-base done
The explicit theorem and certificate were re-based on the convolution-square kernel K_A = f_A ⋆ f_A (paper Thm 10,
Cor 11; formal). Support for bias ≤ 1/2 at q ≤ 2⁶⁴ is now n ≤ 48400 (was 166253). The paper's optimality claims are
corrected (Section 6, with a dated note).

## External review (2026-11-27): suggested priorities
1. **Finite-window extremal problem with rigorous certificates.** C(L) = inf over nonnegative K on [−L, 0] of
   (1/2π)∫|K̂| / ∫K e^{u/2}. Questions: is C(L) > 1 for every finite L, the size of C(L) − 1, existence of optimizers. First goal:
   certified primal (upper) and dual (lower) bounds at one L showing a strict improvement over convolution squares. Our LP numbers
   (`kernel_lp.py`) are exploratory only: truncated quadrature, uncertified. Strongest potential for new mathematics.
2. **Optimize the actual finite certificate**, and build a reusable Lean theorem that accepts a kernel certificate, with an optimizer
   that emits independently checked certificates.
3. **Executable sampler with a proved guarantee**: rational weights, finite bits, unit filtering, explicit error and failure bounds,
   then formal operator-norm and mixing consequences.
4. **One distribution for all moduli**: support/entropy needed for a single integer distribution whose conditioning on units is
   small-biased for every q ≤ Q, against q-dependent weights; adversarial moduli.
