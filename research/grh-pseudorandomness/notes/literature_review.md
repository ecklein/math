# Literature review

Last updated 2026-11-26. Confirmation key: **[O]** page opened during this review,
**[S]** confirmed only via search snippets or secondary citation, **[M]** from memory, not
confirmed. Nothing marked [S] or [M] may be cited in the paper until opened and checked.

## 1. The GRH dependency
- Alpöge (with Claude), Lean proof of RH and GRH for Dirichlet L-functions; announcement
  https://alpo.ge/remark.pdf. Original archive: Lean v4.33.1, Mathlib `0df444a3`
  (leanprover-community/riemann-hypothesis). Compact rewrite: github.com/lsernau/grh-lean
  `72fead10`, Lean v4.35.0, Mathlib `56a00585`. Verification: Sutherland,
  math.mit.edu/~drew/grh and ~drew/shortgrh [O]; Rubinstein,
  math.uwaterloo.ca/~mrubinst/alpoge_claude_grh [O]. See `grh_audit.md`.
- Sutherland, schoenfeld-rh-lean `0e52d7b1` [O via repo]: `|ψ(x) − x| < √x log² x / (8π)` for
  `x ≥ 73.2` ⟺ RH. Contains a Mathlib-only weighted Perron formula `perron_weighted_mu`.

## 2. Explicit GRH bounds for characters and primes
- Bach, *Explicit bounds for primality testing and related problems*, Math. Comp. 55 (1990)
  355–380 [S]. Nontrivial χ mod m with χ(n) = 1 for all n < x forces x < 2 log² m.
- Bach–Sorenson, *Explicit bounds for primes in residue classes*, Math. Comp. 65 (1996)
  1717–1735 [S]. Least prime ≡ a mod q ≤ (1+o(1))(φ(q) log q)².
- Lamzouri–Li–Soundararajan, *Conditional bounds for the least quadratic non-residue and
  related problems*, Math. Comp. 84 (2015) 2391–2412, corrigendum 2017; arXiv:1309.3595 v3 [O].
  Least prime outside a proper subgroup H ≤ G_q is ≤ (log q + B(q))², B(q) = o(log log q).
- Carneiro–Milinovich–Quesada-Herrera–Ramos, *Fourier optimization, the least quadratic
  non-residue, and the least prime in an arithmetic progression*, arXiv:2404.08380 v2 [O].
  limsup n_p/log² p < 0.7615; order-ℓ analogues; the method cannot go below ≈ 0.7596.
  **Closest in spirit to our weight optimisation**, but one-sided (least non-residue), not a
  two-sided bound valid for every character simultaneously.
- Grenié–Molteni, *Explicit smoothed prime ideals theorems under GRH*, Math. Comp. 85 (2016) [S].
- Montgomery, *Topics in Multiplicative Number Theory*, LNM 227 (1971) [S]: under GRH,
  n(q) = Ω(log q log log q) infinitely often. Graham–Ringrose (1990) [S]: unconditionally
  Ω(log q log log log q).
- Kandhil–Languasco–Moree, arXiv:2607.14515 (2026) [O, abstract]: improvements under GRH plus
  pair correlation, so still conditional.

- Lamzouri–Li–Soundararajan, §6 Lemma 6.1 [O, full text]: an asymptotic GRH bound for Σ Λ(n)χ(n)n^{−1/2}K̃(n/x) with general kernels. It gives the leading term of our sharp theorem per character, up to 1 + o(1).
- Ernvall-Hytönen–Palojärvi, Math. Comp. 91 (2022) 1317–1365, doi:10.1090/mcom/3691 [O]: explicit GRH bounds for ψ(x;q,a), uniform in q.
- McGown–Treviño, *The least quadratic non-residue*, Contemp. Math. 775 (2021) 205–231 [O]: exposition of Bach's method, with weight Λ(n)(n/x)^a log(x/n).

## 3. Expanders and small-bias sets
- Jao–Miller–Venkatesan, *Expander graphs based on GRH with an application to elliptic curve
  cryptography*, J. Number Theory 129 (2009) 1491–1504; arXiv:0811.0647 [O]. Cayley graph on a
  ray class group with prime-ideal generators of norm ≤ x: nontrivial eigenvalues
  O(n x^{1/2} log(xq)), absolute but **non-explicit** constants. Over K = Q this is exactly
  G_q with prime generators and needs only Dirichlet GRH. **Closest prior result.**
- Alon–Roichman (1994) [M]: O(log|G|/ε²) random elements are ε-biased.
- Azar–Motwani–Naor (1998) [M]: explicit small-bias for Z_d^n.
- Ajtai–Iwaniec–Komlós–Pintz–Szemerédi, thin set with small Fourier coefficients (1990) [S]:
  explicit small-bias sets in the additive group Z_p.
- Ta-Shma, STOC 2017 [M]: near-optimal ε-balanced codes / small-bias over F_2^n.
- Jalan–Moshkovitz, *Near-optimal Cayley expanders for abelian groups*, FSTTCS 2021;
  arXiv:2105.01149 [S]. Deterministic poly(|G|)-time near-Alon–Roichman expanders for any
  explicitly given abelian group. Unconditional, but it requires the group's structure and runs
  in time polynomial in |G| = φ(q), not in log q.
- Chen–Moore–Russell, RANDOM 2013; arXiv:1304.5010 [S]. Alon–Lubotzky–Wigderson (2001),
  Meshulam–Wigderson (2004), Rozenman–Shalev–Wigderson (2006) [M].
- Chung, *Diameters and eigenvalues*, JAMS 2 (1989) [M] via Katz: unconditional Cayley
  expanders on F_{q^n}^× with generators {g + a}. Finite fields only, not (Z/q)^×.

## 4. Complexity applications already in the literature
- Gaillard–Jindal, arXiv:2304.13605 (2023) [O]: deciding whether an SLP computes a perfect square
  is in coRP **under GRH**. Only the quadratic Dirichlet character χ_a is needed, so the result is
  now unconditional. That is an existing result becoming unconditional, **not new**.
- Balaji–Nosan–Shirmohammadi–Worrell, *Identity testing for radical expressions*, LICS 2022;
  arXiv:2202.07961 [O, abstract]: 2-RIT ∈ coRP under GRH (multiquadratic, hence abelian, fields).
  Likely unconditional now; the exact Chebotarev form still needs checking.
- Bläser–Dörfler–Jindal, FSTTCS 2024; arXiv:2403.00115 [S]: squareness of SLP *polynomials* is in
  coRP unconditionally.

## 5. Formalizations after the GRH announcement (2026-11-20 to 11-26)
- amrehan/grh-miller v1.0.0 [O, cloned]: Lean formalization of Bach's constant 2
  (`Bach.bach_char`), Miller's test with Bach's bound, Ankeny with constant 270, and RH for
  abelian Dedekind zeta. Built on anthropics/zeta-23-lean (Weil explicit formula for primitive
  χ, Lean v4.33.0-rc2, Mathlib `51e6992e`) and the *original* Alpöge archive. **Our results
  must not duplicate these.** Its positivity method (`master_inequality`, test function
  cosh(t/2)·cutoff) is one-sided.
- mizar/PseudoPrimeLean [O, README]: GRH as a hypothesis; Miller–Rabin with prime bases.
- rh-prime-error (Lean v4.35.0, Mathlib `56a00585`) [via repo]: Borel–Carathéodory-based
  log-derivative lemma `norm_deriv_div_le_of_forall_mem_ball_ne_zero`.
- PrimeNumberTheoremAnd at commit `a4fb6989` (same pin) [via repo]: vertical line shift
  `verticalIntegral_eq_verticalIntegral`.
- Blogs: Tao (2026-11-20) and Aaronson (2026-11-20) [O] discuss no pseudorandomness consequences.
  No arXiv paper found in this window on expanders, small-bias or derandomization via the proof.

## Gaps identified
1. No explicit-constant spectral-gap theorem for the prime Cayley graph on G_q (JMV is
   non-explicit), and no analysis of which weights are optimal for the **two-sided, all-
   character** bias, as opposed to the one-sided least-non-residue problem.
2. No formalized uniform bound on prime character sums Σ Λ(n)χ(n)w(n) (two-sided). grh-miller
   formalizes only the one-sided consequence.
3. No formal statement linking GRH to a pseudorandomness property in both directions.

## Added 2026-11-27 (after external review)
- **[O]** Lamzouri–Li–Soundararajan, arXiv:1309.3595v3 (8 Dec 2016): corrected Lemma 6.1 (same leading term), §6.1 limitation of the method, §6.2–6.3 kernels (indicator square; Γ(s+1/2)), Lemma 2.2 (S(x,χ) = Σ Λ(n)χ(n) log(x/n)). Text extracted from the PDF.
- **[S]** Lamzouri–Li–Soundararajan, Corrigendum, Math. Comp. 86 (2017), no. 307, 2551–2554, doi:10.1090/mcom/3261: Crossref metadata only; content taken from v3.
- **[O]** Jao–Miller–Venkatesan, arXiv:0811.0647v2 (HTML), J. Number Theory 129 (2009) 1491–1504: Thm 1.1 (unnormalized eigenvalues O(n x^{1/2} log(xq)), degree 2 li(x) + O(·)); §1 remark on unconditional expansion for almost all q via Garaev.
- **[S]** Garaev, Character sums in short intervals and the multiplication table modulo a large prime, Monatsh. Math. 148 (2006) 127–138, Thm 3: seen only as JMV's reference.
- **[O]** Basu–Kothari–Meka–Tudose, *Optimal Sparsifiers for Abelian Cayley Graphs*, arXiv:2607.08261 v2 (3 Nov 2026), abstract and Thm 1.5 (HTML): O(ε⁻² log|G|)-generator ε-Cayley sparsifiers, randomized poly(|G|, ε⁻¹) time.
- **[O]** Carneiro–Milinovich–Quesada-Herrera–Ramos, arXiv:2404.08380 v2: EP1 (C(A), A ∈ [0, ∞]), EP2 (dual), Thm 4 (C_c^∞ suffices; C(0) = 2, C(∞) = 1), §2.2 smoothing. Text extracted from the PDF.
- **[O]** Brevig–Chirre–Ortega-Cerdà–Seip, *Point evaluation in Paley–Wiener spaces*, J. Anal. Math. 153 (2024) 595–670, doi:10.1007/s11854-024-0338-z (Crossref-verified); read arXiv v4, esp. §9.2 (point evaluation on the imaginary axis, (9.2), Conjecture 9.3).
- **[O]** Quesada-Herrera, *Fourier optimization and consequences of GRH*, arXiv:2411.05095 (survey of CMQR's EP).
- **[S]** Hörmander–Bernhardsson, An extension of Bohr's inequality (1993); Korevaar, Nieuw Arch. Wiskunde (2) 23 (1949) 55–62; Bondarenko–Ortega-Cerdà–Radchenko–Seip, arXiv:2504.05205: seen via BCOS's bibliography and search results only; cite via BCOS.
