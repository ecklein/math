"""Numerical sanity check of Theorem T1(a) (research/conjectures.md).

Kernel: f_a(v) = cosh(v/2) on [-a, a], k_a = f_a * f_a~, so
    k_a(u) = sinh(a - |u|/2) + (a - |u|/2) cosh(u/2),  |u| <= 2a,
    k_a(0) = a + sinh a,   integral k_a(u) e^{u/2} du = (a + sinh a)^2.
Measure: mu(n) ∝ Lambda(n) k_a(log(n/x)) / sqrt(n), n coprime to q.

Predicted bound (positivity + Weil explicit formula, twisted gamma term dropped):
    |E_mu chi| <= [ k(0) log(q/pi) + G_kappa(a) + 2 sum_n Lambda(n) k(log n)/sqrt n ] / M
where M is the actual total mass and G_kappa(a) = (1/2pi) int |f^(t)|^2 Re psi((1/2+kappa+it)/2) dt.
We take max over kappa in {0,1}. If the measured bias ever exceeds the bound, the derivation
is wrong somewhere. Passing is evidence only, not proof.
"""
import math, sys
import numpy as np
from sympy import primerange
from scipy_free_digamma import re_digamma

sys.path.insert(0, "experiments")
from prime_bias import dlog_table, von_mangoldt_upto


def k_a(u, a):
    u = abs(u)
    if u > 2 * a:
        return 0.0
    return math.sinh(a - u / 2) + (a - u / 2) * math.cosh(u / 2)


def fhat_sq(t, a):
    # f^(t) = int_{-a}^{a} cosh(v/2) e^{itv} dv = sum over +-1/2 of sinh((1/2 +- it)... closed form
    # int e^{(c)v} over [-a,a] = 2 sinh(c a)/c with c = +-1/2 + i t
    tot = 0j
    for s in (0.5, -0.5):
        c = complex(s, t)
        tot += (np.exp(c * a) - np.exp(-c * a)) / c / 2
    return abs(tot) ** 2


def gamma_term(a, kappa):
    ts = np.linspace(-400, 400, 400001)
    vals = np.array([fhat_sq(t, a) * re_digamma(complex((0.5 + kappa) / 2, t / 2)) for t in ts])
    return np.trapezoid(vals, ts) / (2 * math.pi)


def main():
    from sympy import nextprime
    a_vals = [1.0, 1.5, 2.0]
    qs = [10007, 100003, 1000003, 3818929]
    print("a\tq\tx\tbias\tbound\tratio\tk0\tG\tsmallprime")
    for a in a_vals:
        G = max(gamma_term(a, 0), gamma_term(a, 1))
        k0 = a + math.sinh(a)
        for q in qs:
            L = dlog_table(q)
            for x in (200.0, 1000.0, 5000.0):
                if x <= math.exp(2 * a):
                    continue
                hi = int(x * math.exp(2 * a))
                lam = von_mangoldt_upto(hi)
                v = np.zeros(q - 1)
                M = 0.0
                for n in range(2, hi + 1):
                    if lam[n] > 0 and n % q:
                        w = lam[n] * k_a(math.log(n / x), a) / math.sqrt(n)
                        v[L[n % q]] += w
                        M += w
                bias = float(np.max(np.abs(np.fft.fft(v / M))[1:]))
                lam2 = von_mangoldt_upto(int(math.exp(2 * a)) + 1)
                sp = 2 * sum(lam2[n] * k_a(math.log(n), a) / math.sqrt(n)
                             for n in range(2, len(lam2)))
                bound = (k0 * math.log(q / math.pi) + G + sp) / M
                print(f"{a}\t{q}\t{x:.0f}\t{bias:.4f}\t{bound:.4f}\t{bias/bound:.3f}\t{k0:.3f}\t{G:.3f}\t{sp:.3f}")
                sys.stdout.flush()


if __name__ == "__main__":
    main()
