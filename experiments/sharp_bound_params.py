"""Certified parameters of the planned sharp bound (explicit formula + positivity, cosh kernel).

bias <= [k0 log(q/pi) + 2 S(a) + 2 G(a)] / M,   M ~ sqrt(x) (a + sinh a)^2 - lower order,
k0 = a + sinh a, S(a) = sum_{n <= e^{2a}} Lambda(n) k_a(log n)/sqrt n, G(a) = (1/2pi) int |f^|^2 |Re psi|.
Lower-order terms in M are ignored here (they are O(k0 (1 + log)) and handled in the proof).
Support of the measure: n in [x e^{-2a}, x e^{2a}]; we report X = x e^{2a}.
"""
import math, sys
sys.path.insert(0, "experiments")
from cosh_kernel_check import k_a, fhat_sq
from scipy_free_digamma import digamma
from prime_bias import von_mangoldt_upto
import numpy as np

def G(a):
    ts = np.linspace(-400, 400, 200001)
    best = 0
    for kappa in (0, 1):
        v = [fhat_sq(t, a) * abs(digamma(complex((0.5 + kappa) / 2, t / 2)).real) for t in ts]
        best = max(best, np.trapezoid(v, ts) / (2 * math.pi))
    return best

def S(a):
    lam = von_mangoldt_upto(int(math.exp(2 * a)) + 1)
    return sum(lam[n] * k_a(math.log(n), a) / math.sqrt(n) for n in range(2, len(lam)))

print("qbits\teps\tbest_a\tx\tX=x*e^{2a}\tlog2(X)\tX/(log q)^2\t(formal-route N)")
formal = {16: {0.5: 6.921e14}, 64: {0.5: 9.693e15, 0.1: 3.516e17, 0.01: 5.646e19}, 1024: {0.5: 3.878e18}}
cache = {}
for qbits in (16, 64, 1024):
    lq = qbits * math.log(2)
    for eps in (0.5, 0.1, 0.01):
        best = None
        for a in [0.5 + 0.25 * i for i in range(14)]:
            if a not in cache:
                cache[a] = (a + math.sinh(a), S(a), G(a))
            k0, s, g = cache[a]
            num = k0 * (lq - math.log(math.pi)) + 2 * s + 2 * g
            x = (num / (eps * k0 ** 2)) ** 2
            x = max(x, math.exp(2 * a) * 1.01)
            X = x * math.exp(2 * a)
            if best is None or X < best[2]:
                best = (a, x, X)
        a, x, X = best
        f = formal.get(qbits, {}).get(eps, float('nan'))
        print(f"{qbits}\t{eps}\t{a}\t{x:.3e}\t{X:.3e}\t{math.log2(X):.1f}\t{X/lq**2:.1f}\t{f:.1e}")
