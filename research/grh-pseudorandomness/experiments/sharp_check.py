"""Check: exact bias of the bias_sharp measure vs the evaluated bound, for prime q (FFT)."""
import math, sys
import numpy as np
sys.path.insert(0, "experiments")
from prime_bias import dlog_table, von_mangoldt_upto
from sharp_certified import consts, bound, st

def kfun(a, n=20001):
    t = np.linspace(-a, a, n); dt = t[1] - t[0]
    f = np.cosh(t / 2) * st(64 * (a - t)) * st(64 * (a + t))
    return lambda u: float(np.sum(f * np.interp(t - u, t, f, left=0.0, right=0.0)) * dt)

print("q\ta\tx\tbias\tbound\tratio")
for a in (1.0, 1.5):
    c = consts(a); k = kfun(a)
    for q in (10007, 1000003):
        L = dlog_table(q); lq = math.log(q)
        for x in (300.0, 3000.0):
            y = math.log(x)
            if y <= 2 * a: continue
            hi = int(math.exp(y + 2 * a)) + 1
            lam = von_mangoldt_upto(hi)
            v = np.zeros(q - 1); M = 0.0
            for n in range(2, hi + 1):
                if lam[n] > 0 and n % q:
                    w = lam[n] * k(math.log(n) - y) / math.sqrt(n)
                    if w > 0:
                        v[L[n % q]] += w; M += w
            b = float(np.max(np.abs(np.fft.fft(v / M))[1:]))
            B = bound(c, a, lq, y)
            print(f"{q}\t{a}\t{x:.0f}\t{b:.4f}\t{B:.4f}\t{b/B:.3f}")
