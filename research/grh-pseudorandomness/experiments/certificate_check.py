"""Exact bias of the measure in `bias_le_half_of_le_two_pow_64` (a = 1, x = 22500) for some prime q.

The theorem guarantees bias <= 1/2 for every q <= 2^64; this shows the actual values (FFT).
"""
import math, sys
import numpy as np
sys.path.insert(0, "experiments")
from prime_bias import dlog_table, von_mangoldt_upto
from sharp_certified import st

a, y = 1.0, 2 * math.log(150)
t = np.linspace(-a, a, 20001); dt = t[1] - t[0]
f = np.cosh(t / 2) * st(64 * (a - t)) * st(64 * (a + t))
U = np.linspace(-2 * a, 2 * a, 4001)
K = np.array([np.sum(f * np.interp(t - u, t, f, left=0.0, right=0.0)) * dt for u in U])
hi = int(math.floor(math.exp(y + 2 * a)))
lam = von_mangoldt_upto(hi)
print(f"support: n <= {hi}; weighted window [{math.exp(y - 2*a):.0f}, {math.exp(y + 2*a):.0f}]")
print("q\tbias\tguarantee")
for q in (10007, 100003, 1000003, 4000037):
    L = dlog_table(q)
    v = np.zeros(q - 1)
    ns = np.nonzero(lam)[0]
    ns = ns[(ns % q) != 0]
    w = lam[ns] * np.interp(np.log(ns) - y, U, K, left=0.0, right=0.0) / np.sqrt(ns)
    np.add.at(v, L[ns % q], w)
    b = float(np.max(np.abs(np.fft.fft(v / v.sum()))[1:]))
    print(f"{q}\t{b:.4f}\t0.5")
