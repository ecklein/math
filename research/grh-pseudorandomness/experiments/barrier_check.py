"""Checks for direction 1 (notes/directions.md), numerics only.

(i) H^1 barrier: for g supported in (-inf, 0],  int g(v) e^{v/2} dv <= (1/2pi) int |g^(t)| dt,
    with equality for g(v) = |v| e^{v/2}. Tested on random piecewise-linear g (any sign).
(ii) Convolution squares f*f with f = e^{t/2} on [-L/2, 0] (window length L): ratio
     c = (1/2pi) int |g^| / int g e^{v/2} = 1/(1 - e^{-L/2}).
"""
import math
import numpy as np

def ratio(v, g):
    h = v[1] - v[0]
    t = np.linspace(0, 400, 160001)
    env = h * np.sinc(t * h / (2 * np.pi)) ** 2
    G = env * (np.exp(1j * np.outer(t, v)) @ g)
    l1 = 2 * np.trapezoid(np.abs(G), t) / (2 * np.pi)
    mass = np.sum(g * np.exp(v / 2)) * h * (math.sinh(h / 4) / (h / 4)) ** 2
    return l1 / mass

rng = np.random.default_rng(1)
print("(i) random kernels on [-L,0], ratio must be >= 1:")
worst = 1e9
for trial in range(40):
    L = rng.uniform(1, 12)
    v = np.linspace(-L, 0, 161)
    g = rng.normal(size=v.size); g[0] = g[-1] = 0
    if rng.random() < 0.5: g = np.abs(g)            # half nonnegative, half signed
    g = g * np.exp(-rng.uniform(0, 1) * (v ** 2))  # vary the shape
    r = ratio(v, g)
    if np.sum(g * np.exp(v / 2)) > 0: worst = min(worst, r)
print(f"   min ratio over trials with positive main term: {worst:.4f}")
v = np.linspace(-30, 0, 3001); g = np.abs(v) * np.exp(v / 2); g[0] = 0
print(f"   extremal g = |v| e^(v/2) on [-30,0]: ratio = {ratio(v, g):.5f}  (theory: 1)")
print("(ii) convolution squares f*f, f = e^(t/2) on [-L/2,0]:")
print("   L\tnumeric\t1/(1-e^(-L/2))")
for L in (4.0, 5.114, 6.0, 8.0, 12.0):
    v = np.linspace(-L, 0, 801)
    g = np.where(v >= -L / 2, -v, L + v) * np.exp(v / 2)  # (e*e)(v) on the window = e^{v/2} * overlap length
    g[0] = 0
    print(f"   {L}\t{ratio(v, g):.4f}\t{1/(1-math.exp(-L/2)):.4f}")
