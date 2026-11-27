"""Evaluate the constants of the formally verified sharp bound `bias_sharp` and the certified support.

Kernel: f_a(t) = cosh(t/2) * eta_a(t), eta_a(t) = st(64(a-t)) st(64(a+t)) (grh-miller testFN),
st = Real.smoothTransition. k_a = f_a * f_a~ (f_a even and real), so
  k(0) = int f^2,  A = int k(u) e^{u/2} du = (int f e^{t/2})^2,  B = 2A,
  I(B') = int fhat(r)^2 (log(4+|r|) + B') dr,  SP = sum_{n <= e^{2a}} Lambda(n) 2|k(log n)| / sqrt n.
Non-units: U <= (4a/log 2 + 1) log q * k(0) e^{a} / sqrt(x).
bias <= Num/Den with Num = k0 log(q/pi) + SP + (I(5)+I(1/2))/(2pi) + U,
                    Den = e^{y/2} A - B - (I(5+log pi) + I(1/2))/(2pi) - U.
Numerical quadrature only; the theorem is the Lean statement.
"""
import math, sys
import numpy as np
sys.path.insert(0, "experiments")
from prime_bias import von_mangoldt_upto

def st(x):
    def g(z): return np.where(z > 0, np.exp(-1.0 / np.where(z > 0, z, 1.0)), 0.0)
    gx, g1 = g(x), g(1 - x)
    return gx / (gx + g1)

def consts(a, n=20001):
    t = np.linspace(-a, a, n); dt = t[1] - t[0]
    f = np.cosh(t / 2) * st(64 * (a - t)) * st(64 * (a + t))
    k0 = np.sum(f * f) * dt
    Ahalf = np.sum(f * np.exp(t / 2)) * dt
    A = Ahalf ** 2
    def k(u):  # int f(t) f(t-u) dt
        fs = np.interp(t - u, t, f, left=0.0, right=0.0)
        return np.sum(f * fs) * dt
    lam = von_mangoldt_upto(int(math.exp(2 * a)) + 1)
    SP = sum(lam[m] * 2 * abs(k(math.log(m))) / math.sqrt(m) for m in range(2, len(lam)) if lam[m] > 0)
    r = np.linspace(-200, 200, 8001); dr = r[1] - r[0]
    fh = np.array([np.sum(f * np.cos(ri * t)) * dt for ri in r])
    F = fh ** 2
    def I(Bp): return float(np.sum(F * (np.log(4 + np.abs(r)) + Bp)) * dr)
    return dict(k0=k0, A=A, B=2 * A, SP=SP, I5=I(5), Ih=I(0.5), I5p=I(5 + math.log(math.pi)))

def bound(c, a, lq, y):
    x = math.exp(y)
    U = (4 * a / math.log(2) + 1) * lq * c['k0'] * math.exp(a) / math.sqrt(x)
    num = c['k0'] * (lq - math.log(math.pi)) + c['SP'] + (c['I5'] + c['Ih']) / (2 * math.pi) + U
    den = math.exp(y / 2) * c['A'] - c['B'] - (c['I5p'] + c['Ih']) / (2 * math.pi) - U
    return num / den if den > 0 else float('inf')

if __name__ == "__main__":
    cache = {a: consts(a) for a in (0.5, 0.75, 1.0, 1.25, 1.5, 2.0, 2.5, 3.0)}
    for a, c in cache.items():
        print(f"# a={a}: " + ", ".join(f"{kk}={vv:.4f}" for kk, vv in c.items()))
    print("qbits\teps\ta\tX_certified\tlog2X\t(formal Theorem B N)")
    old = {(64, 0.5): 9.693e15, (64, 0.1): 3.516e17, (64, 0.01): 5.646e19, (16, 0.5): 6.921e14, (1024, 0.5): 3.878e18}
    for qbits in (16, 64, 256, 1024, 4096):
        lq = qbits * math.log(2)
        for eps in (0.5, 0.1, 0.01):
            best = None
            for a, c in cache.items():
                y = 2 * a + 0.01
                while y < 120:
                    if bound(c, a, lq, y) <= eps:
                        X = math.exp(y + 2 * a)
                        if best is None or X < best[1]: best = (a, X)
                        break
                    y += 0.02
            a, X = best
            o = old.get((qbits, eps), float('nan'))
            print(f"{qbits}\t{eps}\t{a}\t{X:.3e}\t{math.log2(X):.1f}\t{o:.1e}")
