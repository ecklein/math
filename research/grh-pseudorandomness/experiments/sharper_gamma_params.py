"""Certified support with a sharper gamma-side bound, for both kernels (planned Lean bounds).

Sharper bound (Plancherel for the constant part, a split at |r| = R for the log part):
  (1/2pi) I(B) <= (B + log(4+R)) ||f||^2 + (C1^2/pi) (log(4+R) + 1)/R,
where C1 >= sup |r fhat(r)| and ||f||^2 = (f*f~)(0). R is optimized.
Kernels:
  cosh:  ||f||^2 <= sinh a + a,  C1 = 2 sinh(a/2) + 2 cosh(a/2), main F+F- >= (sinh a' + a')^2, pole 2(sinh a + a)^2,
         SP <= 4K/e (floor e^{2a} + 1), U <= K e^{a-y/2} log q log2 M, top X = x e^{2a}.
  conv-square (window A): ||f||^2 <= 1 - e^{-A}, C1 = 3, main Fp^2, pole 2 Fp Fm, SP <= (8/e) e^{A/2},
         U <= A log q log2(x+1)/sqrt x, top X = x.
Numerics only.
"""
import math
def gam(B, n2, C1):
    return min((B + math.log(4 + R)) * n2 + C1 ** 2 / math.pi * (math.log(4 + R) + 1) / R for R in [2 ** (k / 4) for k in range(0, 60)])
def cosh_bound(lq, a, y):
    ap = a - 1 / 64; K = math.sinh(a) + a * math.cosh(a); n2 = math.sinh(a) + a
    C1 = 2 * math.sinh(a / 2) + 2 * math.cosh(a / 2)
    M = math.floor(math.exp(y + 2 * a)) + 1
    U = K * math.exp(a - y / 2) * lq * math.floor(math.log2(M))
    num = n2 * lq + 4 * K / math.e * (math.floor(math.exp(2 * a)) + 1) + gam(5, n2, C1) + gam(0.5, n2, C1) + U
    den = math.exp(y / 2) * (math.sinh(ap) + ap) ** 2 - 2 * n2 ** 2 - gam(5 + math.log(math.pi), n2, C1) - gam(0.5, n2, C1) - U
    return (num / den if den > 0 else 1e9), math.exp(y + 2 * a)
def conv_bound(lq, A, y):
    x = math.exp(y); Fp = math.exp(-1 / 64) - math.exp(-A + 1 / 64); n2 = 1 - math.exp(-A)
    U = A * lq * math.floor(math.log2(x + 1)) / math.sqrt(x)
    num = n2 * lq + 8 / math.e * math.exp(A / 2) + gam(5, n2, 3) + gam(0.5, n2, 3) + U
    den = math.sqrt(x) * Fp ** 2 - 2 * Fp * A - gam(5 + math.log(math.pi), n2, 3) - gam(0.5, n2, 3) - U
    return (num / den if den > 0 else 1e9), x
def best(f, lq, eps, pars):
    out = None
    for p in pars:
        y = 1.0
        while y < 60:
            b, X = f(lq, p, y)
            if b <= eps:
                if out is None or X < out[1]: out = (p, X)
                break
            y += 0.01
    return out
print("bits\teps\tcosh: a, X\t\tconv-square: A, X\t(current formal cosh closed form)")
ref = {(64, 0.5): "1.3e5 (cert 1.66e5)", (64, 0.1): "1.8e6", (64, 0.01): "1.5e8", (1024, 0.5): "5.1e6", (1024, 0.1): "1.0e8", (1024, 0.01): "9.6e9"}
for bits in (64, 1024):
    lq = bits * math.log(2)
    for eps in (0.5, 0.1, 0.01):
        c = best(cosh_bound, lq, eps, [1 + 0.125 * i for i in range(17)])
        v = best(conv_bound, lq, eps, [1.5 + 0.25 * i for i in range(20)])
        print(f"{bits}\t{eps}\t{c[0]:.3f}, {c[1]:.2e}\t\t{v[0]:.2f}, {v[1]:.2e}\t\t{ref[(bits, eps)]}")
