"""Certified support for the sharp route using only formal-friendly (cruder) constants.

bias <= Num / Den with
  Num = k0 log(q/pi) + 2 S(a) + G1 + G2 + U,   Den = e^{y/2} A_lo - A_hi - B - G3 - G4 - U
  k0  <= sinh a + a                        (weilTest_testFnN_zero_le)
  A_lo = ((e^b - 1 - b) + b^2/2)/4, b = 2a - 1/32   (from weilTest_testFnN_re_ge, k even)
  A_hi, B <= (a + sinh a)^2 (upper, Cauchy-Schwarz-free crude: k <= k0, int over [-2a,2a] of e^{u/2})
  G's: (1/2pi)(C0^2 + C1^2)(J + 4.58 pi) each, C0 = 4 sinh(a/2), C1 = 2 sinh(a/2) + 2 cosh(a/2)
  S(a) <= k0 * sum_{n <= e^{2a}} Lambda(n)/sqrt(n);  U <= log q * log2(x e^{2a}) * k0 / sqrt(x e^{-2a})
Numerics only.
"""
import math, sys
sys.path.insert(0, "experiments")
from prime_bias import von_mangoldt_upto
J = 5.626229
def params(a):
    k0 = math.sinh(a) + a
    b = 2 * a - 1 / 32
    A_lo = ((math.exp(b) - 1 - b) + b * b / 2) / 4
    A_hi = 4 * a * k0 * math.exp(a)  # int_{-2a}^{2a} k0 e^{u/2} du <= 4a k0 e^a
    lam = von_mangoldt_upto(int(math.exp(2 * a)) + 1)
    S = k0 * sum(lam[n] / math.sqrt(n) for n in range(2, len(lam)))
    C0, C1 = 4 * math.sinh(a / 2), 2 * math.sinh(a / 2) + 2 * math.cosh(a / 2)
    G = (C0 ** 2 + C1 ** 2) * (J + 4.58 * math.pi) / (2 * math.pi)
    return k0, A_lo, A_hi, S, G
def certified_X(qbits, eps):
    lq = qbits * math.log(2)
    best = None
    for i in range(1, 40):
        a = 0.5 + 0.25 * i
        k0, A_lo, A_hi, S, G = params(a)
        # search y
        y = 2 * a + 0.01
        while y < 200:
            x = math.exp(y)
            U = lq * math.log2(x * math.exp(2 * a)) * k0 / math.sqrt(x * math.exp(-2 * a))
            num = k0 * (lq - math.log(math.pi)) + 2 * S + 2 * G + U
            den = math.exp(y / 2) * A_lo - A_hi - A_hi - 2 * G - U
            if den > 0 and num / den <= eps:
                X = x * math.exp(2 * a)
                if best is None or X < best[1]:
                    best = (a, X)
                break
            y += 0.05
    return best
print("qbits\teps\ta\tX_certified\tlog2X")
for qbits in (16, 64, 1024, 4096):
    for eps in (0.5, 0.1, 0.01):
        a, X = certified_X(qbits, eps)
        print(f"{qbits}\t{eps}\t{a}\t{X:.3e}\t{math.log2(X):.1f}")
