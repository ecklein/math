"""Certified support from bias_sharp using closed-form (formal-friendly) constant bounds.

  k0 <= sinh a + a                                (grh-miller weilTest_testFnN_zero_le, formal)
  A  >= ((e^b - 1 - b) + b^2/2)/4, b = 2a - 1/32  (from weilTest_testFnN_re_ge; to formalize)
  B   = 2A, and A <= (a + sinh a)^2               (Cauchy-Schwarz; to formalize)
  I(B') <= (C0^2 + C1^2)(J + B' pi), C0 = 4 sinh(a/2), C1 = 2 sinh(a/2) + 2 cosh(a/2), J <= 6.577
  SP <= 2 k0 sum_{n <= e^{2a}} Lambda(n)/sqrt n
Numerics only.
"""
import math, sys
sys.path.insert(0, "experiments")
from prime_bias import von_mangoldt_upto
J_UP = math.pi * (math.log(4) + 1 / math.sqrt(2))

def cst(a):
    k0 = math.sinh(a) + a
    b = 2 * a - 1 / 32
    Alo = ((math.exp(b) - 1 - b) + b * b / 2) / 4
    Ahi = (a + math.sinh(a)) ** 2
    lam = von_mangoldt_upto(int(math.exp(2 * a)) + 1)
    SP = 2 * k0 * sum(lam[n] / math.sqrt(n) for n in range(2, len(lam)))
    C = (4 * math.sinh(a / 2)) ** 2 + (2 * math.sinh(a / 2) + 2 * math.cosh(a / 2)) ** 2
    I = lambda Bp: C * (J_UP + Bp * math.pi)
    return k0, Alo, Ahi, SP, I

for qbits in (16, 64, 1024, 4096):
    lq = qbits * math.log(2)
    for eps in (0.5, 0.1, 0.01):
        best = None
        for i in range(0, 11):
            a = 0.5 + 0.25 * i
            k0, Alo, Ahi, SP, I = cst(a)
            y = 2 * a + 0.01
            while y < 150:
                x = math.exp(y)
                U = (4 * a / math.log(2) + 1) * lq * k0 * math.exp(a) / math.sqrt(x)
                num = k0 * (lq - math.log(math.pi)) + SP + (I(5) + I(0.5)) / (2 * math.pi) + U
                den = math.exp(y / 2) * Alo - 2 * Ahi - (I(5 + math.log(math.pi)) + I(0.5)) / (2 * math.pi) - U
                if den > 0 and num / den <= eps:
                    X = math.exp(y + 2 * a)
                    if best is None or X < best[1]: best = (a, X)
                    break
                y += 0.02
        print(f"{qbits}\t{eps}\ta={best[0]}\tX={best[1]:.3e}\tlog2X={math.log2(best[1]):.1f}")
