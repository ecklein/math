"""Parameters certified by the formal closed-form theorem `bias_sharp_closed` (numB/denB exactly as in Lean).

For each (log2 q bound, eps), searches a in {1, 1.25, ..., 3} and y, minimizing the support X = e^{y+2a}.
Numerics only: an instance becomes machine-checked by a numeric proof like `Certificate64.lean`.
"""
import math
def K(a): return math.sinh(a) + a * math.cosh(a)
def C(a): return (4 * math.sinh(a / 2)) ** 2 + (2 * math.sinh(a / 2) + 2 * math.cosh(a / 2)) ** 2
def UB(lq, a, y): return K(a) * math.exp(a - y / 2) * lq * math.floor(math.log2(math.floor(math.exp(y + 2 * a)) + 1))
def numB(lq, a, y):
    return (math.sinh(a) + a) * lq + 2 * K(a) * (2 / math.e) * (math.floor(math.exp(2 * a)) + 1) + \
        (C(a) * (6 + 5 * math.pi) + C(a) * (6 + math.pi / 2)) / (2 * math.pi) + UB(lq, a, y)
def denB(lq, a, y):
    ap = a - 1 / 64
    return math.exp(y / 2) * (math.sinh(ap) + ap) ** 2 - 2 * (math.sinh(a) + a) ** 2 - \
        (C(a) * (6 + (5 + math.log(math.pi)) * math.pi) + C(a) * (6 + math.pi / 2)) / (2 * math.pi) - UB(lq, a, y)
print("log2 q\teps\ta\tX\tlog2 X")
for bits in (16, 32, 64, 128, 256, 1024, 4096):
    lq = bits * math.log(2)
    for eps in (0.5, 0.1, 0.01):
        best = None
        for i in range(9):
            a = 1 + 0.25 * i
            y = 2 * a + 0.01
            while y < 120:
                d = denB(lq, a, y)
                if d > 0 and numB(lq, a, y) / d <= eps:
                    X = math.exp(y + 2 * a)
                    if best is None or X < best[1]: best = (a, X)
                    break
                y += 0.01
        print(f"{bits}\t{eps}\t{best[0]}\t{best[1]:.3e}\t{math.log2(best[1]):.1f}")
print("check q<=2^64, a=1, y=2log150:", numB(64*math.log(2),1,2*math.log(150))/denB(64*math.log(2),1,2*math.log(150)))
