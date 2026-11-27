"""Certified parameters for the convolution-square kernel K = f*f, f = e^{t/2} eta_A(t) (planned Lean bounds).

Bias <= Num/Den with (window [x e^{-2A}, x], top X = x):
  Num = (1 - e^{-A}) log q + SP + C(6+5pi)/(2pi) + C(6+pi/2)/(2pi) + U
  Den = sqrt(x) Fp^2 - 2 Fp Fm - (C(6+(5+log pi)pi) + C(6+pi/2))/(2pi) - U
  Fp >= e^{-1/64} - e^{-A+1/64},  Fm <= A,  C <= 13,  SP <= (8/e) e^{A/2},
  U <= A log q floor(log2(x+1)) / sqrt(x).
Numerics only. Compared with the formal cosh certificate (X ~ 1.66e5 at q <= 2^64, eps = 1/2).
"""
import math
def bound(lq, A, x, C=13.0):
    Fp = math.exp(-1/64) - math.exp(-A + 1/64); Fm = A
    SP = 8 / math.e * math.exp(A / 2)
    U = A * lq * math.floor(math.log2(x + 1)) / math.sqrt(x)
    num = (1 - math.exp(-A)) * lq + SP + C * (12 + 5.5 * math.pi) / (2 * math.pi) + U
    den = math.sqrt(x) * Fp ** 2 - 2 * Fp * Fm - C * (12 + (5.5 + math.log(math.pi)) * math.pi) / (2 * math.pi) - U
    return num / den if den > 0 else float("inf")
def best(bits, eps):
    lq = bits * math.log(2); out = None
    for i in range(1, 41):
        A = 0.25 * i
        x = 10.0
        while x < 1e14:
            if bound(lq, A, x) <= eps:
                if out is None or x < out[1]: out = (A, x)
                break
            x *= 1.01
    return out
print("bits\teps\tA\tX_certified\t(cosh formal certificate / closed form)")
ref = {(64, 0.5): "1.66e5 / 1.3e5", (64, 0.1): "- / 1.8e6", (64, 0.01): "- / 1.5e8", (1024, 0.5): "- / 5.1e6"}
for bits in (64, 1024):
    for eps in (0.5, 0.1, 0.01):
        A, x = best(bits, eps)
        print(f"{bits}\t{eps}\t{A}\t{x:.3e}\t{ref.get((bits, eps), '')}")
lq = 64 * math.log(2)
for A in (2.0, 2.5, 3.0, 3.5, 4.0):
    x = 22500.0
    print(f"A={A}: bound at x=22500 (q<=2^64) = {bound(lq, A, x):.4f}")
