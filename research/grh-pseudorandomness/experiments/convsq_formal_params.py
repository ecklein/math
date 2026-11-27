"""Parameters for the formal convolution-square certificate (mirrors the planned Lean closed form).

Kernel K = f*f, f(t) = e^{t/2} S(64(t+A)) S(-64t) (S = smoothTransition), supported in [-A, 0].
Majorant M = f*f~. Weights Lambda(n) K(log n - y)/sqrt n on n <= x = e^y (y > 2A).
  n2  = M(0) = ||f||^2 <= 1 - e^{-A}
  G(B) = (log(4+R) + B) n2 + 4 C1^2/(pi R),  C1 = 3      [ >= (1/2pi) I(B), sharper gamma bound ]
  SP  <= (2/e)(floor(e^A) + 1)                             [ Lambda(n)/n <= 1/e, |M(u)| <= e^{-|u|/2} ]
  U   <= A e^{-y/2} log q * log2(floor(e^y) + 1)           [ |K(u)| <= A e^{u/2} ]
  main: sqrt(x) Fp^2 with Fp >= e^{-1/64} - e^{-A+1/64};  pole <= 2A
  Num = n2 log q + SP + G(5) + G(1/2) + U
  Den = sqrt(x) Fp^2 - 2A - G(5 + log pi) - G(1/2) - U
Numerics only.
"""
import math, sys
def bound(lq, A, y, R):
    n2 = 1 - math.exp(-A); C1 = 3.0
    G = lambda B: (math.log(4 + R) + B) * n2 + 4 * C1 ** 2 / (math.pi * R)
    Fp = math.exp(-1 / 64) - math.exp(-A + 1 / 64)
    M = math.floor(math.exp(y)) + 1
    U = A * math.exp(-y / 2) * lq * math.floor(math.log2(M))
    num = n2 * lq + 2 / math.e * (math.floor(math.exp(A)) + 1) + G(5) + G(0.5) + U
    den = math.exp(y / 2) * Fp ** 2 - 2 * A - G(5 + math.log(math.pi)) - G(0.5) - U
    return (num / den if den > 0 else float("inf")), num, den
def best(lq, eps):
    out = None
    for A in [1.5 + 0.125 * i for i in range(30)]:
        for R in [10, 20, 30, 50, 75, 100, 150, 200, 300, 500, 1000]:
            y = 2 * A + 0.01
            while y < 60:
                b = bound(lq, A, y, R)[0]
                if b <= eps:
                    if out is None or y < out[2]: out = (A, R, y)
                    break
                y += 0.005
    return out
if __name__ == "__main__":
    print("bits\teps\tA\tR\ty\tX = e^y")
    for bits in (64, 1024):
        for eps in (0.5, 0.1, 0.01):
            A, R, y = best(bits * math.log(2), eps)
            print(f"{bits}\t{eps}\t{A}\t{R}\t{y:.3f}\t{math.exp(y):.3e}")
