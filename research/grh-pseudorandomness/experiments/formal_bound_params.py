"""Evaluate the constants of the formally verified bound (lean/.../PrimeMeasure.lean).

bias <= charSumBound(q, N) / massLower(q, N), where
  charSumBound = 48 e / pi * log(N)^2 * sqrt(N) * (pi * log(2 + 8q) + J)
  massLower    = ((N//2) log 2 - log(N//2 + 1)) / 2 - log(q) * floor(log2 N)
  J            = int_R log(4 + |t|) / (1 + t^2) dt.
Prints J, and the least N (searched over powers of two, then bisected) for which the proven
bound certifies bias <= eps. Numerics only; the Lean statement is the theorem.
"""
import math

def J_const():
    # int_0^inf log(4+t)/(1+t^2) dt * 2, via t = tan(u): int_0^{pi/2} log(4 + tan u) du * 2
    n = 2_000_000
    h = (math.pi / 2) / n
    s = 0.0
    for i in range(n):
        u = (i + 0.5) * h
        s += math.log(4 + math.tan(u))
    return 2 * s * h

J = J_const()

def bound(q, N):
    cs = 48 * math.e / math.pi * math.log(N) ** 2 * math.sqrt(N) * (math.pi * math.log(2 + 8 * q) + J)
    ml = ((N // 2) * math.log(2) - math.log(N // 2 + 1)) / 2 - math.log(q) * int(math.log2(N))
    return cs / ml if ml > 0 else float("inf")

def least_N(q, eps):
    N = 4
    while bound(q, N) > eps:
        N *= 2
    lo, hi = N // 2, N
    while hi - lo > max(1, lo // 1000):
        mid = (lo + hi) // 2
        if bound(q, mid) <= eps:
            hi = mid
        else:
            lo = mid
    return hi

if __name__ == "__main__":
    print(f"J = {J:.6f}  (pi(log 4 + 1/sqrt 2) = {math.pi*(math.log(4)+1/math.sqrt(2)):.6f} is a proven-style upper bound)")
    print("q\teps\tN_certified\tlog2(N)\tN/(log q)^2")
    for qbits in (16, 32, 64, 128, 256, 1024, 4096):
        q = 2 ** qbits
        for eps in (0.5, 0.1, 0.01):
            N = least_N(q, eps)
            print(f"2^{qbits}\t{eps}\t{N:.3e}\t{math.log2(N):.1f}\t{N/math.log(q)**2:.3e}")
