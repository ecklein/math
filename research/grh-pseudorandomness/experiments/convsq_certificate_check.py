"""Exact bias of the measure in `bias_le_half_of_le_two_pow_64_convSq` for some prime q.

Kernel K = f*f, f(t) = e^{t/2} S(64(t+A)) S(-64t), A = 9/4, twist y = 2 log 220 (x = 48400).
Weights Lambda(n) K(log n - y)/sqrt(n) on n <= 48400 coprime to q. The theorem guarantees
bias <= 1/2 for every q <= 2^64; this computes the actual values (one FFT over discrete logs).
Also prints the closed-form numB/denB at the certificate parameters (R = 12), mirroring
`ConvCertificate.lean` with exact constants.
"""
import math, sys
import numpy as np
sys.path.insert(0, "experiments")
from prime_bias import dlog_table, von_mangoldt_upto
from sharp_certified import st

A, y, R = 2.25, 2 * math.log(220), 12.0
t = np.linspace(-A, 0, 18001); dt = t[1] - t[0]
f = np.exp(t / 2) * st(64 * (t + A)) * st(-64 * t)
U = np.linspace(-2 * A, 0, 4001)
K = np.array([np.sum(f * np.interp(u - t, t, f, left=0.0, right=0.0)) * dt for u in U])

def closed_form(lq):
    n2 = 1 - math.exp(-A)
    G = lambda B: (math.log(4 + R) + B) * n2 + 36 / (math.pi * R)
    M = math.floor(math.exp(y)) + 1
    UB = A * math.exp(-y / 2) * lq * (M.bit_length() - 1)
    num = n2 * lq + 2 / math.e * (math.floor(math.exp(A)) + 1) + G(5) + G(0.5) + UB
    den = math.exp(y / 2) * (math.exp(-1 / 64) - math.exp(-A + 1 / 64)) ** 2 - 2 * A \
        - G(5 + math.log(math.pi)) - G(0.5) - UB
    return num, den

if __name__ == "__main__":
    num, den = closed_form(64 * math.log(2))
    print(f"closed form at q = 2^64: numB = {num:.3f} (Lean: <= 65.7), denB = {den:.3f} (Lean: >= 143.9), "
          f"ratio = {num/den:.4f}")
    hi = round(math.exp(y))
    lam = von_mangoldt_upto(hi)
    print(f"support: n <= {hi}; weighted window [{math.exp(y - 2*A):.0f}, {hi}]")
    print("q\tbias\tguarantee")
    rows = []
    for q in (10007, 100003, 1000003, 4000037):
        L = dlog_table(q)
        v = np.zeros(q - 1)
        ns = np.nonzero(lam)[0]
        ns = ns[(ns % q) != 0]
        w = lam[ns] * np.interp(np.log(ns) - y, U, K, left=0.0, right=0.0) / np.sqrt(ns)
        np.add.at(v, L[ns % q], w)
        b = float(np.max(np.abs(np.fft.fft(v / v.sum()))[1:]))
        rows.append((q, b))
        print(f"{q}\t{b:.4f}\t0.5")
    with open("experiments/out/convsq_certificate_check.tsv", "w") as fh:
        fh.write("q\tbias\n")
        for q, b in rows:
            fh.write(f"{q}\t{b:.6f}\n")
