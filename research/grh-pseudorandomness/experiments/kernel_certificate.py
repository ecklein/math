"""Interval-arithmetic certificate: a nonnegative kernel on a window of length 4 beats every convolution square.

Witness: the LP solution in out/kernel_lp_a1.0.tsv (window [-2, 2], step h = 1/20), with its 79 interior
node values rounded to nonnegative integers (scale is irrelevant: the ratio is scale invariant).
K is the piecewise-linear interpolant, zero at u = -2 and u = 2:
    K(u) = sum_j k_j Lambda((u - u_j)/h),   Lambda(s) = max(0, 1 - |s|),   u_j = -2 + (j+1) h.

Quantity (support-normalized constant, top of the support at u = 2):
    c(K) = e^{1} * (1/2pi) int_R |K^(t)| dt / int_R K(u) e^{u/2} du.

Exact reduction (periodization). K^(t) = h sinc^2(th/2) e^{i t u_0} P(th) with P(theta) = sum_j k_j e^{i j theta},
and sum_m sinc^2((theta + 2 pi m)/2) = 1, so
    (1/2pi) int_R |K^(t)| dt = (1/2pi) int_0^{2pi} |P(theta)| d theta     (no tail).
Quadrature: |P| is D-Lipschitz with D = sum_j |j - c| k_j for any real c (multiply P by e^{-i c theta}).
The average of |P| over the N points theta_m = 2 pi m / N, each the midpoint of a cell of width 2 pi / N
(periodicity), differs from the mean of |P| by at most pi D / (2 N).
Mass: int K e^{u/2} = h (sinh(h/4)/(h/4))^2 sum_j k_j e^{u_j/2}.

All quantities are enclosed with mpmath interval arithmetic (outward rounding). The script asserts
    c(K) < 1/(1 - e^{-2}) = optimum over convolution squares on a window of length 4 (Prop. 14).
This is a computer-assisted (not Lean-checked) certificate. It was written independently of, and agrees with,
an integer-interval certificate supplied by an external reviewer (bound 1.137621 for a different rounding of
the same LP solution).
"""
import sys
from fractions import Fraction
import numpy as np
from mpmath import iv

iv.dps = 30
N = int(sys.argv[1]) if len(sys.argv) > 1 else 2 ** 18

def witness():
    d = np.loadtxt("experiments/out/kernel_lp_a1.0.tsv")
    U, k = d[:, 0], d[:, 1]
    assert len(k) == 79 and abs(U[0] + 1.95) < 1e-12 and abs(U[1] - U[0] - 0.05) < 1e-12
    ints = [max(0, int(round(10 ** 6 * x / k.max()))) for x in k]
    assert all(v >= 0 for v in ints) and sum(ints) > 0
    return ints

def main():
    kj = witness()
    n = len(kj)
    h = iv.mpf(1) / 20
    # Lipschitz constant, centred at the weighted median index
    tot = sum(kj); acc = 0
    for c, v in enumerate(kj):
        acc += v
        if 2 * acc >= tot:
            break
    D = sum(abs(j - c) * v for j, v in enumerate(kj))
    # mean of |P| over the grid (upper bound)
    two_pi = 2 * iv.pi
    s_upper = iv.mpf(0)
    for m in range(N):
        th = two_pi * m / N
        ct, st = iv.cos(th), iv.sin(th)
        re = iv.mpf(0); im = iv.mpf(0)
        for v in reversed(kj):                       # Horner: P = sum k_j z^j, z = e^{i theta}
            re, im = re * ct - im * st + v, re * st + im * ct
        s_upper += iv.sqrt(re * re + im * im)
    mean_upper = s_upper / N + iv.pi * D / (2 * N)
    # mass (lower bound)
    q = h / 4
    corr = ((iv.exp(q) - iv.exp(-q)) / 2 / q) ** 2          # (sinh(h/4)/(h/4))^2
    mass = h * corr * sum(v * iv.exp((-2 + (j + 1) * h) / 2) for j, v in enumerate(kj))
    c_K = iv.exp(1) * mean_upper / mass
    conv = 1 / (1 - iv.exp(-2))
    c_hi = c_K.b
    conv_lo = conv.a
    assert c_hi < conv_lo, (c_hi, conv_lo)
    lines = [
        f"witness: 79 nonnegative integer node values (max 10^6), D = {D}, N = {N}",
        f"certified: c(K) <= {iv.nstr(c_hi, 10)}",
        f"convolution-square optimum 1/(1-e^-2) >= {iv.nstr(conv_lo, 10)}",
        f"strict separation certified: {c_hi < conv_lo}",
    ]
    print("\n".join(lines))
    with open("experiments/out/kernel_certificate.txt", "w") as fh:
        fh.write("\n".join(lines) + "\n")

if __name__ == "__main__":
    main()
