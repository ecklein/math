"""Interval-arithmetic certificate: a nonnegative kernel on a window of length 4 beats every convolution square.

Usage:  kernel_certificate.py [--a A] [--N N] [--eps EPS]
  --a    half-width parameter of the LP witness (window [-2a, 2a], file out/kernel_lp_a{A}.tsv); default 1.0
  --N    quadrature points; default 2^18
  --eps  smoothing width; the certified C^infinity kernel K*phi lives on a window of length 4a + eps;
         default 0 (piecewise-linear witness only)

Witness: an LP solution from kernel_lp.py on [-2a, 2a] with 80 equal steps, h = a/20, its 79 interior node values
rounded to nonnegative integers (the ratio is scale invariant). K is the piecewise-linear interpolant, zero at +-2a:
    K(u) = sum_j k_j Lambda((u - u_j)/h),   Lambda(s) = max(0, 1 - |s|),   u_j = -2a + (j+1) h.

Quantity (support-normalized constant; top of the support T = 2a):
    c(K) = e^{a} * (1/2pi) int_R |K^(t)| dt / int_R K(u) e^{u/2} du.

Exact reduction (periodization, paper Lemma 16). K^(t) = h sinc^2(th/2) e^{i t u_0} P(th), P(theta) = sum_j k_j e^{ij theta},
and sum_m sinc^2((theta + 2 pi m)/2) = 1, so (1/2pi) int_R |K^| = (1/2pi) int_0^{2pi} |P|  (no tail).
Quadrature: |P| is D-Lipschitz with D = sum_j |j - c| k_j for any real c; the average over the N cell midpoints
theta_m = 2 pi m / N differs from the mean of |P| by at most pi D / (2N).
Mass: int K e^{u/2} = h (sinh(h/4)/(h/4))^2 sum_j k_j e^{u_j/2}.

Smoothing (paper, Prop. 17(ii)). For phi >= 0 in C_c^infinity with supp phi in [-eps, 0] and int phi = 1,
K_eps = K * phi is C^infinity, nonnegative, supported in [-2a - eps, 2a] (same top), |K_eps^| = |K^||phi^| <= |K^|,
and int K_eps e^{u/2} = (int K e^{u/2})(int phi(v) e^{v/2} dv) >= e^{-eps/2} int K e^{u/2}. Hence
c(K_eps) <= e^{eps/2} c(K) on a window of length 4a + eps.

All quantities are enclosed with mpmath interval arithmetic (outward rounding). The script asserts that the
certified bound is below 1/(1 - e^{-L/2}), the optimum over convolution squares on the final window length L (Prop. 14).
Majorant (paper, Prop. 18), option --majorant n. Positivity needs only a positive-definite, compactly supported M
with M^ >= |K^| on R. With M even, piecewise linear with the same step h and node values q_0..q_n,
M^(t) = h sinc^2(th/2) Q(th), Q(theta) = q_0 + 2 sum q_j cos(j theta), so M^ >= |K^| <=> Q >= |P| on the circle, and
M(0) = q_0. We take q from an LP (floats), add slack to q_0, round to rationals, and verify Q - |P| >= 0 on the circle:
it is Lipschitz with constant 2 sum j|q_j| + D, so its minimum over the N cell midpoints minus that constant times
pi/N is a certified lower bound. M^ = h sinc^2 Q >= 0, so M is positive definite. The certified positivity constant
is c_major = e^{a} q_0 / int K e^{u/2}, and smoothing (K*phi*phi, M*phi*phi~) multiplies it by at most e^{eps/2}.
Computer-assisted, not Lean-checked. Independent of, and in agreement with, an external reviewer's integer-interval
certificate for a = 1 (bound 1.137621 for a different rounding of the same LP solution).
"""
import argparse
from fractions import Fraction
import numpy as np
from mpmath import iv

iv.dps = 30


def witness(a_str):
    d = np.loadtxt(f"experiments/out/kernel_lp_a{a_str}.tsv")
    U, k = d[:, 0], d[:, 1]
    a = Fraction(a_str).limit_denominator(10 ** 6)
    h = a / 20
    assert len(k) == 79
    for j in range(79):                       # nodes are exactly -2a + (j+1) h
        assert abs(U[j] - float(-2 * a + (j + 1) * h)) < 1e-9
    ints = [max(0, int(round(10 ** 6 * x / k.max()))) for x in k]
    assert sum(ints) > 0
    return a, h, ints


def majorant_lp(kj, n, slack):
    """LP for min q_0 s.t. Q >= |P| on a grid; returns rational q with q_0 increased by `slack` (relative)."""
    from scipy.optimize import linprog
    k = np.array(kj, dtype=float)
    th = np.linspace(0, np.pi, 8001)
    absP = np.abs(np.exp(1j * np.outer(th, np.arange(k.size))) @ k)
    C = np.hstack([np.ones((th.size, 1)), 2 * np.cos(np.outer(th, np.arange(1, n + 1)))])
    res = linprog(np.eye(n + 1)[0], A_ub=-C, b_ub=-absP, bounds=[(None, None)] * (n + 1), method="highs")
    assert res.status == 0, res.message
    q = [Fraction(int(round(x))) for x in res.x]
    q[0] = Fraction(int(round(res.x[0] * (1 + slack))))
    return q


def certify(a_str, N, eps_str, n_major=0, slack="0.002"):
    a, h_q, kj = witness(a_str)
    eps = Fraction(eps_str)
    h = iv.mpf(h_q.numerator) / h_q.denominator
    ai = iv.mpf(a.numerator) / a.denominator
    # Lipschitz constant, centred at the weighted median index
    tot = sum(kj); acc = 0
    for c, v in enumerate(kj):
        acc += v
        if 2 * acc >= tot:
            break
    D = sum(abs(j - c) * v for j, v in enumerate(kj))
    two_pi = 2 * iv.pi
    q = majorant_lp(kj, n_major, float(slack)) if n_major else None
    if q:
        LipQ = 2 * sum(j * abs(x) for j, x in enumerate(q))
        Lip = iv.mpf(LipQ.numerator) / LipQ.denominator + D
        gap_lo = None
        qcoef = [iv.mpf(q[0].numerator) / q[0].denominator] + \
            [2 * iv.mpf(x.numerator) / x.denominator for x in q[1:]]
    s_upper = iv.mpf(0)
    for m in range(N):
        th = two_pi * m / N
        ct, st = iv.cos(th), iv.sin(th)
        re = iv.mpf(0); im = iv.mpf(0)
        for v in reversed(kj):                       # Horner: P = sum k_j z^j, z = e^{i theta}
            re, im = re * ct - im * st + v, re * st + im * ct
        absP = iv.sqrt(re * re + im * im)
        s_upper += absP
        if q:
            # Q(theta) = Re(q_0 + 2 sum_{j>=1} q_j z^j), z = e^{i theta}; complex Horner (stable in intervals;
            # a Chebyshev recurrence for cos(j theta) roughly triples interval widths per step)
            qre = iv.mpf(0); qim = iv.mpf(0)
            for c in reversed(qcoef):
                qre, qim = qre * ct - qim * st + c, qre * st + qim * ct
            g = qre - absP
            gap_lo = g.a if gap_lo is None else min(gap_lo, g.a)
    mean_upper = s_upper / N + iv.pi * D / (2 * N)
    qq = h / 4
    corr = ((iv.exp(qq) - iv.exp(-qq)) / 2 / qq) ** 2          # (sinh(h/4)/(h/4))^2
    mass = h * corr * sum(v * iv.exp((-2 * ai + (j + 1) * h) / 2) for j, v in enumerate(kj))
    c_K = iv.exp(ai) * mean_upper / mass
    epsi = iv.mpf(eps.numerator) / eps.denominator
    c_final = c_K * iv.exp(epsi / 2)
    L = 4 * ai + epsi
    conv = 1 / (1 - iv.exp(-L / 2))
    ok = c_final.b < conv.a
    extra = []
    if q:
        cert_gap = gap_lo - (Lip * iv.pi / N).b          # certified lower bound for min (Q - |P|)
        q0 = iv.mpf(q[0].numerator) / q[0].denominator
        c_maj = iv.exp(ai) * q0 / mass * iv.exp(epsi / 2)
        okm = (cert_gap > 0) and (c_maj.b < conv.a)
        extra = [
            f"majorant: degree n = {n_major}, supp M in [-{(n_major + 1) * h_q}, {(n_major + 1) * h_q}], "
            f"certified min(Q - |P|) >= {iv.nstr(cert_gap, 6)} (> 0: {cert_gap > 0})",
            f"positivity constant with majorant (after smoothing eps = {eps}): c <= {iv.nstr(c_maj.b, 10)}",
            f"majorant separation certified: {okm}",
        ]
        ok = ok and okm
    lines = [
        f"witness: kernel_lp_a{a_str}.tsv, window length {4 * a}, 79 integer node values (max 10^6), D = {D}, N = {N}",
        f"certified (piecewise linear): c(K) <= {iv.nstr(c_K.b, 10)}",
        (f"smoothing eps = {eps}: C^infinity kernel on window length {4 * a + eps}, c <= {iv.nstr(c_final.b, 10)}"
         if eps else "no smoothing (eps = 0)"),
        f"convolution-square optimum on that window, 1/(1-e^(-L/2)) >= {iv.nstr(conv.a, 10)}",
        f"strict separation certified: {c_final.b < conv.a}",
    ] + extra
    assert ok, lines
    return lines


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("--a", default="1.0")
    ap.add_argument("--N", type=int, default=2 ** 18)
    ap.add_argument("--eps", default="0")
    ap.add_argument("--majorant", type=int, default=0)
    ap.add_argument("--slack", default="0.002")
    args = ap.parse_args()
    lines = certify(args.a, args.N, args.eps, args.majorant, args.slack)
    print("\n".join(lines))
    tag = "" if (args.a == "1.0" and args.eps == "0" and not args.majorant) else \
        f"_a{args.a}_eps{args.eps.replace('/', 'over')}" + (f"_major{args.majorant}" if args.majorant else "")
    with open(f"experiments/out/kernel_certificate{tag}.txt", "w") as fh:
        fh.write("\n".join(lines) + "\n")
