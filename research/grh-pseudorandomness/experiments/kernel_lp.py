"""Fourier optimization beyond positive-definite kernels (direction A, notes/directions.md).

Problem: over nonnegative k supported in [-2a, 2a] (not necessarily even or positive definite),
    minimize  R(k) = (1/2pi) * int |k^(t)| dt   subject to   int k(u) e^{u/2} du = 1 .
R(k) is the leading coefficient of log q / sqrt(x) in the asymptotic bound of
Lamzouri-Li-Soundararajan (Lemma 6.1). The support-normalized constant is c(a) = e^a * R(a).
For comparison, the positive-definite optimum (cosh kernel) is R_PD(a) = 1/(a + sinh a),
c_PD(a) = e^a/(a + sinh a), with minimum c* = 1.2236 at a* = 1.2785.

Discretization: k is piecewise linear on n+1 nodes with k = 0 at both endpoints. Then exactly
    k^(t) = h sinc^2(t h / 2) sum_i k_i e^{i t u_i},
    int k e^{u/2} = sum_i k_i e^{u_i/2} h (sinh(h/4)/(h/4))^2 .
|k^(t)| is replaced by a variable s_j >= Re(e^{-i theta_l} k^(t_j)) for L angles theta_l, a
polygonal lower model of |.| (relative error <= 1 - cos(pi/L)). The t-integral uses the trapezoid
rule on [0, T], doubled for t < 0. The tail beyond T is bounded by the sinc^2 envelope and reported
separately. Besides the polygonal factor cos(pi/L), the LP value carries quadrature and truncation
errors, so it is neither an upper nor a lower bound in any certified sense. For each LP solution we
report the ratio recomputed by trapezoid quadrature on [0, T] (truncated, NOT certified) and an upper
bound for the omitted tail: a piecewise-linear K vanishing at both ends has |K^(t)| <= TV(K')/t^2,
so the tail is at most 2 TV(K')/(2 pi T). The quadrature error on [0, T] is not bounded.
EXPLORATORY NUMERICS ONLY. (Corrected 2026-11-27: earlier versions called the recomputed value
"exact" and used a much looser sinc^2 tail bound; a later version omitted the end-node slope jumps
from TV(K').)
"""
import math, sys
import numpy as np
from scipy.optimize import linprog


def solve(a, n=80, T=80.0, dt=0.05, L=16):
    u = np.linspace(-2 * a, 2 * a, n + 1)
    h = u[1] - u[0]
    inner = np.arange(1, n)                 # k_0 = k_n = 0
    U = u[inner]
    t = np.arange(0.0, T + dt / 2, dt)
    w = np.full(t.size, dt); w[0] = w[-1] = dt / 2
    env = h * np.sinc(t * h / (2 * np.pi)) ** 2       # np.sinc(x) = sin(pi x)/(pi x)
    C = env[:, None] * np.cos(np.outer(t, U))         # Re k^
    S = env[:, None] * np.sin(np.outer(t, U))         # Im k^
    m, nk = C.shape
    th = 2 * np.pi * np.arange(L) / L
    # rows: cos(th) C k + sin(th) S k - s_j <= 0
    A = []
    for c_, s_ in zip(np.cos(th), np.sin(th)):
        A.append(np.hstack([c_ * C + s_ * S, -np.eye(m)]))
    A = np.vstack(A)
    b = np.zeros(A.shape[0])
    mass = np.exp(U / 2) * h * (math.sinh(h / 4) / (h / 4)) ** 2
    Aeq = np.hstack([mass, np.zeros(m)])[None, :]
    cost = np.hstack([np.zeros(nk), 2 * w / (2 * np.pi)])
    res = linprog(cost, A_ub=A, b_ub=b, A_eq=Aeq, b_eq=[1.0],
                  bounds=[(0, None)] * nk + [(0, None)] * m, method="highs")
    if res.status != 0:
        raise RuntimeError(res.message)
    k = res.x[:nk]
    return u, U, k, h, res.fun


def truncated_R(U, k, h, T=4000.0, dt=0.01):
    """Ratio by trapezoid quadrature on [0, T] (truncated, uncertified) and a tail upper bound."""
    t = np.arange(0.0, T, dt)
    env = h * np.sinc(t * h / (2 * np.pi)) ** 2
    z = env * (np.exp(1j * np.outer(t, U)) @ k)
    head = 2 * np.trapezoid(np.abs(z), t) / (2 * np.pi)
    # K is extended by zero beyond the end nodes (where K = 0), so pad twice on each side: the outer
    # second differences are the slope jumps at the end nodes, from slope 0 to the first/last segment.
    kk = np.concatenate([[0.0, 0.0], k, [0.0, 0.0]])
    tv = np.sum(np.abs(np.diff(kk, 2))) / h          # total variation of K'
    tail = 2 * tv / T / (2 * np.pi)
    mass = np.sum(k * np.exp(U / 2)) * h * (math.sinh(h / 4) / (h / 4)) ** 2
    return head / mass, tail / mass


if __name__ == "__main__":
    print("a\tR_LP\tR_trunc(+tail bound)\tR_PD=1/(a+sinh a)\tc_trunc=e^a R\tc_tail=e^a tail\tc_PD\tmass_frac_top_quarter")
    for a in [float(x) for x in (sys.argv[1:] or ["0.75", "1.0", "1.2785", "1.5", "2.0", "3.0"])]:
        u, U, k, h, val = solve(a)
        R, tail = truncated_R(U, k, h)
        RPD = 1 / (a + math.sinh(a))
        top = np.sum(k[U > a]) / np.sum(k)
        print(f"{a}\t{val:.4f}\t{R:.4f}(+{tail:.5f})\t{RPD:.4f}\t{math.exp(a)*R:.4f}\t{math.exp(a)*tail:.5f}\t{math.exp(a)*RPD:.4f}\t{top:.2f}")
        np.savetxt(f"experiments/out/kernel_lp_a{a}.tsv", np.column_stack([U, k]), header="u k(u)")
