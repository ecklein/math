"""Exploratory: how close a band-limited positive-definite majorant gets to the general-kernel constant.

Positivity needs only a positive-definite M with M^(t) >= |K^(t)| on R (paper, Section 6.1); M compactly supported
(supp M in [-S, S]) keeps the prime sums finite. Take K piecewise linear with step h (the LP witness) and M piecewise
linear with the same step h, even, with node values q_0, ..., q_n at u = 0, h, ..., nh (S = (n+1)h). Then
    M^(t) = h sinc^2(th/2) Q(th),  Q(theta) = q_0 + 2 sum_{j>=1} q_j cos(j theta),
    K^(t) = h sinc^2(th/2) e^{i t u_0} P(th),  P(theta) = sum_j k_j e^{i j theta},
so M^ >= |K^| on R  <=>  Q(theta) >= |P(theta)| for all theta  (exactly; no tail), and M(0) = q_0, while
(1/2pi) int |K^| = mean of |P|. As n grows the best q_0 decreases to mean |P| (Fejer means of |P| converge uniformly),
so the positivity method recovers the general-kernel constant in the limit.
This script solves  min q_0  s.t.  Q >= |P|  on a theta grid (LP, HiGHS) for several n, and reports
    c_major(n) = e^{a} q_0 / int K e^{u/2}   against   c(K) = e^{a} mean|P| / int K e^{u/2}.
Grid-only constraints: an UNDER-estimate of the semi-infinite problem, NOT certified. EXPLORATORY.
"""
import math, sys
import numpy as np
from scipy.optimize import linprog


def main(a_str="1.0"):
    d = np.loadtxt(f"experiments/out/kernel_lp_a{a_str}.tsv")
    U, k = d[:, 0], d[:, 1]
    a = float(a_str); h = U[1] - U[0]
    th = np.linspace(0, np.pi, 4001)
    P = np.exp(1j * np.outer(th, np.arange(k.size))) @ k
    absP = np.abs(P)
    mass = np.sum(k * np.exp(U / 2)) * h * (math.sinh(h / 4) / (h / 4)) ** 2
    thf = np.linspace(0, 2 * np.pi, 200001)
    meanP = np.mean(np.abs(np.exp(1j * np.outer(thf, np.arange(k.size))) @ k)) if False else None
    Pf = np.zeros(thf.size, complex)
    for j, kj in enumerate(k):
        Pf += kj * np.exp(1j * j * thf)
    meanP = np.trapezoid(np.abs(Pf), thf) / (2 * np.pi)
    cK = math.exp(a) * meanP / mass
    print(f"window {4*a}: c(K) = {cK:.4f} (general-kernel value of the witness); conv-square optimum {1/(1-math.exp(-2*a)):.4f}")
    print("n\tS=(n+1)h\tc_major(n)  [exploratory LP]")
    for n in (40, 80, 160, 320, 640):
        C = np.hstack([np.ones((th.size, 1)), 2 * np.cos(np.outer(th, np.arange(1, n + 1)))])
        res = linprog(np.eye(n + 1)[0], A_ub=-C, b_ub=-absP, bounds=[(None, None)] * (n + 1), method="highs")
        if res.status != 0:
            print(n, "LP failed:", res.message); continue
        print(f"{n}\t{(n+1)*h:.2f}\t{math.exp(a)*res.x[0]/mass:.4f}")


if __name__ == "__main__":
    main(*(sys.argv[1:2] or ["1.0"]))
