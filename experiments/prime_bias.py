"""Exact spectral bias of prime-supported measures on G_q = (Z/qZ)^x, q prime.

For prime q, G_q is cyclic of order q-1. Fix a primitive root g and the discrete
log L: G_q -> Z_{q-1}. The characters are chi_k(a) = e(k L(a)/(q-1)), so
    mu_hat(chi_k) = sum_a mu(a) e(k L(a)/(q-1))
is the DFT of the pushforward of mu along L. One FFT of length q-1 gives the
bias against every character, so
    lambda_*(q, mu) = max_{k != 0} |mu_hat(chi_k)|
is computed exactly (up to floating point error ~1e-12).

Measures (all supported on n <= x, gcd(n, q) = 1):
  unif   : uniform on primes p <= x
  lam    : von Mangoldt weights Lambda(n) on n <= x (primes and prime powers)
  smooth : Lambda(n) * log(x/n)^2, the Perron kernel weight used in the proof
  rand   : uniform on a random multiset of residues of the same size as `unif`
           (the Alon-Roichman benchmark)

Output columns report lambda_* and two normalisations:
  grh  = lambda_* * sqrt(x) / log q         (GRH explicit-formula scale)
  rnd  = lambda_* * sqrt(|supp|) / sqrt(log q)  (random-set scale)
Empirical numbers are evidence about the truth, not proofs.
"""
import argparse
import math
import sys

import numpy as np
from sympy import primerange, primitive_root, isprime, nextprime


def dlog_table(q):
    g = primitive_root(q)
    L = np.empty(q, dtype=np.int64)
    L[0] = -1
    a = 1
    for e in range(q - 1):
        L[a] = e
        a = a * g % q
    return L


def von_mangoldt_upto(x):
    lam = np.zeros(x + 1)
    for p in primerange(2, x + 1):
        lp = math.log(p)
        pk = p
        while pk <= x:
            lam[pk] = lp
            pk *= p
    return lam


def bias(q, L, weights_by_n):
    """weights_by_n: dict n -> weight (n coprime to q). Returns lambda_*."""
    v = np.zeros(q - 1)
    for n, w in weights_by_n.items():
        v[L[n % q]] += w
    v /= v.sum()
    f = np.fft.fft(v)
    return float(np.max(np.abs(f[1:])))


def run(qs, xs, seed=0):
    rng = np.random.default_rng(seed)
    xmax = max(xs)
    lam = von_mangoldt_upto(xmax)
    rows = []
    for q in qs:
        L = dlog_table(q)
        lq = math.log(q)
        for x in xs:
            primes = [p for p in primerange(2, x + 1) if p != q]
            unif = {p: 1.0 for p in primes}
            lamw = {n: lam[n] for n in range(2, x + 1) if lam[n] > 0 and n % q}
            smooth = {n: lam[n] * math.log(x / n) ** 2 for n in lamw}
            rnd_supp = rng.integers(1, q, size=len(primes))
            rnd = {}
            for r in rnd_supp:
                rnd[int(r)] = rnd.get(int(r), 0.0) + 1.0
            for name, mu, supp in (("unif", unif, len(primes)),
                                   ("lam", lamw, len(lamw)),
                                   ("smooth", smooth, len(smooth)),
                                   ("rand", rnd, len(primes))):
                b = bias(q, L, mu)
                rows.append((q, x, name, supp, b, b * math.sqrt(x) / lq,
                             b * math.sqrt(supp) / math.sqrt(lq)))
    return rows


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--qs", type=int, nargs="*", default=None)
    ap.add_argument("--xs", type=int, nargs="*", default=[50, 100, 200, 400, 800, 1600])
    ap.add_argument("--qmin", type=int, default=10**4)
    ap.add_argument("--count", type=int, default=4)
    a = ap.parse_args()
    qs = a.qs
    if not qs:
        qs, q = [], a.qmin
        for _ in range(a.count):
            q = nextprime(q * 10)
            qs.append(q)
    print("q\tx\tmeasure\tsupp\tlambda\tgrh_norm\trand_norm")
    for r in run(qs, a.xs):
        print("%d\t%d\t%s\t%d\t%.4f\t%.3f\t%.3f" % r)
        sys.stdout.flush()


if __name__ == "__main__":
    main()
