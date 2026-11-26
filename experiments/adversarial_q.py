"""Bias of primes <= x on G_q for q with a large least quadratic non-residue.

For these q the quadratic character is +1 on every prime below n2(q), so it is the
natural worst case for small x. Compares with typical q of similar size.
"""
import math, sys
import numpy as np
from sympy import primerange, legendre_symbol, nextprime
sys.path.insert(0, "experiments")
from prime_bias import dlog_table, bias

def least_qnr(q):
    for p in primerange(2, q):
        if legendre_symbol(p, q) == -1:
            return p

records = [10559, 18191, 31391, 366791, 422231, 701399, 3818929]
print("q\tn2(q)\tx\tlambda_all\tquad_bias\tlambda*sqrt(x)/log q\tlambda*sqrt(pi(x)/log q)")
for q in records + [nextprime(400000), nextprime(3800000)]:
    L = dlog_table(q); n2 = least_qnr(q)
    for x in (50, 200, 800, 3200):
        ps = [p for p in primerange(2, x+1) if p != q]
        b = bias(q, L, {p: 1.0 for p in ps})
        qb = abs(sum(legendre_symbol(p, q) for p in ps))/len(ps)
        print(f"{q}\t{n2}\t{x}\t{b:.4f}\t{qb:.4f}\t{b*math.sqrt(x)/math.log(q):.3f}\t{b*math.sqrt(len(ps)/math.log(q)):.3f}")
