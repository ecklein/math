"""Real part of the complex digamma function, without SciPy.

Recurrence psi(z) = psi(z+1) - 1/z shifts Re z above 10, then the asymptotic series
psi(z) ~ log z - 1/(2z) - sum B_{2k} / (2k z^{2k}) (error < 1e-12 for |z| >= 10).
"""
import cmath

_B = [1 / 6, -1 / 30, 1 / 42, -1 / 30, 5 / 66, -691 / 2730, 7 / 6]


def digamma(z):
    acc = 0j
    while z.real < 10:
        acc -= 1 / z
        z += 1
    s = cmath.log(z) - 1 / (2 * z)
    z2 = z * z
    zp = z2
    for k, b in enumerate(_B, start=1):
        s -= b / (2 * k * zp)
        zp *= z2
    return s + acc


def re_digamma(z):
    return digamma(z).real


if __name__ == "__main__":
    # psi(1) = -gamma, psi(1/4) = -gamma - pi/2 - 3 log 2
    import math
    print(digamma(1 + 0j).real, -0.5772156649015329)
    print(digamma(0.25 + 0j).real, -0.5772156649015329 - math.pi / 2 - 3 * math.log(2))
