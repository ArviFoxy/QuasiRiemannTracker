"""Multiplicative relations among the Gauss sums g(chi^a), a = 1..l-1, of one character chi of order l at a
prime p = 1 (mod l), modulo roots of unity.

By Stickelberger's theorem the ideal of g(chi^a) in Q(zeta_l, zeta_p) is determined by the vector
v_a = (<a t / l>)_{t in (Z/l)^x} (fractional parts), and p has the vector u = (1, ..., 1); |g| = sqrt(p) in every
complex embedding, so by Kronecker a monomial in the g(chi^a) and p with zero valuation vector is a root of unity.
Hence the relation lattice is the integer kernel of [v_1 .. v_{l-1} u], and its rank is (l - 1 + 1) - rank.
"""
from fractions import Fraction as Fr
from math import gcd
import sys


def frac(x):
    return x - (x.numerator // x.denominator)


def rank(rows):
    rows = [list(r) for r in rows]
    r = 0
    ncol = len(rows[0])
    for c in range(ncol):
        piv = next((i for i in range(r, len(rows)) if rows[i][c] != 0), None)
        if piv is None:
            continue
        rows[r], rows[piv] = rows[piv], rows[r]
        for i in range(len(rows)):
            if i != r and rows[i][c] != 0:
                f = rows[i][c] / rows[r][c]
                rows[i] = [a - f * b for a, b in zip(rows[i], rows[r])]
        r += 1
    return r


def analyse(l):
    units = [t for t in range(1, l) if gcd(t, l) == 1]
    vecs = {a: [frac(Fr(a * t, l)) for t in units] for a in range(1, l)}
    u = [Fr(1)] * len(units)
    rk = rank([vecs[a] for a in range(1, l)] + [u])
    gens = l  # g(chi^1..chi^{l-1}) and p
    conj = len({frozenset((a, (-a) % l)) for a in range(1, l)})
    print(f'l = {l}: generators {gens} (g(chi^a), a=1..{l-1}, and p), valuation rank {rk}, '
          f'relation rank {gens - rk}; conjugate-pair relations g(chi^a)g(chi^-a) ~ p: {conj}; '
          f'extra (Hasse-Davenport type): {gens - rk - conj}')


if __name__ == '__main__':
    for l in [int(x) for x in sys.argv[1:]] or [2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]:
        analyse(l)
