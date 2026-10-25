"""Exact univariate polynomials over Q (coefficient lists, lowest degree first), mirroring the Lean
`Faceless.Poly` operations, plus the positivity test TM1 used by the Lean checker:

  on [a, a + h]: with c = shift(p, a) (coefficients in t = s - a),
      min(c0, c0 + c1 h) > sum_{k >= 2} |c_k| h^k   implies   p > 0 on [a, a + h].
"""
from fractions import Fraction as Fr


def trim(p):
    p = list(p)
    while p and p[-1] == 0:
        p.pop()
    return p


def add(p, q):
    n = max(len(p), len(q))
    return [(p[i] if i < len(p) else 0) + (q[i] if i < len(q) else 0) for i in range(n)]


def smul(c, p):
    return [c*x for x in p]


def sub(p, q):
    return add(p, smul(-1, q))


def mul(p, q):
    if not p or not q:
        return []
    r = [Fr(0)]*(len(p) + len(q) - 1)
    for i, a in enumerate(p):
        if a == 0:
            continue
        for j, b in enumerate(q):
            r[i + j] += a*b
    return r


def const(c):
    return [Fr(c)]


X = [Fr(0), Fr(1)]


def ev(p, x):
    r = Fr(0)
    for c in reversed(p):
        r = c + x*r
    return r


def shift(p, a):
    """coefficients of t -> p(a + t) (Horner)."""
    r = []
    for c in reversed(p):
        r = add([c], mul([a, Fr(1)], r))
    return r


def tm1(p, a, h):
    c = shift(p, a)
    c = c + [Fr(0)]*(2 - len(c)) if len(c) < 2 else c
    R = sum(abs(ck)*h**k for k, ck in enumerate(c) if k >= 2)
    return min(c[0], c[0] + c[1]*h) > R


def tm1_split(p, a, b, depth=0, maxdepth=30):
    """Bisection until TM1 succeeds; returns the breakpoints or None."""
    if tm1(p, a, b - a):
        return [a, b]
    if depth >= maxdepth:
        return None
    m = (a + b)/2
    l = tm1_split(p, a, m, depth + 1, maxdepth)
    if l is None:
        return None
    r = tm1_split(p, m, b, depth + 1, maxdepth)
    if r is None:
        return None
    return l[:-1] + r


def digits(p):
    return max((max(len(str(abs(c.numerator))), len(str(c.denominator))) for c in p), default=0)
