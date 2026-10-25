"""Integer polynomials mirroring Lean `Faceless.IPoly` (ishift3/ibern3/ib33, tm1On, dyadic search)."""
from fractions import Fraction as Fr
from math import lcm

def add(p, q):
    n = max(len(p), len(q))
    return [(p[i] if i < len(p) else 0) + (q[i] if i < len(q) else 0) for i in range(n)]

def smul(c, p):
    return [c*x for x in p]

def mul(p, q):
    if not p or not q: return []
    r = [0]*(len(p) + len(q) - 1)
    for i, a in enumerate(p):
        if a:
            for j, b in enumerate(q):
                r[i + j] += a*b
    return r

def shift(p, k):
    r = []
    for c in reversed(p):
        r = add([c], mul([k, 1], r))
    return r

def scale(e, p):
    n = len(p) - 1
    return [c*2**(e*(n - i)) for i, c in enumerate(p)]

def tm1(Q):
    if not Q: return False
    if len(Q) == 1: return Q[0] > 0
    return sum(abs(c) for c in Q[2:]) < min(Q[0], Q[0] + Q[1])

def tm1On(p, k, e):
    return tm1(shift(scale(e, p), k))

def dyadic_cover(p, k=0, e=0, maxe=14):
    """Contiguous dyadic intervals (k, e) covering [k/2^e, (k+1)/2^e] on which tm1On holds."""
    if tm1On(p, k, e): return [(k, e)]
    if e >= maxe: return None
    l = dyadic_cover(p, 2*k, e + 1, maxe)
    if l is None: return None
    r = dyadic_cover(p, 2*k + 1, e + 1, maxe)
    return None if r is None else l + r

def ishift3(c, k, m):
    A = 2**m
    return [add(add(smul(A**3, c[0]), smul(A**2*k, c[1])), add(smul(A*k**2, c[2]), smul(k**3, c[3]))),
            add(add(smul(A**2, c[1]), smul(2*A*k, c[2])), smul(3*k**2, c[3])),
            add(smul(A, c[2]), smul(3*k, c[3])),
            c[3]]

def ibern3(e):
    return [smul(3, e[0]), add(smul(3, e[0]), e[1]), add(add(smul(3, e[0]), smul(2, e[1])), e[2]),
            smul(3, add(add(e[0], e[1]), add(e[2], e[3])))]

def ib33(c, ka, m, kb, n):
    """c[i][j]: integer polys; output out[I][J] = ibern3_J(ibern3_I(ishift3_u(ishift3_p)))."""
    rows = [ishift3(c[i], kb, n) for i in range(4)]          # rows[i][j]: shifted in p
    out = [[None]*4 for _ in range(4)]
    for j in range(4):
        col = ishift3([rows[i][j] for i in range(4)], ka, m)  # in u, index i
        bu = ibern3(col)                                       # index I
        for I in range(4):
            out[I][j] = bu[I]
    res = [[None]*4 for _ in range(4)]
    for I in range(4):
        bp = ibern3([out[I][j] for j in range(4)])
        for J in range(4):
            res[I][J] = bp[J]
    return res

def to_int16(U):
    D = 1
    for i in range(4):
        for j in range(4):
            for c in U[i][j]:
                D = lcm(D, Fr(c).denominator)
    return D, [[[int(Fr(c)*D) for c in U[i][j]] for j in range(4)] for i in range(4)]
