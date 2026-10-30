"""Exact Python mirror of Submissions/arvi_return_tuning/{Poly2,GuardsQ,Data,RowsQ}.lean.

Same list representations and operations (no trimming), same Bernstein candidate certificate, same
subdivision rule, so it predicts exactly which kernel checks pass and how many Bernstein tests they run.
"""
from fractions import Fraction as Fr
from math import comb

# ---------------- Q1 / Q2 ----------------

def q1add(p, q):
    if not p:
        return list(q)
    if not q:
        return list(p)
    return [p[0] + q[0]] + q1add(p[1:], q[1:])


def q1smul(c, p):
    return [c * x for x in p]


def q1mul(p, q):
    if not p:
        return []
    return q1add(q1smul(p[0], q), [Fr(0)] + q1mul(p[1:], q))


def q1subst(q, c, s):
    acc = []
    for k in reversed(q):
        acc = q1add([k], q1mul([c, s], acc))
    return acc


def add(P, Q):
    if not P:
        return [list(r) for r in Q]
    if not Q:
        return [list(r) for r in P]
    return [q1add(P[0], Q[0])] + add(P[1:], Q[1:])


def smul(c, P):
    return [q1smul(c, r) for r in P]


def mulQ1(a, P):
    return [q1mul(a, r) for r in P]


def mul(P, Q):
    if not P:
        return []
    return add(mulQ1(P[0], Q), [[]] + mul(P[1:], Q))


def sub(P, Q):
    return add(P, smul(Fr(-1), Q))


def C(c):
    return [[Fr(c)]]


X = [[], [Fr(1)]]
Y = [[Fr(0), Fr(1)]]


def subst2(P, a, s, c, t):
    acc = []
    for Pi in reversed(P):
        acc = add([q1subst(Pi, c, t)], mul([[a], [s]], acc))
    return acc


def isZero(P):
    return all(x == 0 for r in P for x in r)


def degD(P):
    return max(len(P) - 1, 0)


def degP(P):
    m = 0
    for r in P:
        m = max(m, len(r))
    return max(m - 1, 0)


def getD(l, i, d):
    return l[i] if i < len(l) else d


def adjSum(l):
    return [l[i] + l[i + 1] for i in range(len(l) - 1)]


def binomT(k, l):
    out = []
    for _ in range(k):
        out.append(l[0] if l else Fr(0))
        l = adjSum(l)
    return out


def scaleBinom(n, c):
    return [getD(c, i, Fr(0)) / comb(n, i) for i in range(n + 1)]


def bern1(n, c):
    return binomT(n + 1, scaleBinom(n, c))


def cols(m, rows):
    return [[getD(r, j, Fr(0)) for r in rows] for j in range(m + 1)]


def bern2(q, n, m):
    rowsW = [bern1(m, getD(q, i, [])) for i in range(n + 1)]
    colsU = [bern1(n, c) for c in cols(m, rowsW)]
    return cols(n, colsU)


def bpoly(a, b, n, i):
    def pw(p, k):
        r = [Fr(1)]
        for _ in range(k):
            r = q1mul(p, r)
        return r
    return q1mul(pw([-a, Fr(1)], i), pw([b, Fr(-1)], n - i))


def outer(u, v):
    return [q1smul(k, v) for k in u]


def bernCert(P, a, b, c, e):
    n, m = degD(P), degP(P)
    beta = bern2(subst2(P, a, b - a, c, e - c), n, m)
    allv = [x for r in beta for x in r]
    mn = min(allv) if allv else Fr(0)
    W = (b - a) ** n * (e - c) ** m
    l = [(I, [((getD(getD(beta, I, []), J, Fr(0)) - mn) * comb(n, I) * comb(m, J) / W, J) for J in range(m + 1)])
         for I in range(n + 1)]
    return mn, l


STATS = {'bern': 0}


def bernCheck(P, a, b, c, e, verify=False):
    STATS['bern'] += 1
    mn, l = bernCert(P, a, b, c, e)
    if not mn > 0:
        return False
    if verify:   # the identity check of checkCert (always true when mn > 0; kept as a self-test)
        n, m = degD(P), degP(P)
        S = []
        for I, r in l:
            inner = []
            for g, J in r:
                assert g >= 0
                inner = q1add(q1smul(g, bpoly(c, e, m, J)), inner)
            S = add(outer(bpoly(a, b, n, I), inner), S)
        assert isZero(sub(P, add(C(mn), S))), 'certificate identity'
    return True


def posBox(P, k, a, b, c, e):
    if bernCheck(P, a, b, c, e):
        return True
    if k == 0:
        return False
    if 3 * (e - c) <= 2 * (b - a):
        mid = (a + b) / 2
        return posBox(P, k - 1, a, mid, c, e) and posBox(P, k - 1, mid, b, c, e)
    mid = (c + e) / 2
    return posBox(P, k - 1, a, b, c, mid) and posBox(P, k - 1, a, b, mid, e)


# ---------------- constants (Data.lean) ----------------
ETA = Fr(1, 10 ** 7)
mMinusQ, sMinusQ, naturalKQ = Fr(377, 1000), Fr(3, 100), Fr(9, 2)
naturalMQ = (1 - naturalKQ * sMinusQ) / 2
ELEVEN = Fr(11, 25)

def set_constants(mMinus, sMinus, eleven):
    global mMinusQ, sMinusQ, naturalMQ, ELEVEN
    mMinusQ, sMinusQ, ELEVEN = Fr(mMinus), Fr(sMinus), Fr(eleven)
    naturalMQ = (1 - naturalKQ * sMinusQ) / 2



class Const:
    def __init__(self, c=Fr(6306383, 50000000), h=Fr(8044451, 10000000), reserve=Fr(1, 10 ** 8),
                 cB=Fr(96232839, 100000000), cL=Fr(3853, 2000), cCap=Fr(9999, 100000),
                 pB=Fr(49283557, 50000000), pL=Fr(4503, 2000), pCap=Fr(31, 500), numCap=Fr(3, 50), dm=Fr(19, 25), w=Fr(7, 4000)):
        self.c, self.h, self.reserve = c, h, reserve
        self.cB, self.cL, self.cCap, self.pB, self.pL, self.pCap = cB, cL, cCap, pB, pL, pCap
        self.numCap, self.dm, self.w = numCap, dm, w
        self.theta = 1 - c
        self.ell = 4 * c - Fr(1, 3)
        self.y = h - 2 * self.ell
        self.kappa = 1 - 2 * c
        self.dp = h + Fr(1, 10 ** 10)
        self.d0 = Fr(1, 200)

    def oldCap(self, d):
        return min(d, 2 * self.y - d) / (6 * self.kappa)

    def newCap(self, d):
        return min(self.numCap * d, (2 * self.y - (2 - self.pB) * d) / self.pL)

    def edge(self, e):
        d = {'oldSmall': self.d0, 'oldSwitch': self.dm, 'newSwitch': self.dm, 'newTop': self.dp}[e]
        cap = self.oldCap(d) if e in ('oldSmall', 'oldSwitch') else self.newCap(d)
        return d, cap

    def toQ(self, b):
        return {'C': (self.cB, self.cL, self.cCap, False), 'capC': (self.cB, self.cL, self.cCap, True),
                'weakC7': (self.cB - self.w, self.cL, self.cCap, False),
                'capP': (self.pB, self.pL, self.pCap, True)}[b]


# ---------------- BranchQ (GuardsQ.lean) ----------------

def branch_polys(bq):
    B, L, cap, capped = bq
    Zc = cap - ETA
    V = sub(C(Fr(5, 6)), X)
    if capped:
        D = sub(C(3), Y); A = C(2); C0 = sub(C(1), smul(2 * Zc, Y)); Z = smul(2 * Zc, Y)
        dD, dA, dC = Fr(-1), Fr(0), -2 * Zc
    else:
        D = sub(sub(C(3), Y), smul(4 / L, Y)); A = sub(C(2), smul(4 / L, Y))
        C0 = sub(C(1), smul(2 * B / L, Y)); Z = smul(2 * B / L, Y)
        dD, dA, dC = -1 - 4 / L, -4 / L, -2 * B / L
    U = mul(sub(C(1), Y), C0)
    J = add(mul(V, D), mul(mul(X, sub(C(1), Y)), A))
    N = add(mul(sub(C(1), X), J), mul(mul(V, X), U))
    T = add(J, mul(X, U))
    RN = add(mul(A, T), mul(sub(Z, Y), J))
    MN = sub(mul(D, T), RN)
    DJ = mul(D, J)
    dU = add(smul(Fr(-1), C0), smul(dC, sub(C(1), Y)))
    dJ = add(smul(dD, V), mul(X, add(smul(Fr(-1), A), smul(dA, sub(C(1), Y)))))
    if capped:
        lowerM = mMinusQ + ETA
        upperM = min(min(ELEVEN - ETA, naturalMQ - ETA), (B - L * Zc) / 2 - ETA)
    else:
        lowerM = max(mMinusQ + ETA, (B - L * (cap - ETA)) / 2 + ETA)
        upperM = min(min(ELEVEN - ETA, naturalMQ - ETA), (B - L * (sMinusQ + ETA)) / 2 - ETA)
    g = [D, A, C0, J, sub(T, J), sub(smul(Fr(12499, 10000), J), T),
         sub(RN, smul(Fr(23, 37), DJ)), sub(DJ, RN),
         sub(MN, smul(lowerM, DJ)), sub(smul(upperM, DJ), MN),
         sub(N, mul(sub(sub(C(1), smul(2 * naturalMQ, X)), smul(2 * sMinusQ, mul(X, Y))), J)),
         sub(mul(U, dJ), mul(dU, J)),
         C(ELEVEN - naturalMQ - ETA),
         C(B - 2 * naturalMQ - L * (sMinusQ + ETA) - 2 * ETA),
         smul(Zc - sMinusQ - ETA, DJ) if capped else C(1)]
    return dict(J=J, N=N, V=V, guards=g)


def windowCheck(bq, k, dlo, dhi, plo):
    g = branch_polys(bq)['guards']
    return all(posBox(gj, k, dlo, dhi, plo, Fr(1, 2)) for gj in g)


# ---------------- rows (RowsQ.lean) ----------------

def EbaseQ(K, d, cap):
    return add(C(Fr(1, 2) + 13 * K.h / 75 - K.y / 2 - K.ell / 2 - Fr(9, 100) * d),
               add(smul(Fr(1, 2), X), smul(K.ell - cap / 2, mul(X, Y))))


def rowQ(K, d, cap, J, N):
    return sub(mul(J, sub(C(K.theta - K.reserve), EbaseQ(K, d, cap))), smul(Fr(3, 4) * d, N))


def oldJN(K):
    V = sub(C(Fr(5, 6)), X)
    oldD = sub(sub(C(3), Y), smul(2 / (3 * K.kappa), Y))
    oldC = mul(smul(2, sub(C(1), Y)), sub(C(1), smul(1 / (3 * K.kappa), Y)))
    J = add(mul(V, oldD), mul(X, oldC))
    N = add(mul(sub(C(1), X), J), smul(Fr(1, 2), mul(mul(X, oldC), V)))
    return J, N


def rowOld(K, e):
    d, cap = K.edge(e)
    J, N = oldJN(K)
    return rowQ(K, d, cap, J, N)


def rowBr(K, e, bq):
    d, cap = K.edge(e)
    br = branch_polys(bq)
    return rowQ(K, d, cap, br['J'], br['N'])
