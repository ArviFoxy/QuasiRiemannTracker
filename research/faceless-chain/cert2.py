"""Certificate prototype on family v2 (polynomials in y in [0,1])."""
import sys, time
from fractions import Fraction as Fr
import polyq as P
import family2 as F2
import cert_proto as CP

def high_polys2(fam, j, bk, k):
    e, r, f = F2.FEES; cap = F2.CAPMAX; den = fam.den
    B, L, B0, L0, sv = fam.polys(j)
    b = sv if bk == 'cross' else [cap]
    t = P.sub(B, P.mul(L, P.sub(b, [e])))
    T = P.add(t, b); S = P.sub(b, [2*e])
    Dn = P.smul(6*den, B0)
    Na = P.add(P.smul(1 - den, P.add(P.mul(L0, b), P.sub(t, B0))), P.smul(6*r, B0))
    NF = P.sub(P.sub(Dn, P.smul(6, Na)), P.smul(e, Dn))
    vals = {}
    for nu in CP.NU_PTS:
        for p in CP.NU_PTS:
            G0 = CP.gateG([], T, S, [], f, 8, B0, L0, cap, nu, p, k)
            Ga = P.sub(CP.gateG([Fr(1)], T, S, [], f, 8, B0, L0, cap, nu, p, k), G0)
            GF = P.sub(CP.gateG([], T, S, [Fr(1)], f, 8, B0, L0, cap, nu, p, k), G0)
            vals[(nu, p)] = P.add(P.add(P.mul(Dn, G0), P.mul(Ga, Na)), P.mul(GF, NF))
    rowsp = {nu: CP.cubic4([vals[(nu, p)] for p in CP.NU_PTS]) for nu in CP.NU_PTS}
    C = [[None]*4 for _ in range(4)]
    for jj in range(4):
        col = CP.cubic4([rowsp[nu][jj] for nu in CP.NU_PTS])
        for i in range(4): C[i][jj] = col[i]
    from math import comb
    Nq = P.smul(1 - den, L0); D6 = P.smul(6, B0)
    al = Nq; be = P.sub(P.smul(Fr(9, 2), B0), Nq)
    pw = lambda p_, n: [Fr(1)] if n == 0 else P.mul(p_, pw(p_, n - 1))
    U = [[[] for _ in range(4)] for _ in range(4)]
    for a_ in range(4):
        for jj in range(4):
            acc = []
            for i in range(a_, 4):
                acc = P.add(acc, P.smul(comb(i, a_), P.mul(P.mul(C[i][jj], pw(al, i - a_)), P.mul(pw(be, a_), pw(D6, 3 - i)))))
            U[a_][jj] = acc
    return U

def dyadic_split(p, lo, hi, depth=0, maxdepth=12):
    if P.tm1(p, lo, hi - lo): return [lo, hi]
    if depth >= maxdepth: return None
    m = (lo + hi)/2
    l = dyadic_split(p, lo, m, depth + 1, maxdepth)
    if l is None: return None
    r = dyadic_split(p, m, hi, depth + 1, maxdepth)
    return None if r is None else l[:-1] + r

def leaf_ok(U, a, s, b, t, lo, hi, maxint=64):
    BB = CP.bern33(U, a, s, b, t); n = 0
    for I in range(4):
        for J in range(4):
            x = dyadic_split(BB[I][J], lo, hi, maxdepth=8)
            if x is None or len(x) - 1 > maxint: return None
            n += len(x) - 1
    return n

def find(U, a, s, b, t, lo, hi, depth=0, maxdepth=10):
    r = leaf_ok(U, a, s, b, t, lo, hi)
    if r is not None: return ('leaf', r)
    if depth >= maxdepth: return None
    for dim in (('u', 'p') if s >= 2*t else ('p', 'u')):
        if dim == 'u':
            L_ = find(U, a, s/2, b, t, lo, hi, depth + 1, maxdepth); R_ = L_ and find(U, a + s/2, s/2, b, t, lo, hi, depth + 1, maxdepth)
        else:
            L_ = find(U, a, s, b, t/2, lo, hi, depth + 1, maxdepth); R_ = L_ and find(U, a, s, b + t/2, t/2, lo, hi, depth + 1, maxdepth)
        if L_ and R_: return (dim, L_, R_)
    return None

def size(T):
    if T is None: return (None, None)
    if T[0] == 'leaf': return (1, T[1])
    a = size(T[1]); b = size(T[2]); return (a[0] + b[0], a[1] + b[1])

if __name__ == "__main__":
    sig = [float(x) for x in sys.argv[1].split(',')]
    m = int(sys.argv[2]) if len(sys.argv) > 2 else 16
    fam, _ = F2.build2(sig, m=m)
    Dy = fam.Dy
    tl = ti = 0; dg = 0
    for j in range(len(fam.H)):
        for bk in ('cross', 'cap'):
            for k in [(i, jj) for i in range(2) for jj in range(3)]:
                U = high_polys2(fam, j, bk, k)
                dg = max(dg, max(P.digits(U[a][b]) for a in range(4) for b in range(4)))
                T = find(U, Fr(0), Fr(1), Fr(0), Fr(1, 2), Dy, 1 - Dy)
                nl, ni = size(T)
                if bk == 'cross' and k[0] == 1: print(f"piece {j} {bk} {k}: leaves {nl} intervals {ni}", flush=True)
                if nl: tl += nl; ti += ni
                else: print("FAIL", j, bk, k)
    print("digits", dg, "total leaves", tl, "total TM1", ti)
