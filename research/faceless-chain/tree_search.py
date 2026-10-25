"""Find, per piece / branch / width endpoint, a (u, p) bisection tree whose leaf Bernstein coefficients
(polynomials in x) are positive on the whole piece by TM1 (with s-subdivision)."""
import sys, time, json
from fractions import Fraction as Fr
import polyq as P
import family as Fm
import cert_proto as CP

MAXINT = 64

def leaf_ok(U, a, s, b, t, lo, hi):
    BB = CP.bern33(U, a, s, b, t)
    br = []
    for I in range(4):
        for J in range(4):
            x = P.tm1_split(BB[I][J], lo, hi, maxdepth=8)
            if x is None or len(x) - 1 > MAXINT:
                return None
            br.append(len(x) - 1)
    return br

def find(U, a, s, b, t, lo, hi, depth=0, maxdepth=10):
    r = leaf_ok(U, a, s, b, t, lo, hi)
    if r is not None:
        return ('leaf', sum(r))
    if depth >= maxdepth:
        return None
    # split the longer side in relative terms (u in [0,1], p in [0,1/2])
    for dim in (('u', 'p') if s >= 2*t else ('p', 'u')):
        if dim == 'u':
            L_ = find(U, a, s/2, b, t, lo, hi, depth + 1, maxdepth)
            R_ = L_ and find(U, a + s/2, s/2, b, t, lo, hi, depth + 1, maxdepth)
        else:
            L_ = find(U, a, s, b, t/2, lo, hi, depth + 1, maxdepth)
            R_ = L_ and find(U, a, s, b + t/2, t/2, lo, hi, depth + 1, maxdepth)
        if L_ and R_:
            return (dim, L_, R_)
    return None

def size(T):
    if T is None: return (None, None)
    if T[0] == 'leaf': return (1, T[1])
    a = size(T[1]); b = size(T[2]); return (a[0] + b[0], a[1] + b[1])

if __name__ == "__main__":
    sig = [float(x) for x in sys.argv[1].split(',')]
    fam, _ = Fm.build(sig, 2e-5, 1e-4)
    e, r, f = Fm.FEES; cap = Fm.CAPMAX; den = fam.den; D = fam.Delta
    tot_leaves = tot_int = 0
    for j in range(len(fam.sig) - 1):
        h = fam.sig[j + 1] - fam.sig[j]
        for bk in ('cross', 'cap'):
            for k in [(i, jj) for i in range(2) for jj in range(3)]:
                t0 = time.time()
                U, _ = CP.high_polys(fam, j, bk, k, e, r, f, cap, den)
                T = find(U, Fr(0), Fr(1), Fr(0), Fr(1, 2), D, h - D)
                nl, ni = size(T)
                print(f"piece {j} {bk:5s} branch {k}: leaves {nl} TM1 intervals {ni}  ({time.time()-t0:.1f}s)", flush=True)
                if nl: tot_leaves += nl; tot_int += ni
    print("total leaves", tot_leaves, "total TM1 checks", tot_int)
