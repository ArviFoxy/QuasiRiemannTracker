r"""Tight-cluster (confluent) model: profile g(v) = exp(-L*dc*v) * P(v), P real polynomial of degree n.
Find minimal n such that
   |g(r1)| >= 1, |g(r2)| >= 1                     (saturation at r*, t*)
   |g(v)| <= exp(-theta*c(v)*L) on (r1, r2)       (tent dip)
   [bounded]  |g(v)| <= B on [0, V] minus (r1,r2) (pointwise bound from zero-free region)
LP in Chebyshev coefficients; objective t = max violation factor in the dip region.
"""
import numpy as np, sys
from scipy.optimize import linprog
from numpy.polynomial import chebyshev as C
from common import R1, R2, tent

def solve(n, L, theta=1.0, bounded=False, V=3.0, B=1.0, dc=0.0, sign=1, ngrid=None):
    lo, hi = (0.0, V) if bounded else (R1, R2)
    def basis(v):
        x = (2*np.asarray(v) - (lo+hi))/(hi-lo)
        return C.chebvander(x, n)
    m = ngrid or max(400, 12*n)
    # dip grid (Chebyshev-like clustering near ends)
    th = np.linspace(0, np.pi, m+2)[1:-1]
    vin = 0.5*(R1+R2) - 0.5*(R2-R1)*np.cos(th)
    bound_in = np.exp(-theta*tent(vin)*L + L*dc*vin)     # bound on |P|
    A_in = basis(vin) / bound_in[:, None]
    nv = n+1
    # variables: a_0..a_n, t ; minimize t
    rows = []; rhs = []
    for s in (+1, -1):
        rows.append(np.hstack([s*A_in, -np.ones((m, 1))])); rhs.append(np.zeros(m))
    if bounded:
        mo = max(400, 12*n)
        vout = np.concatenate([np.linspace(0, R1, mo), np.linspace(R2, V, mo)])
        bo = B*np.exp(L*dc*vout)
        A_out = basis(vout)/bo[:, None]
        for s in (+1, -1):
            rows.append(np.hstack([s*A_out, np.zeros((len(vout), 1))])); rhs.append(np.ones(len(vout)))
    A_ub = np.vstack(rows); b_ub = np.concatenate(rhs)
    e1 = np.exp(L*dc*R1); e2 = np.exp(L*dc*R2)
    A_eq = np.vstack([np.hstack([basis([R1])[0]/e1, [0.0]]),
                      np.hstack([basis([R2])[0]/e2, [0.0]])])
    b_eq = np.array([1.0, float(sign)])
    cobj = np.zeros(nv+1); cobj[-1] = 1.0
    bnds = [(None, None)]*nv + [(0, None)]
    res = linprog(cobj, A_ub=A_ub, b_ub=b_ub, A_eq=A_eq, b_eq=b_eq, bounds=bnds, method="highs")
    if res.status != 0:
        return np.inf, None
    return res.x[-1], res.x[:-1]

def nmin(L, theta=1.0, bounded=False, **kw):
    """smallest n with optimal t <= 1 (bisection on n, both signs)."""
    def ok(n):
        return min(solve(n, L, theta, bounded, sign=s, **kw)[0] for s in (1, -1)) <= 1.0
    lo, hi = 1, 8
    while not ok(hi):
        lo = hi; hi *= 2
        if hi > 2000: return None
    while hi - lo > 1:
        mid = (lo+hi)//2
        if ok(mid): hi = mid
        else: lo = mid
    return hi

if __name__ == "__main__":
    for L in [100, 200, 400]:
        for bounded in (False, True):
            n = nmin(L, 1.0, bounded)
            print(f"L={L:5d} bounded={bounded!s:5}  n_min={n}  kappa=n/L={n/L:.4f}", flush=True)
