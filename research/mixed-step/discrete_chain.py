"""Discrete greedy chain with the mixed LOW law (e = 1, c = 6, pool a = r), started on Sil's face.

Each step: parent (B0, L0, cap0) -> child with crossing s_c = s_prev + ds, i.e.
B = B0 - L0 s_c + L s_c; the child's slope L is the least one for which every gate of
`../faceless-chain/gates.py` holds at widths b in [s_c, cap] (both endpoints and interior points),
with the LOW and HIGH parent the previous face and q the largest value with den3 >= DMIN, q < 3/4.
This is the finite-step version of `continuum_mixed.py` (which treats each face as its own parent and
so ignores the jump from Sil's slope 93/25 down to the flow).
usage: python3 discrete_chain.py ds [s_start] [s_end] [CC]"""
import sys, os
import numpy as np
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'faceless-chain'))
import gates as G

CC = float(sys.argv[4]) if len(sys.argv) > 4 else 6.0
DMIN = 1e-6
QMAX = 0.7499

def basics_mixed(n, low, b):
    B, L, cap, q, e, r, f = n
    B0, L0 = low[0], low[1]
    t = B - L*(b - e)
    den = 1 + q - CC*q*B0/L0
    d = (q*(b + (t - B0)/L0) + r)/den
    return t, den, d, 1 - CC*d
G.basics = basics_mixed

def q_for(B0, L0):
    x = CC*B0/L0 - 1
    return QMAX if x <= 0 else min(QMAX, (1 - DMIN)/x)

def ok_child(par, s_c, L, cap=G.CAPMAX, nb=5, q=None):
    B0, L0, cap0 = par
    B = B0 - L0*s_c + L*s_c
    if B > 1 or B < 22/23: return False
    if q is None: q = q_for(B0, L0)
    if q < 0.5 or 1 + q - CC*q*B0/L0 < DMIN: return False
    n = G.node(B, L, cap, q, G.FINE)
    low = (B0, L0, cap0)
    for b in np.linspace(s_c, cap, nb):
        m = G.margins(n, low, low, b, nnu=11, npp=21, nfine=201)
        if m['scalar'] <= 0 or m['sector'] <= 0 or m['high'] <= 0:
            return False
    return True

def min_L(par, s_c, Lhi, q=None, it=30):
    if not ok_child(par, s_c, Lhi, q=q):
        # the weak cap can fail for small drops when the child's cap exceeds the parent's: scan down
        for k in range(1, 60):
            x = Lhi*(1 - 0.01*k)
            if ok_child(par, s_c, x, q=q): Lhi = x; break
        else:
            return None
    lo, hi = 0.5, Lhi
    if ok_child(par, s_c, lo, q=q): return lo
    for _ in range(it):
        mid = 0.5*(lo + hi)
        if ok_child(par, s_c, mid, q=q): hi = mid
        else: lo = mid
    return hi

QOPT = os.environ.get('QOPT') == '1'
def best_child(par, s_c):
    """Least slope over q (QOPT=1: a q grid below the den3 bound; else the largest q)."""
    if not QOPT:
        return min_L(par, s_c, par[1]*(1 - 1e-9)), q_for(par[0], par[1])
    qhi = q_for(par[0], par[1])
    best = (None, None)
    for q in np.linspace(0.5, qhi, 16):
        L = min_L(par, s_c, par[1]*(1 - 1e-9), q=q, it=24)
        if L is not None and (best[0] is None or L < best[0]): best = (L, q)
    return best

if __name__ == '__main__':
    ds = float(sys.argv[1])
    s = float(sys.argv[2]) if len(sys.argv) > 2 else 0.005
    s_end = float(sys.argv[3]) if len(sys.argv) > 3 else 0.0545
    par = (0.99999, 3.72, 0.06)
    while s <= s_end + 1e-12:
        L, q = best_child(par, s)
        if L is None:
            print(f"s={s:.4f}: no admissible child below the parent slope", flush=True)
            s = round(s + ds, 10); continue
        B = par[0] - par[1]*s + L*s
        print(f"s={s:.4f} B={B:.6f} L={L:.5f} E={B - L*s:.6f} q={q:.4f}", flush=True)
        par = (B, L, G.CAPMAX)
        s = round(s + ds, 10)
