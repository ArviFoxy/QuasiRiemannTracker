"""k_min for zeros on one vertical line (Re = a - d), equally spaced heights omega/L, free coefficients."""
import numpy as np, sys
from expsum_dip import solve, trig_config

def kmin(L, omega, bounded, d=0.0, kmax=400, **kw):
    def ok(k):
        return solve(trig_config(k, omega, L, d), L, bounded=bounded, **kw)[0] <= 1.0
    lo, hi = 1, 4
    while not ok(hi):
        lo = hi; hi = int(hi*1.5)+1
        if hi > kmax: return None
    while hi - lo > 1:
        mid = (lo+hi)//2
        if ok(mid): hi = mid
        else: lo = mid
    return hi

if __name__ == "__main__":
    L = float(sys.argv[1]); bounded = sys.argv[2] == "b"
    d = float(sys.argv[3]) if len(sys.argv) > 3 else 0.0
    for omega in [0.25, 0.5, 1.0, 2.0, 3.0, 4.0, 6.0, 8.0, 12.0]:
        k = kmin(L, omega, bounded, d)
        print(f"L={L:.0f} bounded={bounded} d={d} omega={omega:5.2f}  k_min={k}  k/L={(k or np.nan)/L:.4f}  height-span={(k or np.nan)*omega/L:.4f}", flush=True)
