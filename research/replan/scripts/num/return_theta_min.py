import numpy as np, sys
from scipy.optimize import brentq
from return_replica import Faces, Ret
from return_opt import worst_need

def margin(c, h, F, n=301, refine=False):
    r = Ret(c,h,F)
    val,e,dl,p,b = worst_need(r, n=n, refine=refine)
    return (r.theta - F.reserve) - val, (e,dl,p,b)

def theta_min(F, hs=np.linspace(0.790,0.815,26), n=241):
    """For each h, largest c (smallest theta) with margin >= 0; return best."""
    best=None
    for h in hs:
        # margin increases as c decreases (theta bigger)? scan c from 0.12 to 0.13
        cs = np.linspace(0.118, 0.132, 15)
        ms = [margin(c,h,F,n)[0] for c in cs]
        # find largest c with margin>=0
        ok = [c for c,m in zip(cs,ms) if m>=0]
        if not ok: continue
        c_hi = max(ok)
        # bracket to the next c where margin<0
        idx = list(cs).index(c_hi)
        if idx+1<len(cs):
            try:
                c_root = brentq(lambda c: margin(c,h,F,n)[0], c_hi, cs[idx+1], xtol=1e-9)
            except Exception:
                c_root = c_hi
        else:
            c_root = c_hi
        th = 1-c_root
        if best is None or th<best[0]: best=(th,h,c_root)
    return best

if __name__=='__main__':
    F = Faces()
    print("margin at actual:", margin(25201/200000, 8053/10000, F, 601, True))
    best = theta_min(F)
    print("min theta over h in grid: theta=%.6f at h=%.4f (c=%.6f)" % best)
