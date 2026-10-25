import sys, os, numpy as np
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import genmodel as G
from genmodel import M, FC, FP, DL, PP, BP, LP
def gap_sp(ell, h, sP):
    th = 11/12 - ell/4; y = h - 2*ell; kappa = 2*th - 1
    Rs = M.count_envelope(kappa, DL, PP, (FC, FP), M.K_I_FINAL)
    worst=-np.inf; where=None
    for name, d, C in G.edges(h, ell, y, kappa, sP=sP):
        e = (0.5 + 13*h/75 - y/2 - ell/2 - 9*d/100 + DL/2 + DL*PP*(ell - C/2) + 0.75*d*Rs) - th
        i = np.unravel_index(np.argmax(e), e.shape)
        if e[i] > worst: worst, where = e[i], (name, float(DL[i]), float(PP[i]))
    return worst, th, where
def best(sP, hs):
    out=(9,None)
    for h in hs:
        lo, hi = 0.160, 0.175
        for _ in range(36):
            mid=(lo+hi)/2
            if gap_sp(mid,h,sP)[0] <= 0: lo=mid
            else: hi=mid
        g, th, where = gap_sp(lo, h, sP)
        if th < out[0]: out=(th,h,lo,where)
    return out
for sP in [0.040, 0.042, 0.043]:
    b = best(sP, np.linspace(0.796, 0.812, 17))
    print(f"sP={sP}: theta={b[0]:.9f} h={b[1]:.4f} ell={b[2]:.6f} bind={b[3]}", flush=True)
