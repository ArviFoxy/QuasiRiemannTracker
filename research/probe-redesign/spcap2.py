import sys, os, numpy as np
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import genmodel as G
from genmodel import M, FC, FP, DL, PP
def gap_sp(ell, h, sP, epsE=0.0, epsM=0.0):
    th = 11/12 - ell/4 + epsM/12; y = h - 2*ell + epsM; kappa = 2*th - 1
    Rs = M.count_envelope(kappa, DL, PP, (FC, FP), M.K_I_FINAL)
    worst=-np.inf; where=None
    for name, d, C in G.edges(h, ell, y, kappa, sP=sP):
        e = (0.5 + 13*h/75 - y/2 - ell/2 - 9*d/100 + DL/2 + DL*PP*(ell - C/2) + 0.75*d*Rs) - th - epsE
        i = np.unravel_index(np.argmax(e), e.shape)
        if e[i] > worst: worst, where = e[i], (name, round(d,5), round(C,5), float(DL[i]), float(PP[i]), round(float(Rs[i]),5))
    return worst, th, where
def best(sP, hs, **kw):
    res=[]
    for h in hs:
        lo, hi = 0.160, 0.175
        for _ in range(34):
            mid=(lo+hi)/2
            if gap_sp(mid,h,sP,**kw)[0] <= 0: lo=mid
            else: hi=mid
        g, th, where = gap_sp(lo, h, sP, **kw)
        res.append((th,h,lo,where))
        print(f"sP={sP} h={h:.4f} theta={th:.9f} ell={lo:.6f} bind={where}", flush=True)
    return res
if __name__ == "__main__":
  sP = float(sys.argv[1]) if len(sys.argv) > 1 else 0.045
  res = best(sP, np.linspace(0.798, 0.818, 11))
  print("BEST", min(res), flush=True)
