import sys, os, numpy as np
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from spcap2 import gap_sp
def theta_at(h, sP=0.045, **kw):
    lo, hi = 0.165, 0.170
    for _ in range(40):
        mid=(lo+hi)/2
        if gap_sp(mid,h,sP,**kw)[0] <= 0: lo=mid
        else: hi=mid
    g, th, where = gap_sp(lo,h,sP,**kw)
    return th, lo, where
h=0.802
b = theta_at(h); print("base", b, flush=True)
for kw in [dict(epsE=1e-4), dict(epsM=1e-3)]:
    t = theta_at(h, **kw); print(kw, t, "dtheta", t[0]-b[0], flush=True)
