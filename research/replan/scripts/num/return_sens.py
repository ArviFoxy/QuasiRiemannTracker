import numpy as np, copy
from scipy.optimize import brentq
from return_replica import Faces, Ret
from return_opt import worst_need

def margin(c, h, F, n=241):
    r = Ret(c,h,F)
    val,e,dl,p,b = worst_need(r, n=n, refine=False)
    return (r.theta - F.reserve) - val, (e,round(float(dl),4),round(float(p),4),b)

def theta_min(F, hs=np.linspace(0.796,0.808,13), n=241, clo=0.115, chi=0.135):
    best=None
    for h in hs:
        f = lambda c: margin(c,h,F,n)[0]
        # margin(c) decreasing in c; find root in [clo,chi] if sign change
        flo, fhi = f(clo), f(chi)
        if flo<0: continue
        if fhi>0: root=chi
        else: root = brentq(f, clo, chi, xtol=1e-9)
        th=1-root
        if best is None or th<best[0]: best=(th,h,root)
    return best

def show(label, F):
    b = theta_min(F)
    c=b[2]; h=b[1]
    m,info = margin(c,h,F)
    print("%-52s theta_min=%.6f (h=%.4f)  binding=%s" % (label, b[0], h, info))

if __name__=='__main__':
    F0 = Faces()
    show("baseline faces (B,L,cap)=(.9934,2.45,.09999)", F0)
    # Vary count-face L (and physical face L = L_C + 0.001)
    for L in [2.50, 2.45, 2.40, 2.35, 2.30]:
        F = copy.deepcopy(F0); F.CL=L; F.PL=L+0.001
        show("L=%.2f (P face L+0.001)" % L, F)
    # Vary B
    for B in [0.996, 0.9934, 0.990, 0.985, 0.98]:
        F = copy.deepcopy(F0); F.CB=B; F.PB=B-1e-7
        show("B=%.4f" % B, F)
    # Vary caps
    for cap in [0.08, 0.09999, 0.12, 0.14]:
        F = copy.deepcopy(F0); F.Ccap=cap
        show("count cap=%.5f" % cap, F)
    for cap in [0.055, 0.062, 0.08, 0.10]:
        F = copy.deepcopy(F0); F.Pcap=cap
        show("physical-face cap=%.4f" % cap, F)
    for nc in [0.05, 0.06, 0.07]:
        F = copy.deepcopy(F0); F.numeratorCap=nc
        show("numeratorCap=%.3f" % nc, F)
