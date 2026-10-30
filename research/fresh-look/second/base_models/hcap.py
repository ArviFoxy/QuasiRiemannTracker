# newTop-only: theta*(h, numCap) with the banked count (count independent of h) -- precompute spline once
import numpy as np, slotcost as S
from scipy.interpolate import CubicSpline
cap = lambda L: 0.1 + 0.06 * (5143 / 2000 - L)
B, L = 0.99999, 2.0001
dls = np.round(np.arange(0.30, 0.6001, 0.005), 4)
cs = CubicSpline(dls, [S.count(dd, 0.5, B, L, cap(L), 2.0) for dd in dls])
dl = np.linspace(0.30, 0.60, 30001); cn = cs(dl)
def th(h, numcap, p=0.5, reserve=1e-8):
    lo, hi = 0.85, 0.88
    for _ in range(60):
        t = (lo+hi)/2; c = 1-t; ell = 4*c-1/3; y = h-2*ell; dp = h+1e-10
        C = min(numcap*dp, (2*y-(2-B)*dp)/L)
        row = (0.5+13*h/75-y/2-ell/2-0.09*dp+dl/2+dl*p*(ell-C/2)+0.75*dp*cn)
        if row.max() > t-reserve: lo = t
        else: hi = t
    i = np.argmax(row); return hi, dl[i], C
for nc in (0.075, 0.10, 0.12, 0.15, 0.20):
    out = []
    for h in (0.8097, 0.83, 0.85, 0.87, 0.89, 0.91):
        t, d, C = th(h, nc); out.append('h%.3f:%.8f(d*%.3f,C%.4f)' % (h, t, d, C))
    print('numCap %.3f  ' % nc + '  '.join(out))
