"""Generalized float model of the final balance (built on model69's count envelope).
theta_low = 11/12 - ell/4 + epsL + epsM/12       (epsM: extra energy room, M = 1 - ell + epsM)
E(d) = 1/2 + 13h/75 - y/2 - ell/2 - 9d/100 + delta/2 + delta*p*(ell - C/2) + (3d/4)R  - epsE
with y = h - 2 ell + epsM.  theta* = min_h  (theta at the ell where max E = theta_low).
"""
import sys, os, json, numpy as np
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import model69 as M
from fractions import Fraction as Fr
nodes = json.load(open(os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'repeated-marks', 'cchain_k8b.json')))
def face(i): n = nodes[i]; return (float(Fr(n['B'])), float(Fr(n['L'])), float(Fr(n['cap'])))
Cf, Pf = face(58), face(52)
FC = M.Face(Cf[0], Cf[1], 13/250, 'C'); FP = M.Face(Pf[0], Pf[1], 43/1000, 'P')
BP, LP = FP.B, FP.Lam
DL, PP = M.grid(301, 151)
def edges(h, ell, y, kappa, sP=1/25):
    ds = 2*y/(1 + 6*kappa*sP); dk = 2*y/(2 - BP + LP*sP); dp = h + 1e-10
    CO = lambda d: min(d, 2*y - d)/(6*kappa)
    CN = lambda d: min(sP*d, (2*y - (2 - BP)*d)/LP)
    E = [("old_small", 1/200, CO(1/200)), ("old_peak", y, CO(y)), ("old_switch", ds, CO(ds)),
         ("new_switch", ds, CN(ds)), ("new_top", dp, CN(dp))]
    if dk < dp: E.append(("new_kink", dk, CN(dk)))
    return E
def gapf(ell, h, epsL=0., epsM=0., epsE=0., Rshift=0., Cshift=0., extra=None):
    th = 11/12 - ell/4 + epsL + epsM/12
    y = h - 2*ell + epsM
    kappa = 2*th - 1
    Rs = M.count_envelope(kappa, DL, PP, (FC, FP), M.K_I_FINAL) - Rshift
    worst = -np.inf; where=None
    for name, d, C in edges(h, ell, y, kappa):
        C = C + Cshift
        e = (0.5 + 13*h/75 - y/2 - ell/2 - 9*d/100 + DL/2 + DL*PP*(ell - C/2) + 0.75*d*Rs) - epsE
        if extra is not None: e = e + extra(d, h, ell, y, DL, PP, Rs)
        g = e - th
        i = np.unravel_index(np.argmax(g), g.shape)
        if g[i] > worst: worst, where = g[i], (name, float(DL[i]), float(PP[i]), float(Rs[i]))
    return worst, th, where
def best_ell(h, **kw):
    lo, hi = 0.160, 0.175
    for _ in range(40):
        mid = (lo+hi)/2
        if gapf(mid, h, **kw)[0] <= 0: lo = mid
        else: hi = mid
    return lo
def theta_star(hs=None, **kw):
    if hs is None: hs = np.linspace(0.7955, 0.8005, 11)
    best = (9, None, None)
    for h in hs:
        ell = best_ell(h, **kw)
        g, th, where = gapf(ell, h, **kw)
        if th < best[0]: best = (th, h, ell, where)
    # refine around best h
    h0 = best[1]; 
    for h in np.linspace(h0-0.0005, h0+0.0005, 11):
        ell = best_ell(h, **kw)
        g, th, where = gapf(ell, h, **kw)
        if th < best[0]: best = (th, h, ell, where)
    return best
if __name__ == "__main__":
    b0 = theta_star()
    print("base", b0, flush=True)
    for name, kw in [("epsL=1e-5", dict(epsL=1e-5)), ("epsE=1e-4", dict(epsE=1e-4)),
                     ("epsM=1e-3", dict(epsM=1e-3)), ("Rshift=1e-4", dict(Rshift=1e-4)),
                     ("Cshift=1e-3", dict(Cshift=1e-3))]:
        b = theta_star(**kw)
        print(name, b, "dtheta=", b[0]-b0[0], flush=True)
