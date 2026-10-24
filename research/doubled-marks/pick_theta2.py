import sys, json, numpy as np
import os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import model69 as M
def edges2(c, h, BP, LP, sP=1/25):
    theta, ell, x, y, kappa = M.geometry(c, h)
    ds = 2*y/(1 + 6*kappa*sP); dk = 2*y/(2 - BP + LP*sP); dp = h + 1e-10
    CO = lambda d: min(d, 2*y - d)/(6*kappa)
    CN = lambda d: min(sP*d, (2*y - (2 - BP)*d)/LP)
    E = [("old_small", 1/200, CO(1/200)), ("old_peak", y, CO(y)), ("old_switch", ds, CO(ds)),
         ("new_switch", ds, CN(ds)), ("new_top", dp, CN(dp))]
    if dk < dp: E.append(("new_kink", dk, CN(dk)))
    return E, (ds < dk, dk < dp)
def gap(c, h, dl, pp, FC, FP, sP):
    theta, ell, x, y, kappa = M.geometry(c, h)
    Rs = M.count_envelope(kappa, dl, pp, (FC, FP), M.K_I_FINAL)
    worst = -np.inf
    E, order = edges2(c, h, FP.B, FP.Lam, sP)
    for name, d, C in E:
        e = (0.5 + 13*h/75 - y/2 - ell/2 - 9*d/100 + dl/2 + dl*pp*(ell - C/2) + 0.75*d*Rs)
        worst = max(worst, np.max(e - theta))
    return worst, order
def maxc(FC, FP, h, sP, dl, pp):
    lo, hi = 0.12522, 0.1262
    if gap(lo, h, dl, pp, FC, FP, sP)[0] > -1e-9: return 0, None
    for _ in range(40):
        mid = (lo+hi)/2
        if gap(mid, h, dl, pp, FC, FP, sP)[0] <= -1e-9: lo = mid
        else: hi = mid
    return lo, gap(lo, h, dl, pp, FC, FP, sP)[1]
if __name__ == "__main__":
    ch = json.load(open(sys.argv[1]))
    nC = ch[-1]; nP = min(ch, key=lambda n: abs(float(n.get('pivot', n.get('bx', 0))) - 0.0395))
    FC = M.Face(float(nC['B']), float(nC['L']), 11/250, 'C'); FP = M.Face(float(nP['B']), float(nP['L']), 43/1000, 'P')
    dl, pp = M.grid(601, 301)
    for sP in (1/25, 0.042):
        best = (0, None)
        for h in np.linspace(0.7994, 0.8010, 17):
            c, order = maxc(FC, FP, h, sP, dl, pp)
            if c > best[0]: best = (c, h, order)
            print(f"sP={sP:.4f} h={h:.5f} c={c:.11f} order(ds<dk, dk<d+)={order}", flush=True)
        print("best", best)
