import os, sys, numpy as np
sys.path.insert(0, '/home/user/QuasiRiemannTracker/research/selected-leaf')
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import root_ledger as R
from native_line import run
from ledger_gamma import e_sel_g

def worst_sel_min(B, L, c, a, B0, L0, c0, delta, gamma, nS=41, nt=9):
    wv, where = -1e9, None
    for S in np.linspace(0.0, c, nS)[1:]:
        w = S; u = a * w; PCmax = B - L * S
        for PC in np.linspace(0.5 * PCmax, PCmax, 6):
            for s in (w - u, 0.75 * (w - u), 0.5 * (w - u)):
                for t in np.linspace(0.0, 1 + 6 * u, nt):
                    M = 1 + t - 6 * u
                    for frac in (0.5, 0.4, 0.3, 0.0):
                        x1, x2 = PC * (1 - frac), PC * frac
                        sel = e_sel_g(x1, x2, s, M, delta, gamma, nrho=241) - M
                        par = R.deletion_need(B0, L0, c0, PC, s, M)       # parent face on all rows
                        v = min(sel, par) - u
                        if v > wv:
                            wv, where = v, dict(S=round(S,4), PC=round(PC,4), s=round(s,4), M=round(M,3), x=(round(x1,3), round(x2,3)), sel=round(sel,4), par=round(par,4))
    return wv, where

if __name__ == "__main__":
  Lend, cend, reason, path = run(0.5 + 1e-3)
  for Lq in (2.2, 2.05):
    i = min(range(len(path)), key=lambda j: abs(path[j][0] - Lq)); L, c, a = path[i]; L0, c0, _ = path[i - 1]
    for delta, gamma in ((0.501, 0.0), (0.48, 1/6), (0.48, 0.05)):
        v, where = worst_sel_min(0.99999, L, c, a, 0.99999, L0, c0, delta, gamma)
        print('L=%.3f  delta=%.3f gamma=%.3f  max(min(sel,parent) - u) = %+.4f  at %s' % (L, delta, gamma, v, where), flush=True)
