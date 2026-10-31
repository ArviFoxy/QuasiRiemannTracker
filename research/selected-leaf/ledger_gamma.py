"""Price the selected branch of the E5 ledger when the selected norm has an excess gamma over its fixed point:
per root, norm exponent max(X, (1 - delta + gamma) y + delta X).  gamma = 0 is PR 93's fixed point (delta > 1/2);
gamma = 1/6 is the Theta6 closure below slope 1/2 (lean/arvi_kwall)."""
import sys, numpy as np
sys.path.insert(0, '/home/user/QuasiRiemannTracker/research/selected-leaf')
import root_ledger as R
from native_line import run

def e_sel_g(x1, x2, s, M, delta, gamma, nrho=601):
    P = x1 + x2; best = -1e9
    for rho in np.linspace(0.0, M / 6, nrho):
        y = M - 6 * rho
        if y < x1 or y < x2:
            continue
        xe = min(x1, y - x1) + min(x2, y - x2) + s
        per = max(xe, (1 - delta + gamma) * y + delta * xe)
        best = max(best, rho + per)
    return best

def worst_sel(B, L, c, a, delta, gamma, nS=21, nt=7):
    wv, where = -1e9, None
    for S in np.linspace(0.0, c, nS)[1:]:
        w = S; u = a * w; PCmax = B - L * S
        for PC in (PCmax, 0.75 * PCmax, 0.5 * PCmax):
            for s in (w - u, 0.5 * (w - u)):
                for t in np.linspace(0.0, 1 + 6 * u, nt):
                    M = 1 + t - 6 * u
                    for (x1, x2) in ((PC / 2, PC / 2), (PC, 0.0)):
                        v = e_sel_g(x1, x2, s, M, delta, gamma) - M - u
                        if v > wv:
                            wv, where = v, dict(S=round(S,4), PC=round(PC,4), s=round(s,4), M=round(M,3), x=(round(x1,3), round(x2,3)))
    return wv, where

if __name__ == "__main__":
  Lend, cend, reason, path = run(0.5 + 1e-3)
  for Lq in (2.2, 2.05, 2.01):
    i = min(range(len(path)), key=lambda j: abs(path[j][0] - Lq)); L, c, a = path[i]
    for delta, gamma in ((0.501, 0.0), (0.48, 1/6), (0.48, 0.05), (0.48, 0.02)):
        v, where = worst_sel(0.99999, L, c, a, delta, gamma)
        print('L=%.3f c=%.4f  delta=%.3f gamma=%.3f  max(sel price - u) = %+.4f  at %s' % (L, c, delta, gamma, v, where), flush=True)
