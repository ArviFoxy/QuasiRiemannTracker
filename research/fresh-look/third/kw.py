# K-wall ledger with the child face restricted to slot widths S >= s0 (parent unrestricted): which gamma passes?
import sys, time, numpy as np
sys.path.insert(0, '/home/user/QuasiRiemannTracker/research/selected-leaf')
from native_line import run
import root_ledger as R
def e_sel_vec(x1, x2, s, M, delta, gamma, nrho=241):
    rho = np.linspace(0.0, M/6, nrho); y = M - 6*rho
    ok = (y >= x1) & (y >= x2)
    xe = np.minimum(x1, y - x1) + np.minimum(x2, y - x2) + s
    per = np.maximum(xe, (1 - delta + gamma)*y + delta*xe)
    v = np.where(ok, rho + per, -1e9)
    return v.max()
def worst(B, L, c, a, B0, L0, c0, delta, gamma, s0, nS=41, nt=9):
    wv, where = -1e9, None
    for S in np.linspace(0.0, c, nS)[1:]:
        if S < s0: continue
        w = S; u = a*w; PCmax = B - L*S
        for PC in np.linspace(0.5*PCmax, PCmax, 6):
            for s in (w - u, 0.75*(w - u), 0.5*(w - u)):
                for t in np.linspace(0.0, 1 + 6*u, nt):
                    M = 1 + t - 6*u
                    for frac in (0.5, 0.4, 0.3, 0.0):
                        x1, x2 = PC*(1 - frac), PC*frac
                        sel = e_sel_vec(x1, x2, s, M, delta, gamma) - M
                        par = R.deletion_need(B0, L0, c0, PC, s, M)
                        v = min(sel, par) - u
                        if v > wv: wv, where = v, (round(S,4), round(PC,3), round(s,4), round(M,4), round(x1,3), round(x2,3), round(sel,5), round(par,5), u)
    return wv, where
K = float(sys.argv[1]); gammas = [float(g) for g in sys.argv[2].split(',')]; s0s = [float(x) for x in sys.argv[3].split(',')]
Lend, cend, reason, path = run(K)
print('K=%.4f line ends L=%.5f cap %.4f (%s)' % (K, Lend, cend, reason), flush=True)
t0 = time.time()
for Lq in (1.99, Lend + 2e-4):
    i = min(range(1, len(path)), key=lambda j: abs(path[j][0] - Lq)); L, c, a = path[i]; L0, c0, _ = path[i-1]
    print(' L=%.5f cap=%.4f a=%.3e' % (L, c, a), flush=True)
    for g in gammas:
        for s0 in s0s:
            v, wh = worst(0.99999, L, c, a, 0.99999, L0, c0, K, g, s0)
            print('   gamma=%.3f S>=%.3f: worst %+.2e  (relative to u: %+.2f) at %s  [%.0fs]' % (g, s0, v, v/wh[-1] if wh else 0, wh, time.time()-t0), flush=True)
