# As kw12, but per root take the better of the selected norm with excess (x-5/6-Delta)_+ and the proven full sextic
# sieve Theta_6 = max(y, xe, 5y/6+xe/3, y/3+5xe/6) (OptimalBound exponents; replaces the withdrawn 5y/6+5xe/18).
import sys, numpy as np
from kwlib import run_from_base, BASE, R
def e_sel_geo5(x1, x2, s, M, delta, Delta, nrho=241):
    rho = np.linspace(0.0, M/6, nrho); y = M - 6*rho
    ok = (y >= x1) & (y >= x2) & (y > 0)
    xe = np.minimum(x1, y - x1) + np.minimum(x2, y - x2) + s
    x = np.where(y > 0, xe/np.maximum(y, 1e-12), 0)
    g = np.maximum(0.0, x - 5/6 - Delta)
    sel = np.maximum(xe, (1 - delta + g)*y + delta*xe)
    full = np.maximum.reduce([y, xe, 5*y/6 + xe/3, y/3 + 5*xe/6])
    per = np.minimum(sel, full)
    return np.where(ok, rho + per, -1e9).max()
def worst_geo5(B, L, c, a, L0, c0, delta, Delta, s0, nS=41, nt=7, base=BASE):
    wv, where = -1e9, None
    for S in np.linspace(0.0, c, nS)[1:]:
        if S < s0: continue
        w = S; u = a*w; PCmax = B - L*S
        for PC in np.linspace(0.5*PCmax, PCmax, 5):
            for s in (w - u, 0.9*(w-u), 0.75*(w - u), 0.5*(w - u), 0.25*(w-u)):
                for t in np.linspace(0.0, 1 + 6*u, nt):
                    M = 1 + t - 6*u
                    pr = R.deletion_need(B, L0, c0, PC, s, M)
                    par = pr if (s - pr) >= s0 else R.deletion_need(base[0], base[1], base[2], PC, s, M)
                    for frac in (0.5, 0.4, 0.3, 0.0):
                        x1, x2 = PC*(1 - frac), PC*frac
                        sel = e_sel_geo5(x1, x2, s, M, delta, Delta) - M
                        v = min(sel, par) - u
                        if v > wv: wv, where = v, (round(S,4), round(s,4), round(M,4), round(x1,3), round(x2,3))
    return wv, where
K = float(sys.argv[1]); s0 = float(sys.argv[2]); Lstop = float(sys.argv[3])
Lend, cend, reason, path = run_from_base(K)
pth = [q for q in path if q[0] >= Lstop - 1e-9]
idx = sorted(set([1] + [int(len(pth)*f) for f in (0.2, 0.4, 0.6, 0.8)] + [len(pth)-1]))
def passes(D):
    for i in idx:
        L, c, a = pth[i]; L0, c0, _ = pth[i-1]
        v, wh = worst_geo5(0.99999, L, c, a, L0, c0, K, D, s0)
        if v > 0: return False, (round(L, 4), wh)
    return True, None
ok, info = passes(0.0)
lo, hi = 0.0, 0.2
if not ok:
    for _ in range(9):
        mid = (lo+hi)/2; ok2, inf2 = passes(mid)
        if ok2: hi = mid
        else: lo = mid; info = inf2
else: hi = 0.0
print('K=%.2f s0=%.3f stop L=%.4f [sel (x-5/6)_+ or Theta6]: needed extra saving Delta ~ %.4f ; last failure %s' % (K, s0, pth[-1][0], hi, info), flush=True)
