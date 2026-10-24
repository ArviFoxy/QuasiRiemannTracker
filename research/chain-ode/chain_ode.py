"""Continuous model of the source chain's envelope (see README.md).
E' = -kamp q E/(1 - kamp q s),  q = smallest density passing the HIGH gate at the pivot:
1 - rho(q) + eps - q (E + (1 - g(s)) s) = 0,  rho(nu) = 1 - 10 nu/(15 - 6 nu)."""
import numpy as np
K = 4.4973108
S_ = [0.0135,0.014,0.018,0.022,0.026,0.030,0.03375,0.03575,0.03775,0.03975,0.04175,0.04375,0.04575,0.04775,0.04975]
G_ = [0.40,0.430,0.572,0.692,0.782,0.847,0.891,0.911,0.927,0.940,0.951,0.961,0.969,0.975,0.981]
gprof = lambda s: np.interp(s, S_, G_)
def qmin(X, eps=0.0):
    if eps == 0.0:
        return (15 - 10/X)/6
    lo, hi = 0.2, 0.83
    for _ in range(60):
        mid = (lo+hi)/2
        if mid*X - 10*mid/(15-6*mid) - eps <= 0: hi = mid
        else: lo = mid
    return hi
def run(gf, ds=2e-6, s_end=0.05, kamp=6.0, eps=0.0):
    s, E = 0.0, 1.0; out = []
    while s < s_end:
        X = E + (1-gf(s))*s
        q = qmin(X, eps)
        slope = min(kamp*q*E/(1-kamp*q*s), K)
        out.append((s, E, slope, q)); E -= slope*ds; s += ds
    return np.array(out)
def at(o, s): i = np.searchsorted(o[:,0], s); return o[i]
base = run(gprof)
cases = [('actual g profile', gprof, {}), ('g=1 everywhere', lambda s: 1.0, {}),
         ('g profile +0.05', lambda s: min(1.0, gprof(s)+0.05), {}),
         ('g profile, s<0.03 -> 1', lambda s: 1.0 if s < 0.03 else gprof(s), {}),
         ('exchange rate 6 -> 5.94', gprof, dict(kamp=5.94)),
         ('unmarked rho - 0.001', gprof, dict(eps=0.001)),
         ('unmarked rho - 0.0025', gprof, dict(eps=0.0025))]
for name, gf, kw in cases:
    o = run(gf, **kw)
    a, b = at(o, 0.0412), at(o, 0.045)
    print(f"{name:28s} E(0.0412)={a[1]:.6f} (d={a[1]-at(base,0.0412)[1]:+.2e}) L={a[2]:.4f} q={a[3]:.4f}  E(0.045)={b[1]:.6f} (d={b[1]-at(base,0.045)[1]:+.2e})")
if False:
  for name, gf in [('actual g profile', gprof), ('g=1 everywhere', lambda s: 1.0), ('g profile +0.05', lambda s: min(1.0, gprof(s)+0.05)),
                 ('g profile, s<0.03 -> 1', lambda s: 1.0 if s < 0.03 else gprof(s))]:
    o = run(gf)
    a, b = at(o, 0.0412), at(o, 0.045)
    print(f"{name:28s} E(0.0412)={a[1]:.6f} (d={a[1]-at(base,0.0412)[1]:+.2e}) L={a[2]:.4f} q={a[3]:.4f}  E(0.045)={b[1]:.6f} (d={b[1]-at(base,0.045)[1]:+.2e})")
