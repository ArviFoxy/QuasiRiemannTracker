"""Generator lemma check: for EVERY face (B0, Lam0) in a band around the eta-curve (not only on it), every slope
s0 in [sigma(B0,Lam0) + mu, sigma + mu + ds] and every step h in (0, h0], one density step with the fixed selection
(A, D) passes all scalar conditions.  Random sampling of the band; report the worst margins and failures."""
import sys
import numpy as np
from scipy.integrate import solve_ivp
from conditions import cond, cond_V10, cond_1d
def q_of(B, L): return 0.999*L/(6*B - L)
def kappa(q): return 4*(5 - 3*q)/(25 - 18*q)
def sigma(B, L):
    k = kappa(min(q_of(B, L), 0.75)); return (B - k)/(L - k)
mu = float(sys.argv[1]); h0 = float(sys.argv[2]); A = float(sys.argv[3]); D = float(sys.argv[4])
band = float(sys.argv[5]); qlo = float(sys.argv[6]); n = int(sys.argv[7])
f = lambda L, y: [(y[0] - (kappa(min(q_of(y[0], L), 0.75)) - 1e-4))/(L - (kappa(min(q_of(y[0], L), 0.75)) - 1e-4))]
sol = solve_ivp(f, [2.5715, 1.90], [0.99999], method='DOP853', rtol=1e-12, atol=1e-14, dense_output=True)
rng = np.random.default_rng(5)
worst = {}; fails = []
for it in range(n):
    L0 = rng.uniform(1.926, 2.5715)
    B0 = float(sol.sol(L0)[0]) + rng.uniform(-band, band)
    q = q_of(B0, L0)
    if q < qlo or q > 0.7495: continue
    s0 = sigma(B0, L0) + mu + rng.uniform(0, 2e-4)
    h = h0*rng.uniform(0.02, 1.0)**0.5
    o = cond(B0, L0, h, s0, A, D); o.pop('beta'); o.pop('m0')
    o['V10'] = cond_V10(B0, L0, h, s0, A, D); o.update(cond_1d(B0, L0, h, s0, A, D))
    for k, v in o.items(): worst[k] = min(worst.get(k, np.inf), v)
    if min(o.values()) <= 0: fails.append((round(L0, 4), round(B0, 6), round(q, 4), round(h, 6), min(o, key=o.get), min(o.values())))
print('mu=%g h0=%g A=%g D=%g band=%g qlo=%g: %d samples, %d fail' % (mu, h0, A, D, band, qlo, n, len(fails)))
print(' worst:', ' '.join('%s=%+.1e' % (k, v) for k, v in worst.items()))
for x in fails[:6]: print('  fail', x)
