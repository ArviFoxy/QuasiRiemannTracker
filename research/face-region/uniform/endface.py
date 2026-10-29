import numpy as np
from scipy.integrate import solve_ivp
from conditions import cond, cond_V10, cond_1d
def q_of(B, L): return min(0.999*L/(6*B - L), 0.75)
def kappa(q): return 4*(5 - 3*q)/(25 - 18*q)
for eta in (1e-4, 5e-5):
    f = lambda L, y: [(y[0] - (kappa(q_of(y[0], L)) - eta))/(L - (kappa(q_of(y[0], L)) - eta))]
    sol = solve_ivp(f, [2.5715, 1.90], [0.99999], method='DOP853', rtol=1e-12, atol=1e-14, dense_output=True)
    h = 0.0005
    for L0 in (1.9275, 1.927, 1.9265 + h):
        B0 = float(sol.sol(L0)[0]); s0 = (B0 - float(sol.sol(L0 - h)[0]))/h
        best = None
        for A in (0.30, 0.35, 0.42, 0.49):
            for D in (10, 20, 40, 70, 100, 200):
                o = cond(B0, L0, h, s0, A, D); o.pop('beta'); o.pop('m0')
                o['V10'] = cond_V10(B0, L0, h, s0, A, D); o.update(cond_1d(B0, L0, h, s0, A, D))
                m = min(o.values()); arg = min(o, key=o.get)
                if best is None or m > best[0]: best = (m, A, D, arg)
        print('eta=%g parent Lam=%.4f q=%.5f -> child Lam=%.4f B=%.8f : best min margin %+.2e (A=%.2f D=%d, binding %s)' % (
            eta, L0, q_of(B0, L0), L0 - h, float(sol.sol(L0 - h)[0]), *best))
    print('   target: dominate old final face (1.9265, 0.96232839)')
