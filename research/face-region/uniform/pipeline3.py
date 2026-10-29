import sys
import numpy as np
from scipy.integrate import solve_ivp
from conditions import cond, cond_V10, cond_1d
def q_of(B, L): return min(0.999*L/(6*B - L), 0.75)
def kappa(q): return 4*(5 - 3*q)/(25 - 18*q)
eta = float(sys.argv[1]); h = float(sys.argv[2]); A = float(sys.argv[3]); D = float(sys.argv[4]); Lstop = float(sys.argv[5])
f = lambda L, y: [(y[0] - (kappa(q_of(y[0], L)) - eta))/(L - (kappa(q_of(y[0], L)) - eta))]
sol = solve_ivp(f, [2.5715, 1.90], [0.99999], method='DOP853', rtol=1e-12, atol=1e-14, dense_output=True)
n = int(round((2.5715 - Lstop)/h))
worst = {}; fails = []; m0neg = 0
for k in range(n):
    L0 = 2.5715 - k*h; B0 = float(sol.sol(L0)[0]); s0 = (B0 - float(sol.sol(L0 - h)[0]))/h
    o = cond(B0, L0, h, s0, A, D); m0neg += o['m0'] < 0; o.pop('beta'); o.pop('m0')
    o['V10'] = cond_V10(B0, L0, h, s0, A, D); o.update(cond_1d(B0, L0, h, s0, A, D))
    for kk, v in o.items():
        worst[kk] = min(worst.get(kk, np.inf), v)
    if min(o.values()) <= 0: fails.append((round(L0, 5), min(o, key=o.get)))
print('eta=%g h=%g A=%g D=%g: %d steps to Lam=%.4f, %d fail, m0<0 at %d steps' % (eta, h, A, D, n, 2.5715 - n*h, len(fails), m0neg))
print('fails (first 5):', fails[:5])
print('worst:', ' '.join('%s=%+.2e' % (kk, v) for kk, v in worst.items()))
print('end face: Lam=%.4f B=%.8f' % (2.5715 - n*h, float(sol.sol(2.5715 - n*h)[0])))
