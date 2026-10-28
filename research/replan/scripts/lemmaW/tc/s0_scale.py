# source-side lever: scale the whole density-step slope s0 by (1-eps) (ODE faces), exact return, role split C at best L, P at ~k=38 position
import json
from multiprocessing import Pool
import numpy as np
from fractions import Fraction as Fr
from scipy.integrate import solve_ivp
import pr86, best, ode_faces as OF
def make(eps):
    def rhs(L, y):
        B = y[0]; q = 0.999*L/(6*B - L)
        return [(1-eps)*(B - 10/(15 - 6*q))/(L - 1)]
    sol = solve_ivp(rhs, [2.5715, 2.0], [0.99999], rtol=1e-13, atol=1e-15, dense_output=True)
    return lambda L: float(sol.sol(L)[0])
def job(a):
    eps, Lc = a
    Bf = make(eps)
    fc = (OF.frac(Bf(Lc)), OF.frac(Lc)); fp = (OF.frac(Bf(2.38)), OF.frac(2.38))
    cfg = pr86.Cfg(windows='lemmaW', branches=['old','C','Ccap','C-7','P','Pcap'], BC=fc[0], LC=fc[1], BP=fp[0], LP=fp[1])
    r = best.theta_best(cfg, unit=10**9, anchor=873960000, lo=873800000, step=1000, maxstep=60)
    return a, None if r is None else r[0]/1e9
if __name__ == '__main__':
    jobs = [(e, L) for e in (0.0, 0.01, 0.03, 0.05, 0.07, 0.10) for L in (2.3383, 2.25, 2.20, 2.18)]
    with Pool(4) as p: res = dict(p.map(job, jobs))
    for e in (0.0, 0.01, 0.03, 0.05, 0.07, 0.10):
        print('s0 scaled by (1-%.2f): ' % e + '  '.join('C@L=%.4f: %s' % (L, '%.9f' % res[(e,L)] if res[(e,L)] else None) for L in (2.3383, 2.25, 2.20, 2.18)))
