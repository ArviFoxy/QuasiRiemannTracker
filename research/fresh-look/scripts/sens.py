"""Sensitivities of theta* at the relaxed optimum (full E5 face at Lambda_end, both pieces, relaxed guards)."""
import numpy as np
from fractions import Fraction as Fr
from fast import branch, old_count
from model import hceiling
from ideal import face_count
d = np.round(np.arange(0.38, 0.52, 0.0005), 6)
p = np.round(np.array([0.46, 0.48, 0.49, 0.495, 0.499, 0.5]), 6)
DD, PP = np.meshgrid(d, p, indexing='ij')

def theta_star(env, numCap=0.075, pB=0.99999, pL=2.02, dh=0.0, long_slope=5/6, reserve=1e-8):
    lo, hi = 0.86, 0.885
    for _ in range(46):
        th = (lo + hi) / 2
        h = float(hceiling(Fr(th).limit_denominator(10 ** 12))) + dh
        c = 1 - th; ell = 4 * c - 1 / 3; y = h - 2 * ell; kappa = 1 - 2 * c; dd = h + 1e-10
        C = min(numCap * dd, (2 * y - (2 - pB) * dd) / pL)
        e = np.minimum(env, old_count(DD, PP, kappa))
        E = 0.5 + 13 * h / 75 - y / 2 - ell / 2 - 0.09 * dd + DD / 2 + DD * PP * (ell - C / 2) + 0.75 * dd * e
        if E.max() > th - reserve: lo = th
        else: hi = th
    return hi

capf = lambda L: 0.1 + 0.06 * (5143 / 2000 - L)
for Lend in (2.02, 2.005):
    ok, v = face_count(DD, PP, 0.99999, Lend, capf(Lend))
    env = np.where(ok, v, np.inf)
    t0 = theta_star(env, pL=Lend)
    print('Lend %.3f: theta* = %.8f' % (Lend, t0))
    for dh in (1e-4, 1e-3, 3e-3):
        print('   h + %.0e: dtheta = %.2e' % (dh, theta_star(env, pL=Lend, dh=dh) - t0))
    for nc in (0.06, 0.07, 0.09):
        print('   numCap %.3f: dtheta = %.2e' % (nc, theta_star(env, pL=Lend, numCap=nc) - t0))
    for dc in (-0.001, -0.005):
        e2 = env + dc
        print('   count - %.3f uniformly: dtheta = %.2e' % (-dc, theta_star(e2, pL=Lend) - t0))
    ok2, v2 = face_count(DD, PP, 1.0, Lend, capf(Lend))
    print('   B = 1: dtheta = %.2e' % (theta_star(np.where(ok2, v2, np.inf), pL=Lend, pB=1.0) - t0))
