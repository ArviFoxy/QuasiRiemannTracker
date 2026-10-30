"""theta* when the floor-margin constant 1/200 is replaced by m' (h ceiling rises by 3(1/200 - m')), capped by the box h < hmax."""
import numpy as np
from fractions import Fraction as Fr
from fast import old_count
from model import hceiling
from ideal import face_count
d = np.round(np.arange(0.38, 0.52, 0.0005), 6)
p = np.round(np.array([0.46, 0.48, 0.49, 0.495, 0.499, 0.5]), 6)
DD, PP = np.meshgrid(d, p, indexing='ij')
def theta_star(env, pL, dmargin=0.0, hmax=0.806, numCap=0.075, pB=0.99999, reserve=1e-8):
    lo, hi = 0.86, 0.885
    for _ in range(46):
        th = (lo + hi) / 2
        h = min(float(hceiling(Fr(th).limit_denominator(10 ** 12))) + 3 * dmargin, hmax - 1e-7)
        c = 1 - th; ell = 4 * c - 1 / 3; y = h - 2 * ell; kappa = 1 - 2 * c; dd = h + 1e-10
        C = min(numCap * dd, (2 * y - (2 - pB) * dd) / pL)
        e = np.minimum(env, old_count(DD, PP, kappa))
        E = 0.5 + 13 * h / 75 - y / 2 - ell / 2 - 0.09 * dd + DD / 2 + DD * PP * (ell - C / 2) + 0.75 * dd * e
        if E.max() > th - reserve: lo = th
        else: hi = th
    return hi, h
capf = lambda L: 0.1 + 0.06 * (5143 / 2000 - L)
for Lend in (2.02, 2.005):
    ok, v = face_count(DD, PP, 0.99999, Lend, capf(Lend))
    env = np.where(ok, v, np.inf)
    t0, h0 = theta_star(env, Lend)
    print('Lend %.3f base theta* %.8f h %.6f' % (Lend, t0, h0))
    for mprime in (1/400, 1/1000, 1/10000):
        for hmax in (0.806, 0.82):
            t, h = theta_star(env, Lend, dmargin=1/200 - mprime, hmax=hmax)
            print('   margin %.5f hmax %.3f: h %.6f theta* %.8f (d %.2e)' % (mprime, hmax, h, t, t - t0))
