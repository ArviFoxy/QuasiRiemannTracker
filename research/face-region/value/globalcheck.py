"""Is p = 1/2 on newTop still the binding point when the count face is much better?  theta* over the whole
return: max over the four edges, delta in [0, 3/4], p in [0, 1/2] of Ebase + 3/4 d envelope(delta, p), the
envelope being the least count among the branches whose 15 guards hold there (old count always available).
Float model (research/return-tuning/model.py); grid 0.01 in delta, 1/20 in p."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', 'return-tuning'))
import numpy as np
from fractions import Fraction as Fr
from model import P, count, row_exponent, guard_vals, hceiling


def env(Pm, faces, d, p):
    best, who = count(Pm, 'old', d, p), 'old'
    for name, face in faces:
        c = count(Pm, None, d, p, face=face)
        if c < best:
            g, _ = guard_vals(Pm, None, d, p, face=face)
            if all(v > 0 for v in g):
                best, who = c, name
    return best, who


def global_max(theta, cface, pface):
    Pm = P(theta=float(theta), h=float(hceiling(Fr(theta))), cB=cface[0], cL=cface[1], cCap=cface[2], pB=pface[0], pL=pface[1])
    # the hypothetical region contains the merged faces and every weakening B' <= B of the new count face
    faces = [('mC', (0.96232839, 1.9265, 0.09999, False)), ('mcapC', (0.96232839, 1.9265, 0.09999, True)),
             ('mweakC7', (0.96232839 - 7 / 4000, 1.9265, 0.09999, False)),
             ('capP', (Pm.pB, Pm.pL, Pm.pCap, True))]
    for k in range(0, 41):
        Bk = Pm.cB - k * 0.002
        if Bk < 0.9580:
            break
        faces.append(('C-%d' % k, (Bk, Pm.cL, Pm.cCap, False)))
    faces.append(('capC', (Pm.cB, Pm.cL, Pm.cCap, True)))
    best = (-1, None)
    for e in ('oldSmall', 'oldSwitch', 'newSwitch', 'newTop'):
        for d in np.linspace(0.0, 0.75, 76):
            for p in np.linspace(0.0, 0.5, 11):
                c, who = env(Pm, faces, d, p)
                v = row_exponent(Pm, e, d, p, c)
                if v > best[0]:
                    best = (v, (e, d, p, who))
    return best, Pm


def theta_global(cface, pface, r=1e-8):
    """start from the binding-point optimum (common.best_theta) and move up until the whole grid passes"""
    from common import best_theta
    b = best_theta(cface[0], cface[1], cface[2], pface[0], pface[1])
    lo = float(b[0]) - 2e-8 if b else 0.8735
    (v, where), _ = global_max(lo, cface, pface)
    if v <= lo - r:
        return lo, where
    hi = lo + 2e-5
    while True:
        (v, where), _ = global_max(hi, cface, pface)
        if v <= hi - r:
            break
        lo, hi = hi, hi + 2e-5
    for _ in range(12):
        mid = (lo + hi) / 2
        (v, where_m), _ = global_max(mid, cface, pface)
        if v > mid - r:
            lo = mid
        else:
            hi, where = mid, where_m
    return hi, where


if __name__ == '__main__':
    PF = (49283557 / 50000000, 4503 / 2000)
    cases = [('merged count face', (0.96232839, 1.9265, 0.09999), PF),
             ('count face B + 0.01, cap 0.11', (0.97232839, 1.9265, 0.11), PF),
             ('count face B = 1, cap 0.12', (1.0, 1.9265, 0.12), PF),
             ('lever (b) Lb = 2.3 face', (0.976472, 1.99533, 0.09999), PF)]
    for name, cf, pf in cases:
        t, where = theta_global(cf, pf)
        print('%-32s global theta* = %.8f  binding: edge=%s delta=%.3f p=%.3f branch=%s' % ((name, t) + where))
