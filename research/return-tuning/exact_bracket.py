"""Exact-rational bracket for the least theta this return structure can certify.

Upper end: the merged theta = 43693617/50000000 is certified (Lean).
Lower end: for theta_t below the estimated optimum, with the most favourable admissible h (the floor
ceiling of BoundsN.floor_margin, exact), the newTop row at one point (delta0, 1/2) exceeds theta_t - rowFee
for EVERY branch admissible at that point: old, and every proven chain face (131 faces) on both plain
pieces (uncapped / capped), plus weakC7.  Any window containing the point must be admissible there, and the
envelope is a min over windows containing the point and old, so no cover of the newTop edge exists.
Uses exact Fractions throughout (model.py with exact=True).
"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from fractions import Fraction as Fr
from model import P, count, guard_vals, row_exponent, hceiling
from chainfaces import chain_faces

ROWFEE = Fr(1, 10 ** 9)


def check(theta_t, delta0=Fr(4487894, 10 ** 7), p0=Fr(1, 2)):
    h = hceiling(theta_t)
    Pm = P(theta=theta_t, h=h, exact=True)
    target = Pm.theta - ROWFEE
    rows = []
    e = row_exponent(Pm, 'newTop', delta0, p0, count(Pm, 'old', delta0, p0))
    rows.append(('old', True, e))
    cands = [('weakC7', None)]
    for name, (B, L, cap) in chain_faces().items():
        for capped in (False, True):
            cands.append((f'{name}{"/cap" if capped else ""}', (B, L, min(cap, Fr(9999, 100000)) if not capped else cap, capped)))
    best_adm = None
    for nm, face in cands:
        if face is None:
            g, _ = guard_vals(Pm, 'weakC7', delta0, p0)
            c = count(Pm, 'weakC7', delta0, p0)
        else:
            g, _ = guard_vals(Pm, None, delta0, p0, face=face)
            c = count(Pm, None, delta0, p0, face=face)
        adm = all(v > 0 for v in g)
        ex = row_exponent(Pm, 'newTop', delta0, p0, c)
        rows.append((nm, adm, ex))
        if adm and (best_adm is None or ex < best_adm[2]):
            best_adm = (nm, adm, ex)
    return Pm, target, rows, best_adm


if __name__ == '__main__':
    for th in [Fr(43693617, 50000000), Fr(873872338, 10 ** 9), Fr(873872337, 10 ** 9)]:
        Pm, target, rows, best = check(th)
        lowest_any = min(rows, key=lambda r: r[2])
        print(f'theta_t = {th} = {float(th):.10f}, h = floor ceiling = {float(Pm.h):.12f}')
        print(f'   best admissible branch at (0.4487894, 1/2): {best[0]}  exponent - (theta_t - rowFee) = '
              f'{float(best[2] - target):+.4e}  (exact sign: {"+" if best[2] > target else "-/0"})')
        print(f'   lowest exponent over all candidates (admissible or not): {lowest_any[0]} '
              f'admissible={lowest_any[1]} {float(lowest_any[2] - target):+.4e}')


def lower_bound_all_faces(theta_t, delta0=Fr(4487894, 10 ** 7), p0=Fr(1, 2)):
    """min over all chain faces of the exponent of the *uncapped* three-line crossing (a lower bound for
    any window of the face or of any restriction of it, admissible or not: the window value must satisfy
    plainCurve(t - r) <= value with plainCurve = max of both pieces) and of the old count"""
    h = hceiling(theta_t)
    Pm = P(theta=theta_t, h=h, exact=True)
    target = Pm.theta - ROWFEE
    vals = [('old', row_exponent(Pm, 'newTop', delta0, p0, count(Pm, 'old', delta0, p0)))]
    for name, (B, L, cap) in chain_faces().items():
        vals.append((name, row_exponent(Pm, 'newTop', delta0, p0, count(Pm, None, delta0, p0, face=(B, L, cap, False)))))
    best = min(vals, key=lambda v: v[1])
    return best, target


if __name__ == '__main__':
    for th in [Fr(436936169, 500000000), Fr(873872337, 10 ** 9)]:
        (nm, ex), target = lower_bound_all_faces(th)
        print(f'theta_t = {float(th):.10f}: min over all faces (uncapped crossing, any admissibility) and old: {nm}, '
              f'exponent - (theta_t - rowFee) = {float(ex - target):+.4e} (exact sign {"+" if ex > target else "-/0"})')
