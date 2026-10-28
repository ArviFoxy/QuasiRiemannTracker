"""floor-coupled theta*: least theta (units of 1e-7) such that the Lean return (pr86.certifiable) passes at
h = the largest h on a 1e-6 grid allowed by BoundsN.floor_margin (and h < hu).  Used for all scans."""
import math
from fractions import Fraction as Fr
import pr86

HGRID = 10**6


def floor_margin_h(th, h):
    ell = Fr(11, 3) - 4 * th
    x = 1 + ell - h; y = h - 2 * ell; dP = h + Fr(1, 10**10)
    signal = x / 2 + (y - x) / 12
    return signal - Fr(1, 200) - (Fr(4, 25) * x - Fr(3, 20) - Fr(51, 100) * y + Fr(67, 100) * dP - Fr(3, 20) * ell)


def hmax_floor(th):
    """largest h with floor_margin >= 0 (linear in h)"""
    f0 = floor_margin_h(th, Fr(0)); f1 = floor_margin_h(th, Fr(1))
    slope = f1 - f0
    return -f0 / slope   # slope<0 -> root


def h_for(th, hu, extra=Fr(0)):
    hm = min(hmax_floor(th) - extra, hu - Fr(1, 10**6))
    return Fr(math.floor(hm * HGRID), HGRID)


def passes(cfg, th_units, hfix=None, unit=10**7, cache=None):
    th = Fr(th_units, unit)
    hu = cfg.bounds[1]
    h = hfix if hfix is not None else h_for(th, hu)
    return pr86.certifiable(cfg.copy(th=th, h=h))


def theta_best(cfg, anchor=8739600, lo=8700000, step=20, maxstep=40, unit=10**7, hfix=None):
    """-> (theta in 1/unit, h) or None; bisection assuming monotonicity in theta."""
    hi = anchor
    n = 0
    while not passes(cfg, hi, hfix, unit):
        n += 1
        if n > maxstep:
            return None
        lo, hi = hi, hi + step
    k = 0
    while passes(cfg, lo, hfix, unit):
        hi = lo; lo -= 2000; k += 1
        if k > 30:
            return None
    while hi - lo > 1:
        mid = (lo + hi) // 2
        if passes(cfg, mid, hfix, unit):
            hi = mid
        else:
            lo = mid
    th = Fr(hi, unit)
    h = hfix if hfix is not None else h_for(th, cfg.bounds[1])
    return hi, h


def why(cfg, th_units, unit=10**7, hfix=None):
    th = Fr(th_units, unit)
    h = hfix if hfix is not None else h_for(th, cfg.bounds[1])
    return pr86.certifiable(cfg.copy(th=th, h=h), why=True)[1]
