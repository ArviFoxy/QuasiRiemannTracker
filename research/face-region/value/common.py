"""Shared helpers: theta* of the merged return (research/return-tuning/model.py) for a count face and a
physical face, on the uncapped branch C or the capped branch capC, with the 15 admission guards checked at the
binding point (newTop edge, p = 1/2, max over delta).  Reserve 1e-8, h = exact floor ceiling of theta."""
import sys, os
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', '..', 'return-tuning'))
import mpmath as mp
from fractions import Fraction as Fr
from model import P, count, row_exponent, hceiling, guard_vals, GUARD_NAMES, witness

mp.mp.dps = 30
HALF = mp.mpf(1) / 2
MERGED = Fr(43693617, 50000000)
PB0, PL0 = Fr(49283557, 50000000), Fr(4503, 2000)
CB0, CL0, CC0 = Fr(96232839, 100000000), Fr(3853, 2000), Fr(9999, 100000)
MPF = lambda v: mp.mpf(v.numerator) / v.denominator if isinstance(v, Fr) else mp.mpf(v)


def model(theta, cB, cL, cCap, pB, pL):
    Pm = P(theta=theta, h=hceiling(theta))
    for k, v in (('cB', cB), ('cL', cL), ('cCap', cCap), ('pB', pB), ('pL', pL)):
        setattr(Pm, k, MPF(v))
    for k in ('pCap', 'numCap', 'dm', 'reserve', 'mMinus', 'sMinus', 'K'):
        setattr(Pm, k, MPF(getattr(P(exact=True), k)))
    Pm.theta = MPF(theta); Pm.h = MPF(hceiling(theta)); Pm.eta = mp.mpf(1) / 10 ** 7
    return Pm.finish()


def maxE(Pm, cand):
    f = lambda d: row_exponent(Pm, 'newTop', d, HALF, count(Pm, cand, d, HALF))
    d0 = mp.findroot(lambda d: mp.diff(f, d), mp.mpf('0.44'))
    return f(d0), d0


def theta_star(cand, cB, cL, cCap=CC0, pB=PB0, pL=PL0, r=mp.mpf('1e-8'), lo=Fr(8700, 10000), hi=Fr(8740, 10000)):
    """least theta on branch cand; returns (theta*, delta*, failing guards, witness (t, r, m), slot at witness)"""
    cB, cL, cCap, pB, pL = (Fr(v).limit_denominator(10 ** 14) if not isinstance(v, Fr) else v for v in (cB, cL, cCap, pB, pL))

    def F(th):
        e, _ = maxE(model(th, cB, cL, cCap, pB, pL), cand)
        return e - (MPF(th) - r)
    for _ in range(56):
        mid = (lo + hi) / 2
        if F(mid) > 0:
            lo = mid
        else:
            hi = mid
    Pm = model(hi, cB, cL, cCap, pB, pL)
    e, d0 = maxE(Pm, cand)
    g, br = guard_vals(Pm, cand, d0, HALF)
    bad = [GUARD_NAMES[i] for i in range(len(g)) if g[i] <= 0]
    t, rr, m = witness(Pm, cand, d0, HALF)
    z = (br['B'] - 2 * m) / br['L'] if cand == 'C' else br['Zc']
    return hi, d0, bad, (t, rr, m), z


def best_theta(cB, cL, cCap=CC0, pB=PB0, pL=PL0):
    """best valid branch (C or capC) for the count face; returns (theta*, branch, witness m, slot z)"""
    out = []
    for cand in ('C', 'capC'):
        t, d0, bad, (tt, rr, m), z = theta_star(cand, cB, cL, cCap, pB, pL)
        if not bad:
            out.append((t, cand, m, z))
    return min(out) if out else None
