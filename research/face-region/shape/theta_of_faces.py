"""theta*(count face, physical face): the least theta the current return certifies when its two faces are
replaced.  Same model and binding point as research/return-tuning/theta_star.py (newTop edge, p = 1/2,
branch C, max over delta), with the faces as arguments.  h = exact floor ceiling of theta; reserve 1e-8.

Usage:  python3 theta_of_faces.py            (table of the cases used in README.md)
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', 'return-tuning'))
import mpmath as mp
from fractions import Fraction as Fr
from model import P, count, row_exponent, hceiling, guard_vals, GUARD_NAMES

mp.mp.dps = 40
MPF = lambda v: mp.mpf(v.numerator) / v.denominator if isinstance(v, Fr) else mp.mpf(v)


def model(theta, h, cB, cL, cCap, pB, pL):
    Pm = P(theta=theta, h=h)
    for k, v in (('cB', cB), ('cL', cL), ('cCap', cCap), ('pB', pB), ('pL', pL)):
        setattr(Pm, k, MPF(v))
    for k in ('pCap', 'numCap', 'dm', 'reserve', 'mMinus', 'sMinus', 'K'):
        v = getattr(P(exact=True), k)
        setattr(Pm, k, MPF(v))
    Pm.theta = MPF(theta); Pm.h = MPF(h); Pm.eta = mp.mpf(1) / 10 ** 7
    return Pm.finish()


def maxE(Pm):
    f = lambda d: row_exponent(Pm, 'newTop', d, mp.mpf(1) / 2, count(Pm, 'C', d, mp.mpf(1) / 2))
    d0 = mp.findroot(lambda d: mp.diff(f, d), mp.mpf('0.4488'))
    return f(d0), d0


def theta_star(cB, cL, cCap=Fr(9999, 100000), pB=Fr(49283557, 50000000), pL=Fr(4503, 2000), r=mp.mpf('1e-8')):
    def F(th):
        Pm = model(th, hceiling(th), cB, cL, cCap, pB, pL)
        e, _ = maxE(Pm)
        return e - (MPF(th) - r)
    lo, hi = Fr(8737, 10000), Fr(8740, 10000)
    for _ in range(64):
        mid = (lo + hi) / 2
        if F(mid) > 0:
            lo = mid
        else:
            hi = mid
    Pm = model(hi, hceiling(hi), cB, cL, cCap, pB, pL)
    e, d0 = maxE(Pm)
    g, _ = guard_vals(Pm, 'C', d0, mp.mpf(1) / 2)
    worst = min(range(len(g)), key=lambda i: g[i] / (abs(g[3]) if i > 3 else 1))
    cap = Pm.new_capacity(Pm.dp)
    return hi, d0, GUARD_NAMES[worst], cap


if __name__ == '__main__':
    cases = [
        ('chain end (merged count face)', Fr(96232839, 100000000), Fr(3853, 2000)),
        ('ODE floor face (CONTINUUM.md sec. 0)', Fr(96239387, 100000000), Fr(192607179, 100000000)),
        ('chain end, B + 1e-5', Fr(96232839, 100000000) + Fr(1, 10 ** 5), Fr(3853, 2000)),
        ('chain end, Lam - 1e-4', Fr(96232839, 100000000), Fr(3853, 2000) - Fr(1, 10 ** 4)),
    ]
    base = None
    for name, B, L in cases:
        t, d0, gw, cap = theta_star(B, L)
        base = t if base is None else base
        print('%-38s B=%.8f Lam=%.8f  theta*=%.10f  (%+.2e vs first)  delta*=%.5f  tightest guard: %s' % (
            name, float(B), float(L), float(t), float(t - base), float(d0), gw))
    for name, pB in (('physical face 64 (merged)', Fr(49283557, 50000000)), ('physical B + 1e-5', Fr(49283557, 50000000) + Fr(1, 10 ** 5))):
        t, d0, gw, cap = theta_star(cases[0][1], cases[0][2], pB=pB)
        print('%-38s capacity(dp)=%.8f  theta*=%.10f  (%+.2e vs merged)' % (name, float(cap), float(t), float(t - base)))
