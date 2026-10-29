"""Step 4: the least theta the return could reach with an exact (pointwise, continuous) envelope.

theta*(r) solves  max_{delta, p} E_newTop(delta, p; theta) = theta - r,  where E uses the best admissible
count at each (delta, p).  By analyze2/analyze3 the max sits at p = 1/2 on the C branch, with every guard
slack, so E = Ebase + 3/4 dp N_C/J_C there.  h = floor ceiling of theta (exact, or rounded to 7 digits).
"""
import mpmath as mp
from fractions import Fraction as Fr
from model import P, count, row_exponent, hceiling, guard_vals

mp.mp.dps = 40


def maxE(theta, h):
    Pm = P(theta=theta, h=h)
    Pm.theta = mp.mpf(theta.numerator) / theta.denominator
    Pm.h = mp.mpf(h.numerator) / h.denominator
    for k in ('cB', 'cL', 'cCap', 'pB', 'pL', 'pCap', 'numCap', 'dm', 'reserve', 'mMinus', 'sMinus', 'K'):
        v = getattr(P(exact=True), k)
        setattr(Pm, k, mp.mpf(v.numerator) / v.denominator)
    Pm.eta = mp.mpf(1) / 10 ** 7
    Pm.finish()
    f = lambda d: row_exponent(Pm, 'newTop', d, mp.mpf(1) / 2, count(Pm, 'C', d, mp.mpf(1) / 2))
    # maximize via derivative root near 0.4488
    d0 = mp.findroot(lambda d: mp.diff(f, d), mp.mpf('0.4488'))
    return f(d0), d0, Pm


def theta_star(r, hmode):
    def F(th):
        thf = Fr(th).limit_denominator(10 ** 30) if not isinstance(th, Fr) else th
        h = hceiling(thf)
        if hmode == 'round7':
            h = Fr(int(h * 10 ** 7), 10 ** 7)
        e, d, _ = maxE(thf, h)
        return e - (mp.mpf(thf.numerator) / thf.denominator - r)
    lo, hi = Fr(87387, 100000), Fr(87388, 100000)
    for _ in range(60):
        mid = (lo + hi) / 2
        if F(mid) > 0:
            lo = mid
        else:
            hi = mid
    return hi


cur = Fr(43693617, 50000000)
e, d, Pm = maxE(cur, Fr(8044451, 10000000))
print('current: theta =', float(cur), ' max newTop exponent =', mp.nstr(e, 15), ' at delta =', mp.nstr(d, 12),
      ' theta - max =', mp.nstr(mp.mpf(cur.numerator) / cur.denominator - e, 6))
print('exact floor ceiling h(theta_cur) =', float(hceiling(cur)), '(current h = 0.8044451)')
for r in (mp.mpf('1e-8'), mp.mpf('1e-9'), mp.mpf(0)):
    for hmode in ('exact', 'round7'):
        ts = theta_star(r, hmode)
        print(f'reserve {mp.nstr(r, 3):6s} h={hmode:6s}: theta* = {float(ts):.12f}   gain vs current = {float(cur - ts):.3e}')
