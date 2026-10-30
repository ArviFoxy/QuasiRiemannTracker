"""High-precision theta* at the binding point (newTop, p = 1/2, branch C = uncapped full E5 face), h = 7-digit
floor of the exact floor-margin ceiling, reserve 1e-8; guard margins at the optimum (relaxed set)."""
import mpmath as mp
from fractions import Fraction as Fr
from model import hceiling
mp.mp.dps = 40
def run(B, L, cap, pB, pL, numCap=Fr(3, 40), reserve=mp.mpf('1e-8'), floor7=True):
    B, L, cap, pB, pL = (mp.mpf(Fr(v).numerator) / Fr(v).denominator for v in (B, L, cap, pB, pL))
    nc = mp.mpf(numCap.numerator) / numCap.denominator
    half = mp.mpf(1) / 2
    def parts(theta, d, p=half):
        hc = hceiling(Fr(mp.nstr(theta, 30)).limit_denominator(10 ** 15))
        h = Fr(int(hc * 10 ** 7), 10 ** 7) if floor7 else hc
        h = mp.mpf(h.numerator) / h.denominator
        c = 1 - theta; ell = 4 * c - mp.mpf(1) / 3; y = h - 2 * ell; dd = h + mp.mpf('1e-10')
        C = min(nc * dd, (2 * y - (2 - pB) * dd) / pL)
        V = mp.mpf(5) / 6 - d
        D = 3 - p - 4 * p / L; A = 2 - 4 * p / L; C0 = 1 - 2 * B * p / L
        U = (1 - p) * C0; J = V * D + d * (1 - p) * A; N = (1 - d) * J + V * d * U
        cnt = N / J
        E = mp.mpf(1) / 2 + 13 * h / 75 - y / 2 - ell / 2 - mp.mpf('0.09') * dd + d / 2 + d * p * (ell - C / 2) + mp.mpf(3) / 4 * dd * cnt
        return E, cnt, h, C
    def maxE(theta):
        f = lambda d: parts(theta, d)[0]
        d0 = mp.findroot(lambda d: mp.diff(f, d), mp.mpf('0.452'))
        return f(d0), d0
    lo, hi = mp.mpf('0.8730'), mp.mpf('0.8740')
    for _ in range(70):
        mid = (lo + hi) / 2
        e, _ = maxE(mid)
        if e > mid - reserve: lo = mid
        else: hi = mid
    e, d0 = maxE(hi)
    E, cnt, h, C = parts(hi, d0)
    return hi, d0, cnt, h, C
for label, args in [('E5 end 2.02 (count = physical face)', (Fr(99999, 100000), Fr(101, 50), Fr(13309, 100000), Fr(99999, 100000), Fr(101, 50))),
                    ('E5 line to 2.005', (Fr(99999, 100000), Fr(401, 200), Fr(1, 10) + Fr(3, 50) * (Fr(5143, 2000) - Fr(401, 200)), Fr(99999, 100000), Fr(401, 200))),
                    ('E5 line to 2.0001', (Fr(99999, 100000), Fr(20001, 10000), Fr(1, 10) + Fr(3, 50) * (Fr(5143, 2000) - Fr(20001, 10000)), Fr(99999, 100000), Fr(20001, 10000)))]:
    th, d0, cnt, h, C = run(*args)
    N = int(mp.ceil((1 - th) * 0 + (1 - th) * 50000000 - 1e-9))  # c = N / 5e7 must be <= 1 - theta*
    N = int(mp.floor((1 - th) * 50000000))
    print('%-38s theta* = %s  delta* = %.6f  count = %.6f  h = %.7f  C = %.6f  8-digit grid: theta = 1 - %d/5e7 = %.8f' % (
        label, mp.nstr(th, 12), float(d0), float(cnt), float(h), float(C), N, 1 - N / 5e7))
