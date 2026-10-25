"""Family v2: per-piece scaled variable y = (s - sig_j)/H_j in [0, 1], dyadic step Delta_j = H_j/2^m,
dyadic LOW denominator, Et_j(y) cubic with coefficients rounded to 10^-RD. Same node definition as
family.py (secant lines, q from the parent with exact LOW denominator).

All polynomials are in y. s = sig_j + H_j y.
"""
import os, sys
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'repeated-marks'))
from fractions import Fraction as Fr
import numpy as np
import closed_flow as CF
import polyq as P

from chain_params import K, START   # natural cost and the chain's first parent (one source)
CAPMAX = Fr(549989, 10000000)
FEES = (Fr(1, 10**17), Fr(1, 10**12), Fr(1, 10**10))


class Family2:
    def __init__(self, sig, H, m, den, Ey):
        self.sig, self.H, self.m, self.den, self.Ey = sig, H, m, den, Ey
        self.Dy = Fr(1, 2**m)                       # step in y
        self.D = [h*self.Dy for h in H]             # step in s per piece

    def polys(self, j):
        """B, L, B0, L0, s as polynomials in y on piece j (child and parent both in piece j)."""
        Ey = self.Ey[j]; H = self.H[j]; Dy = self.Dy
        EyD = P.shift(Ey, Dy)
        L = P.smul(1/(H*Dy), P.sub(Ey, EyD))        # (Et(s) - Et(s + Delta))/Delta
        sv = [self.sig[j], H]
        B = P.add(Ey, P.mul(sv, L))
        return B, L, P.shift(B, -Dy), P.shift(L, -Dy), sv


def build2(sig_f, m=16, den=Fr(1, 2**15), phi=1e-4, RD=14, n=40000):
    s0 = sig_f[0]
    E0 = float(START['B']) - float(START['L'])*s0
    ss, Es = CF.flow(s0, E0, sig_f[-1], n, den=float(den), fudge=phi)
    sl = lambda s, E: -CF.slope(s, E, float(den), phi)
    sig = [Fr(x).limit_denominator(10**7) for x in sig_f]
    vals, ders = [], []
    for x in sig:
        i = int(np.argmin(abs(ss - float(x))))
        s, E = ss[i], Es[i]; h = (float(x) - s)/8
        for _ in range(8):
            k1 = sl(s, E); k2 = sl(s + h/2, E + h*k1/2); k3 = sl(s + h/2, E + h*k2/2); k4 = sl(s + h, E + h*k3)
            E += h*(k1 + 2*k2 + 2*k3 + k4)/6; s += h
        vals.append(E); ders.append(sl(float(x), E))
    vals[0] = float(START['B']) - float(START['L'])*float(sig[0])
    H = [sig[j + 1] - sig[j] for j in range(len(sig) - 1)]
    Ey = []
    for j in range(len(H)):
        h = float(H[j])
        Ea, Eb, da, db = vals[j], vals[j + 1], ders[j]*h, ders[j + 1]*h   # slopes in y
        c = [Ea, da, 3*(Eb - Ea) - 2*da - db, da + db - 2*(Eb - Ea)]
        Ey.append([Fr(round(ck*10**RD), 10**RD) for ck in c])
    if True:   # start exactly on the start face (the chain's first parent)
        Ey[0][0] = START['B'] - START['L']*sig[0]
    return Family2(sig, H, m, den, Ey), (ss, Es)


def face_C(fam):
    """The final count face: the last grid face of the last piece, as (piece, grid index)."""
    return len(fam.H) - 1, 2**fam.m - 1


def face_P(fam):
    """The final physical face: the last grid face with slope above 3, as (piece, grid index). The
    slope decreases along the family, so it lies in the last piece that starts above 3."""
    for j in reversed(range(len(fam.H))):
        L = fam.polys(j)[1]
        if P.ev(L, Fr(0)) > 3:
            lo, hi = 0, 2**fam.m
            while hi - lo > 1:
                mid = (lo + hi)//2
                if P.ev(L, mid*fam.Dy) > 3: lo = mid
                else: hi = mid
            return j, lo
    raise ValueError("no face with slope above 3")
