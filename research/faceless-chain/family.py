"""The faceless face family: secant lines of a piecewise-cubic C^1 curve that tracks the closed-form flow.

Target: the closed-form switching flow (closed_flow.py) with LOW denominator `den` and slope factor
(1 + phi), started on the natural face at s0. On each piece [sig_j, sig_{j+1}] the curve Et is the
cubic Hermite interpolant of the target (values and slopes at both ends, rounded to rationals), so Et
is C^1 and piecewise cubic.

Node at s (Delta = step): L(s) = (Et(s) - Et(s + Delta))/Delta, B(s) = Et(s) + s L(s), cap = CAPMAX,
q(s) = (1 - den) L(s - Delta)/(6 B(s - Delta)), fine fees. The LOW and HIGH parent of F(s) is F(s - Delta);
the crossing is exactly s and the LOW denominator is exactly den.
"""
import json, sys
from fractions import Fraction as Fr
import numpy as np
import closed_flow as CF
import gates as G

K = Fr(11243277, 2500000)
CAPMAX = Fr(549989, 10000000)
FEES = (Fr(1, 10**17), Fr(1, 10**12), Fr(1, 10**10))


def rat(x, d=10**15):
    return Fr(x).limit_denominator(d)


class Family:
    def __init__(self, sig, den, Delta, Ecoef):
        self.sig = sig            # junctions (Fractions), sig[0] = s0
        self.den = den
        self.Delta = Delta
        self.Ecoef = Ecoef        # per piece: cubic coefficients in (s - sig_j), Fractions

    def piece(self, s):
        for j in range(len(self.sig) - 1):
            if s <= self.sig[j + 1]:
                return j
        return len(self.sig) - 2

    def Et(self, s, j=None):
        """Et on piece j (default: the piece containing s; right end belongs to the left piece)."""
        if j is None:
            j = self.piece(s)
        x = s - self.sig[j]
        c = self.Ecoef[j]
        return c[0] + x*(c[1] + x*(c[2] + x*c[3]))

    def node(self, s):
        """F(s); uses Et at s and s + Delta from the piece that contains [s, s + Delta]."""
        D = self.Delta
        j = self.piece(s + D) if s + D <= self.sig[-1] else len(self.sig) - 2
        # the piece must contain both s and s + Delta (junctions are grid points)
        e0, e1 = self.Et(s, j), self.Et(s + D, j)
        L = (e0 - e1)/D
        B = e0 + s*L
        return B, L

    def source(self, s, parent=None):
        B, L = self.node(s)
        if parent is None:
            parent = self.node(s - self.Delta)
        B0, L0 = parent
        q = (1 - self.den)*L0/(6*B0)
        return dict(B=B, L=L, cap=CAPMAX, q=q, allowance=FEES[0], lowFee=FEES[1], highFee=FEES[2])


def hermite(s_a, s_b, Ea, Eb, da, db):
    """Cubic coefficients in x = s - s_a with E(s_a) = Ea, E'(s_a) = da, E(s_b) = Eb, E'(s_b) = db."""
    h = s_b - s_a
    c0, c1 = Ea, da
    c2 = (3*(Eb - Ea)/h - 2*da - db)/h
    c3 = (da + db - 2*(Eb - Ea)/h)/(h*h)
    return [c0, c1, c2, c3]


def build(sig_f, den=2e-5, phi=1e-4, Delta=Fr(1, 10**7), n=40000):
    s0 = sig_f[0]
    E0 = 1 - float(K)*s0
    ss, Es = CF.flow(s0, E0, sig_f[-1], n, den=den, fudge=phi)
    sl = lambda s, E: -CF.slope(s, E, den, phi)
    sig = [rat(x, 10**7) for x in sig_f]
    vals, ders = [], []
    for x in sig:
        i = int(np.argmin(abs(ss - float(x))))
        # re-integrate from the nearest grid point to x exactly (RK4 substeps)
        s, E = ss[i], Es[i]
        h = (float(x) - s)/8
        for _ in range(8):
            k1 = sl(s, E); k2 = sl(s + h/2, E + h*k1/2); k3 = sl(s + h/2, E + h*k2/2); k4 = sl(s + h, E + h*k3)
            E += h*(k1 + 2*k2 + 2*k3 + k4)/6; s += h
        vals.append(E); ders.append(sl(float(x), E))
    vals[0] = 1 - float(K)*float(sig[0])
    Ev = [rat(v) for v in vals]
    Ev[0] = 1 - K*sig[0]
    Dv = [rat(d) for d in ders]
    coefs = [hermite(sig[j], sig[j + 1], Ev[j], Ev[j + 1], Dv[j], Dv[j + 1]) for j in range(len(sig) - 1)]
    return Family(sig, rat(den, 10**12), Delta, coefs), (ss, Es)


def margins_at(fam, s, nnu=21, npp=41, nfine=801):
    """Float margins of the step F(s - Delta) -> F(s) at both cell ends."""
    n = fam.source(s)
    B0, L0 = fam.node(s - fam.Delta)
    f = lambda x: float(x)
    nn = (f(n['B']), f(n['L']), f(n['cap']), f(n['q']), f(n['allowance']), f(n['lowFee']), f(n['highFee']))
    lo = (f(B0), f(L0), f(CAPMAX), 0.0) + nn[4:]
    mL = G.margins(nn, lo, lo, f(s), nnu, npp, nfine=nfine)
    mR = G.margins(nn, lo, lo, f(CAPMAX), nnu, npp, nfine=nfine)
    return mL, mR, nn, lo


if __name__ == "__main__":
    sig_f = [float(x) for x in sys.argv[1].split(',')]
    den = float(sys.argv[2]); phi = float(sys.argv[3])
    fam, (ss, Es) = build(sig_f, den, phi)
    worst = (1, None)
    for s in np.linspace(sig_f[0] + 1e-6, sig_f[-1], 400):
        sq = rat(s, 10**9)
        mL, mR, nn, lo = margins_at(fam, sq)
        m = min(mL['high'], mR['high'], mL['scalar'], mR['scalar'], mL['sector'], mR['sector'])
        if m < worst[0]:
            worst = (m, float(sq), mL['high'], mR['high'])
    print("worst margin", worst)
