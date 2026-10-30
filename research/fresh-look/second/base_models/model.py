"""Float/Fraction model of the final return (Return/Formulas.lean, Constants.lean) for slack analysis.

Everything mirrors research/density/gen_return86.py (branch_polys, guards, row_poly), but evaluates
pointwise instead of building Bernstein covers.
"""
import math
from fractions import Fraction as Fr

ETA = 1e-7


class P:
    """return constants; defaults = Return/Constants.lean (current merged values)"""

    def __init__(self, theta=Fr(43693617, 50000000), h=Fr(8044451, 10000000),
                 cB=Fr(96232839, 100000000), cL=Fr(3853, 2000), cCap=Fr(9999, 100000),
                 pB=Fr(49283557, 50000000), pL=Fr(4503, 2000), pCap=Fr(31, 500),
                 numCap=Fr(3, 50), dm=Fr(19, 25), reserve=Fr(1, 10 ** 8), mMinus=Fr(377, 1000),
                 sMinus=Fr(3, 100), K=Fr(9, 2), exact=False):
        conv = (lambda v: Fr(v)) if exact else (lambda v: float(v))
        self.exact = exact
        self.theta = conv(theta); self.h = conv(h)
        self.cB, self.cL, self.cCap = conv(cB), conv(cL), conv(cCap)
        self.pB, self.pL, self.pCap = conv(pB), conv(pL), conv(pCap)
        self.numCap, self.dm, self.reserve = conv(numCap), conv(dm), conv(reserve)
        self.mMinus, self.sMinus, self.K = conv(mMinus), conv(sMinus), conv(K)
        self.eta = Fr(1, 10 ** 7) if exact else 1e-7
        self.finish()

    def finish(self):
        one = Fr(1) if self.exact else 1.0
        self.c = 1 - self.theta
        self.ell = 4 * self.c - one / 3
        self.x = 1 + self.ell - self.h
        self.y = self.h - 2 * self.ell
        self.kappa = 1 - 2 * self.c
        self.dp = self.h + (Fr(1, 10 ** 10) if self.exact else 1e-10)
        self.d0 = one / 200
        self.naturalM = (1 - self.K * self.sMinus) / 2
        return self

    def old_capacity(self, d):
        return min(d, 2 * self.y - d) / (6 * self.kappa)

    def new_capacity(self, d):
        return min(self.numCap * d, (2 * self.y - (2 - self.pB) * d) / self.pL)

    def edges(self):
        return [('oldSmall', self.d0, self.old_capacity(self.d0)),
                ('oldSwitch', self.dm, self.old_capacity(self.dm)),
                ('newSwitch', self.dm, self.new_capacity(self.dm)),
                ('newTop', self.dp, self.new_capacity(self.dp))]

    def face(self, cand):
        if cand in ('C', 'capC'):
            return (self.cB, self.cL, self.cCap)
        if cand == 'weakC7':
            return (self.cB - (Fr(7, 4000) if self.exact else 7 / 4000), self.cL, self.cCap)
        if cand in ('P', 'capP'):
            return (self.pB, self.pL, self.pCap)
        raise KeyError(cand)


def old_JN(Pm, d, p):
    k3 = 3 * Pm.kappa
    V = 5 / 6 - d if not Pm.exact else Fr(5, 6) - d
    oldD = 3 - p - 2 * p / k3
    oldC = 2 * (1 - p) * (1 - p / k3)
    J = V * oldD + d * oldC
    N = (1 - d) * J + d * oldC * V / 2
    return J, N


def branch_vals(Pm, cand, d, p, face=None):
    """dict of the Formulas.lean quantities at (delta=d, p); face=(B, L, cap, capped) overrides"""
    exact = Pm.exact
    V = (Fr(5, 6) if exact else 5 / 6) - d
    if face is None:
        B, L, cap = Pm.face(cand)
        capped = cand in ('capP', 'capC')
    else:
        B, L, cap, capped = face
    Zc = cap - Pm.eta
    if capped:
        D = 3 - p; A = 2 + 0 * p; C0 = 1 - 2 * Zc * p; Z = 2 * Zc * p
        dD, dA, dC = -1, 0, -2 * Zc
    else:
        D = 3 - p - 4 * p / L; A = 2 - 4 * p / L; C0 = 1 - 2 * B * p / L; Z = 2 * B * p / L
        dD, dA, dC = -1 - 4 / L, -4 / L, -2 * B / L
    U = (1 - p) * C0
    J = V * D + d * (1 - p) * A
    N = (1 - d) * J + V * d * U
    T = J + d * U
    RN = A * T + (Z - p) * J
    MN = D * T - RN
    DJ = D * J
    dU = -C0 + dC * (1 - p)
    dJ = dD * V + d * (-A + dA * (1 - p))
    return dict(D=D, A=A, C0=C0, Z=Z, U=U, J=J, N=N, T=T, RN=RN, MN=MN, DJ=DJ, dU=dU, dJ=dJ,
                B=B, L=L, cap=cap, Zc=Zc, capped=capped, V=V)


def guard_vals(Pm, cand, d, p, face=None, upper_t=None, mlo=None, mhi=None):
    """the 15 guards of admissionGuard (Formulas.lean:75) at (d, p); optional overrides of the
    cutoff bound 12499/10000 (upper_t), the plain floor (mlo) and the natural join (mhi)"""
    br = branch_vals(Pm, cand, d, p, face)
    exact = Pm.exact
    eta = Pm.eta
    B, L, cap, Zc, capped = br['B'], br['L'], br['cap'], br['Zc'], br['capped']
    nm = Pm.naturalM if mhi is None else mhi
    mMinus = Pm.mMinus if mlo is None else mlo
    eleven = Fr(11, 25) if exact else 11 / 25
    sM = Pm.sMinus if mhi is None else (1 - 2 * nm) / (6 * (Pm.K / 6))  # tail slope of the natural face
    if capped:
        lowerM = mMinus + eta
        upperM = min(min(eleven - eta, nm - eta), (B - L * Zc) / 2 - eta)
    else:
        lowerM = max(mMinus + eta, (B - L * (cap - eta)) / 2 + eta)
        upperM = min(min(eleven - eta, nm - eta), (B - L * (sM + eta)) / 2 - eta)
    D, A, C0, U, J, N, T, RN, MN, DJ, dU, dJ = (br[k] for k in ('D', 'A', 'C0', 'U', 'J', 'N', 'T', 'RN', 'MN', 'DJ', 'dU', 'dJ'))
    tail = 1 - 2 * nm * d - 2 * sM * d * p
    ut = (Fr(12499, 10000) if exact else 1.2499) if upper_t is None else upper_t
    g = [D, A, C0, J, T - J, ut * J - T,
         RN - (Fr(23, 37) if exact else 23 / 37) * DJ, DJ - RN,
         MN - lowerM * DJ, upperM * DJ - MN,
         N - tail * J,
         U * dJ - dU * J,
         eleven - nm - eta,
         B - 2 * nm - L * (sM + eta) - 2 * eta,
         (Zc - sM - eta) * DJ if capped else 1]
    return g, br


GUARD_NAMES = ['D>0', 'A>0', 'C0>0', 'J>0', 't>1', 't<1.2499', 'r>23/37', 'r<1', 'm>lowerM', 'm<upperM',
               'natural tail', 'antitone (dR/dp<=0)', '11/25>naturalM', 'widths (const)', 'cap>sMinus (const)']


def count(Pm, cand, d, p, face=None):
    if cand == 'old':
        J, N = old_JN(Pm, d, p)
        return N / J
    br = branch_vals(Pm, cand, d, p, face)
    return br['N'] / br['J']


def witness(Pm, cand, d, p, face=None):
    """(t, r, m) = (cutoff, inverse crossing, plain length)"""
    br = branch_vals(Pm, cand, d, p, face)
    return br['T'] / br['J'], br['RN'] / br['DJ'], br['MN'] / br['DJ']


def ebase(Pm, dd, C, d, p):
    return (Fr(1, 2) if Pm.exact else 0.5) + 13 * Pm.h / 75 - Pm.y / 2 - Pm.ell / 2 - (Fr(9, 100) if Pm.exact else 0.09) * dd \
        + d / 2 + d * p * (Pm.ell - C / 2)


def row_exponent(Pm, edge, d, p, cnt):
    for nm, dd, C in Pm.edges():
        if nm == edge:
            return ebase(Pm, dd, C, d, p) + (Fr(3, 4) if Pm.exact else 0.75) * dd * cnt
    raise KeyError(edge)


def hceiling(theta, hu=Fr(806, 1000)):
    """exact largest h allowed by BoundsN.floor_margin (gen_return86.hceiling without rounding)"""
    theta = Fr(theta)
    ell = Fr(11, 3) - 4 * theta

    def fm(h):
        x = 1 + ell - h; y = h - 2 * ell; dP = h + Fr(1, 10 ** 10)
        sig = x / 2 + (y - x) / 12
        return sig - Fr(1, 200) - (Fr(4, 25) * x - Fr(3, 20) - Fr(51, 100) * y + Fr(67, 100) * dP - Fr(3, 20) * ell)
    f0, f1 = fm(Fr(0)), fm(Fr(1))
    return min(-f0 / (f1 - f0), hu - Fr(1, 10 ** 6))
