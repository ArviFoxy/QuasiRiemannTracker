"""ode_amp.py -- continuum density-step ODE with a general amplifier mixture (R2).

PR 83's step in the limit dL -> 0, v -> 0 (B2_source_slope.md s1.2, re-derived here from StepGates.lean:122-165):
    LOW   :  q (dL v + (c B0 - r L0) u) <= e L0 u        ->  q <= f e L / (c B - r L)      (f = 0.999, PR83's `dens`)
    HIGH  :  J(0) = q [ (1-rho(q))/q - B + (L-1) s0 ] = 0 ->  s0 = (B - 10/(15-6q)) / (L-1)
    dB/dL = s0(B, L),  q = min(3/4, q_inf(L,B)),   (e,c,r) = (1,6,1) reproduces dB/dL = (B - 10/(15-6q))/(L-1), q = f L/(6B-L).

`types` is a list of Amp (ledger.py): the best type sets q (capacity of the best type is not binding as v -> 0, see report s5).
"""
import numpy as np
from scipy.integrate import solve_ivp
from scipy.optimize import brentq
from ledger import qinf, SIMPLE

QMAX = 0.75


def thr(q):
    return 10.0 / (15.0 - 6.0 * q)


class OdeAmp:
    def __init__(self, types=(SIMPLE,), f=0.999, qmax=QMAX, B0=0.99999, L0=2.5715, Lend=1.2, eps=0.0, dthr=0.0,
                 dl=0.0, floor_ignore=False):
        self.types = tuple(types)
        self.f, self.qmax = f, qmax
        self.eps, self.dthr, self.dl = eps, dthr, dl
        self.L0, self.B0, self.Lend = L0, B0, Lend
        self.sol = solve_ivp(lambda L, y: [self.s0(y[0], L)], [L0, Lend], [B0], rtol=1e-11, atol=1e-13,
                             dense_output=True)

    def q(self, B, L):
        return qinf(L, B, self.types, self.f, self.qmax)

    def s0(self, B, L):
        q = self.q(B, L)
        return (1 - self.eps) * (B - thr(q) - self.dthr) / (L - 1 + self.dl)

    def B(self, L):
        return float(self.sol.sol(L)[0])

    def slope(self, L):
        return self.s0(self.B(L), L)

    def qinf(self, L):
        return self.q(self.B(L), L)

    def wall(self, floor, lo=1.3, hi=2.5715):
        """largest-L crossing where q_inf drops to the density floor; None if q_inf stays above the floor on [lo,hi]."""
        g = lambda L: self.qinf(L) - floor
        Ls = np.linspace(hi, lo, 600)
        prev = Ls[0]
        if g(prev) < 0:
            return hi
        for L in Ls[1:]:
            if g(L) < 0:
                return brentq(g, L, prev, xtol=1e-12)
            prev = L
        return None


if __name__ == "__main__":
    o = OdeAmp()
    for L in (2.3415, 2.30, 2.25, 2.20):
        print(L, round(o.B(L), 6), round(o.slope(L), 5), round(o.qinf(L), 4))
    print("wall(0.60) =", o.wall(0.60), " B2 reports 2.2031 / B 0.97855")
