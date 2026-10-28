"""Continuum (Delta L -> 0) density chain for a count variant:  dB/dL = s0(B,L),  q = dfac*L/(6B-L).
s0 = least slope with the v=0 HIGH gate satisfied  (inst.s0_inst).  Parent HIGH face = current (B,L,h0=0.1).
Boot face (PR 86): (0.99999, 2.5715); bootstrapped native barrier (kappa=2*theta_rec-1): (0.99999, 2.56738).
"""
import numpy as np
from scipy.integrate import solve_ivp
from scipy.optimize import brentq
import inst

KAPPA_NAT = 0.75
KAPPA_BOOT = 2 * (4369779 / 5000000) - 1      # 0.7479116
BOOT = {False: (0.99999, 2.5715), True: (0.99999, 2.56738)}


class Chain:
    def __init__(self, var='pr83', dfac=0.999, boot=False, c6=6.0, Lend=1.80, shift_R=0.0, h0=0.1, sigma=None,
                 s0scale=1.0, rtol=1e-11, dL0=0.0, dB0=0.0):
        self.var, self.dfac, self.boot, self.c6 = var, dfac, boot, c6
        self.kappa = KAPPA_BOOT if boot else KAPPA_NAT
        self.h0 = h0
        self.shift_R = shift_R
        self.sigma = sigma
        self.s0scale = s0scale
        B0, L0 = BOOT[boot]
        B0, L0 = B0 + dB0, L0 - dL0
        self.B0, self.L0 = B0, L0
        self.sol = solve_ivp(lambda L, y: [self.s0(y[0], L)], [L0, Lend], [B0], rtol=rtol, atol=1e-13,
                             dense_output=True, events=[self._dead])
        self.Lmin = float(self.sol.t[-1])

    def _dead(self, L, y):
        return self.q(y[0], L) - 0.4
    _dead.terminal = True

    def q(self, B, L):
        return self.dfac * L / (self.c6 * B - L)

    def par(self, B, L):
        d = dict(kappa=self.kappa, B0=B, L0=L, h0=self.h0)
        if self.sigma is not None:
            d['sigma'] = self.sigma
        d['shift_R'] = self.shift_R(L) if callable(self.shift_R) else self.shift_R
        return d

    def s0(self, B, L):
        q = min(self.q(B, L), 0.75)
        return self.s0scale * inst.s0_inst(self.var, B, L, q, self.par(B, L))

    def B(self, L):
        return float(self.sol.sol(L)[0])

    def slope(self, L):
        return self.s0(self.B(L), L)

    def qinf(self, L):
        return self.q(self.B(L), L)

    def wall(self, floor):
        return brentq(lambda L: self.qinf(L) - floor, self.Lmin + 1e-9, 2.57, xtol=1e-12)


if __name__ == '__main__':
    import time
    for var in ('pr83', 'd2'):
        t0 = time.time()
        c = Chain(var)
        print(var, 'B(2.3415)=%.7f' % c.B(2.3415), 'wall(0.6)=%.4f' % c.wall(0.60), 'Lmin %.4f' % c.Lmin, '%.1fs' % (time.time() - t0))
