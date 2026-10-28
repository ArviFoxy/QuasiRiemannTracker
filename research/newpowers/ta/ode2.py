"""Continuum (Delta L -> 0) density chain with the Lean-faithful marked HIGH gate.   dB/dL = s0(B, L),  q = dfac L/(c6 B - L).
s0 = least slope with the v = 0 HIGH gate satisfied:
      min_{nu in [q, 3/4]} [ highJ(B, L, s0, 0, nu) + gain * gainK(nu, 8, B, L, h0, s0, 1) + shift_R ] >= 0,
parent face = current face (B, L, h0 = 0.1).   Boot face (PR 86): (0.99999, 2.5715); bootstrapped native barrier (0.99999, 2.56738).
Levers: shift_R (count exponent R -> R - shift_R, scalar or function of L), s0scale, c6, dL0/dB0 (start face), K, gain (scale of the gain).
"""
import numpy as np
from scipy.integrate import solve_ivp
from scipy.optimize import brentq
import gainc as GC
import chain2 as C2

BOOT = {False: (0.99999, 2.5715), True: (0.99999, 2.56738)}
NUF = np.array([0.0, 0.05, 0.15, 0.3, 0.5, 0.75, 1.0])


def hi_gate(B, L, s, nu, h0, gain, K, shift_R, Bgate=None):
    J = C2.highJ(B, L, s, 0.0, nu)
    if gain == 0.0:
        return J + shift_R
    g = GC.gainK(nu, K, B, L, h0, s, 1.0, ngrid=65, nref=33, levels=3)
    if B < GC.B_MIN:
        g = np.zeros_like(g)
    return J + gain * g + shift_R


def s0_inst(B, L, q, h0=0.1, gain=1.0, K=8, shift_R=0.0, nu_mode='range', hi=0.4):
    nu = q + (0.75 - q) * (NUF if nu_mode == 'range' else np.array([0.0]))

    def g(s):
        return float(np.min(hi_gate(B, L, s, nu, h0, gain, K, shift_R)))
    if g(0.0) >= 0:
        return 0.0
    return brentq(g, 0.0, hi, xtol=1e-13)


class Chain2:
    def __init__(self, gain=1.0, dfac=0.999, boot=False, c6=6.0, Lend=1.80, shift_R=0.0, h0=0.1, s0scale=1.0, K=8,
                 rtol=1e-10, dL0=0.0, dB0=0.0, nu_mode='range'):
        self.gain, self.dfac, self.boot, self.c6, self.K, self.h0 = gain, dfac, boot, c6, K, h0
        self.shift_R, self.s0scale, self.nu_mode = shift_R, s0scale, nu_mode
        B0, L0 = BOOT[boot]
        B0, L0 = B0 + dB0, L0 - dL0
        self.B0, self.L0 = B0, L0
        self.sol = solve_ivp(lambda L, y: [self.s0(y[0], L)], [L0, Lend], [B0], method='DOP853', rtol=rtol, atol=1e-13,
                             dense_output=True, events=[self._dead])
        self.Lmin = float(self.sol.t[-1])

    def _dead(self, L, y):
        return self.q(y[0], L) - 0.4
    _dead.terminal = True

    def q(self, B, L):
        return self.dfac * L / (self.c6 * B - L)

    def sR(self, L):
        return self.shift_R(L) if callable(self.shift_R) else self.shift_R

    def s0(self, B, L):
        q = min(self.q(B, L), 0.75)
        return self.s0scale * s0_inst(B, L, q, self.h0, self.gain, self.K, self.sR(L), self.nu_mode)

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
    for gain in (0.0, 1.0):
        t0 = time.time()
        c = Chain2(gain=gain)
        print('gain', gain, 'B(2.3415)=%.7f' % c.B(2.3415), 'wall(0.65)=%.4f wall(0.6)=%.4f wall(0.5)=%.4f' % (
            c.wall(0.65), c.wall(0.6), c.wall(0.5)), 'Lmin %.4f' % c.Lmin, '%.1fs' % (time.time() - t0))
