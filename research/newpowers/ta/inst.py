"""Instantaneous (v=0, continuum) slope s0(B,L,q) for each count variant.
Gate at v=0 (u=0, H=1, w=s=s0):   for all nu in [q,3/4], x in [0,1/2]:
     J = cs(nu,x; s0) - nu*B + nu*(L-2x)*s0 >= 0 ,   cs = (1-R)*Q  (Q=1)
"""
import numpy as np
from scipy.optimize import brentq
import counts as C

XS = np.linspace(0, 0.5, 51)


import variants as V


def cs_variant(var, nu, x, s, Q, par):
    return V.cs(var, nu, x, s, Q, par)


def gate_v0(var, s0, B, L, q, par, nus=None):
    if nus is None:
        nus = np.linspace(q, 0.75, 7)
    nu = nus[:, None]
    x = XS[None, :]
    cs = cs_variant(var, nu, x, s0, 1.0, par)
    J = cs - nu * B + nu * (L - 2 * x) * s0
    return J.min()


def s0_inst(var, B, L, q, par, hi=0.4):
    g = lambda s: gate_v0(var, s, B, L, q, par)
    if g(0.0) >= 0:
        return 0.0
    return brentq(g, 0.0, hi, xtol=1e-13)


if __name__ == '__main__':
    pass
