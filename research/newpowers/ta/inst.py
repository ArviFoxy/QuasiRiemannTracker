"""Instantaneous (v=0, continuum) slope s0(B,L,q) for each count variant.
Gate at v=0 (u=0, H=1, w=s=s0):   for all nu in [q,3/4], x in [0,1/2]:
     J = cs(nu,x; s0) - nu*B + nu*(L-2x)*s0 >= 0 ,   cs = (1-R)*Q  (Q=1)
"""
import numpy as np
from scipy.optimize import brentq
import counts as C

XS = np.linspace(0, 0.5, 51)


def cs_variant(var, nu, x, s, Q, par):
    """count saving (1-R)*Q for the variant.  par: dict(kappa, B0, L0, h0, K, sigma)"""
    if var == 'pr83':
        return (1 - C.rho(nu)) * Q + 0 * x
    if var == 'a':      # black box: dummies to the library supply 7/37 ; p = x*min(s/sigma,1)
        pe = x * np.minimum(s / par.get('sigma', C.SIG_LIB), 1.0)
        return (1 - C.rowCount(nu, pe, par['kappa'])) * Q
    if var == 'u':      # undiluted rowCount (ideal supply): p = x
        return (1 - C.rowCount(nu, x, par['kappa'])) * Q
    if var == 'c':      # face-based (return's C branch from the parent face), diluted p
        pe = x * np.minimum(s / par.get('sigma', C.SIG_LIB), 1.0)
        return (1 - C.R_face(nu, pe, par['B0'], par['L0'])) * Q
    if var == 'cu':     # face-based, undiluted
        return (1 - C.R_face(nu, x, par['B0'], par['L0'])) * Q
    if var.startswith('d'):   # repeated marks, K copies; var = 'd1','d2',...
        K = int(var[1:])
        xi = C.xi_roots(nu, x, s, Q, K, par['B0'], par['L0'], par['h0'])
        return nu * xi
    raise ValueError(var)


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
    from odemod import Ode   # B2's PR83 ODE (path set below)
