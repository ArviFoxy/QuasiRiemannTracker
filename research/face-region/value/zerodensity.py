"""Hypothetical HIGH counts: the density step with a stronger zero-density estimate for the natural dictionary.

The unmarked HIGH payment at density nu (Sil's leaf, rho(nu) M + nu (P + s) <= M) holds on P + s <= k_u(nu) M,
k_u = (1 - rho)/nu, so the step needs the crossing slope s0 >= (B - k_u)/(Lam - 1).  The marked gate (PR 76's
repeated marks) needs s0 >= (B - k_m)/(Lam - k_m), k_m(nu) = 4(5 - 3 nu)/(25 - 18 nu) (CONTINUUM.md).  With both
counts available the slope is the smaller one; both k's increase in nu, so nu = q binds.  rho in sigma = (1+nu)/2:
  baseline   rho = 1 - 10 nu / (3 (5 - 2 nu))          (A(sigma) ~ 2.3; never better than the marked count)
  Huxley     rho = 3 (1 - nu) / (1 + 3 nu)              (A = 3/(3 sigma - 1), sigma >= 3/4)
  DH-from-s0 rho = 1 - nu for sigma >= s0, Huxley below (Jutila-type range s0 = 11/14; Huxley's own s0 = 5/6)
  A<A0>      rho = A0 (1 - sigma) = A0 (1 - nu)/2 on the whole range (constant exponent A0)
[hypothetical inputs; numerical]"""
import sys
import numpy as np
from scipy.integrate import solve_ivp
from scipy.optimize import brentq
from levers import kappa as k_m, q_of, d


def rho_hux(nu):
    return 3 * (1 - nu) / (1 + 3 * nu)


def make_rho(name):
    if name == 'huxley':
        return rho_hux
    if name.startswith('dh'):
        s0 = {'dh56': 5 / 6, 'dh1114': 11 / 14}[name]
        return lambda nu: (1 - nu) if (1 + nu) / 2 >= s0 else rho_hux(nu)
    if name.startswith('A'):
        A0 = float(name[1:])
        return lambda nu: A0 * (1 - nu) / 2
    raise KeyError(name)


def slope(B, L, rho):
    q = q_of(B, L)
    km = k_m(q)
    sm = (B - km) / (L - km)
    ku = (1 - rho(q)) / q
    su = (B - ku) / (L - 1)
    return max(0.0, min(sm, su))


def curve(rho, L0=2.5715, B0=0.99999, Lend=1.80):
    sol = solve_ivp(lambda L, y: [slope(y[0], L, rho)], [L0, Lend], [B0], method='DOP853', rtol=1e-11,
                    atol=1e-13, dense_output=True, max_step=1e-3)
    return lambda L: float(sol.sol(L)[0])


if __name__ == '__main__':
    from levers_global import run
    name = sys.argv[1]
    Bc = curve(make_rho(name))
    Lq = brentq(lambda L: d * L / (6 * Bc(L) - L) - 0.5, 1.80, 2.5)
    for L in (2.5, 2.4, 2.3, 2.2, 2.1, 2.0, Lq):
        print('  %s: L=%.4f B=%.6f q=%.4f' % (name, L, Bc(L), q_of(Bc(L), L)), flush=True)
    run('zero density: %s' % name, Bc, Lq)
    run('zero density: %s, cap 0.12' % name, Bc, Lq, cap=0.12)
