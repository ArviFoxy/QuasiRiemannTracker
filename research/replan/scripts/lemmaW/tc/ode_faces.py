import json
import numpy as np
from fractions import Fraction as Fr
from scipy.integrate import solve_ivp
def rhs(L, y):
    B = y[0]; q = 0.999*L/(6*B - L)
    return [(B - 10/(15 - 6*q))/(L - 1)]
sol = solve_ivp(rhs, [2.5715, 2.0], [0.99999], rtol=1e-13, atol=1e-15, dense_output=True)
def B_ode(L): return float(sol.sol(L)[0])
def q_of(B, L): return 0.999*L/(6*B - L)
def wall():
    from scipy.optimize import brentq
    return brentq(lambda L: q_of(B_ode(L), L) - 0.65, 2.30, 2.3415, xtol=1e-14)
def frac(x, den=10**10): return Fr(round(x*den), den)
if __name__ == '__main__':
    Lw = wall()
    print('wall: L=%.6f B=%.7f q=%.4f s0=%.5f' % (Lw, B_ode(Lw), q_of(B_ode(Lw), Lw), rhs(Lw, [B_ode(Lw)])[0]))
    for L in (2.3415, 2.3405, 2.3395, Lw, 2.38, 2.3865, 2.371):
        print('L=%.5f B_ode=%.7f s0=%.5f q=%.4f' % (L, B_ode(L), rhs(L, [B_ode(L)])[0], q_of(B_ode(L), L)))
