"""Cost of ending the continuous shape before the floor ray: the eta-curve stopped where q = q_stop.
Count face = curve point at q_stop, physical face = best curve point (as in eta_cost.py)."""
import numpy as np
from fractions import Fraction as Fr
from scipy.integrate import solve_ivp
from scipy.optimize import brentq, minimize_scalar
from theta_of_faces import theta_star
d = 0.999
def q_of(B, L): return min(d*L/(6*B - L), 0.75)
def kappa(q): return 4*(5 - 3*q)/(25 - 18*q)
eta = 1e-4
f = lambda L, y: [(y[0] - (kappa(q_of(y[0], L)) - eta))/(L - (kappa(q_of(y[0], L)) - eta))]
sol = solve_ivp(f, [2.5715, 1.90], [0.99999], method='DOP853', rtol=1e-13, atol=1e-15, dense_output=True)
Bc = lambda L: float(sol.sol(L)[0])
y2, dp = 2*69313573/150000000, 0.8044451001
cap = lambda L: (y2 - (2 - Bc(L))*dp)/L
Lp = minimize_scalar(lambda L: -cap(L), bounds=(2.1, 2.4), method='bounded', options={'xatol': 1e-10}).x
pB, pL = Fr(Bc(Lp)).limit_denominator(10**12), Fr(Lp).limit_denominator(10**12)
for qs in (0.5, 0.5002, 0.5005, 0.5015, 0.503):
    Ls = brentq(lambda L: q_of(Bc(L), L) - qs, 1.90, 2.2)
    t, *_ = theta_star(Fr(Bc(Ls)).limit_denominator(10**12), Fr(Ls).limit_denominator(10**12), pB=pB, pL=pL)
    print('eta=1e-4  q_stop=%.4f  count face (B=%.8f, Lam=%.8f)  theta*=%.10f  vs merged %+.2e' % (qs, Bc(Ls), Ls, float(t), float(t) - 0.87387234))
