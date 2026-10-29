"""Cost of the margin eta: the provable continuous shape is the eta-curve dB/dLam = (B - k)/(Lam - k), k = kappa(q) - eta,
from the boot face (0.99999, 2.5715).  Count face = the curve point on the floor ray q = 1/2; physical face = the
curve point that maximises the newTop capacity.  theta* from theta_of_faces.py (same return model)."""
import numpy as np
from fractions import Fraction as Fr
from scipy.integrate import solve_ivp
from scipy.optimize import brentq, minimize_scalar
from theta_of_faces import theta_star
d = 0.999
rf = (0.5 + d)/3
def q_of(B, L): return min(d*L/(6*B - L), 0.75)
def kappa(q): return 4*(5 - 3*q)/(25 - 18*q)
for eta in (0.0, 1e-5, 1e-4):
    f = lambda L, y: [(y[0] - (kappa(q_of(y[0], L)) - eta))/(L - (kappa(q_of(y[0], L)) - eta))]
    sol = solve_ivp(f, [2.5715, 1.90], [0.99999], method='DOP853', rtol=1e-13, atol=1e-15, dense_output=True)
    Bc = lambda L: float(sol.sol(L)[0])
    Lf = brentq(lambda L: Bc(L)/L - rf, 1.90, 2.0)
    y2, dp = 2*69313573/150000000, 0.8044451001
    cap = lambda L: (y2 - (2 - Bc(L))*dp)/L
    Lp = minimize_scalar(lambda L: -cap(L), bounds=(2.1, 2.4), method='bounded', options={'xatol': 1e-10}).x
    cB, cL = Fr(Bc(Lf)).limit_denominator(10**12), Fr(Lf).limit_denominator(10**12)
    pB, pL = Fr(Bc(Lp)).limit_denominator(10**12), Fr(Lp).limit_denominator(10**12)
    t, *_ = theta_star(cB, cL, pB=pB, pL=pL)
    print('eta=%.0e  count face (B=%.8f, Lam=%.8f)  physical face (B=%.8f, Lam=%.6f, cap %.8f)  theta*=%.10f  vs merged %+.2e'
          % (eta, Bc(Lf), Lf, Bc(Lp), Lp, cap(Lp), float(t), float(t) - 0.87387234))
