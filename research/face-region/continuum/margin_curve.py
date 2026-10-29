"""Feasibility of a discretisation-free chain: faces on the eta-curve
   dB/dLam = (B - (kappa - eta))/(Lam - (kappa - eta))   (target lowered by eta: exact solution keeps the same form)
and steps of size h ALONG the curve (parent and child both on the curve).  For each sampled Lam, compare the chord
slope of the curve with the least slope s0_min that passes all 14 Lean gates (chain2, rigorous nu-range mode),
optimised over the selection (A, D)."""
import sys
import numpy as np
from scipy.integrate import solve_ivp
import os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', 'newpowers', 'ta'))
import chain2 as C2

def q_of(B, L): return min(0.999*L/(6*B - L), 0.75)
def kappa(q): return 4*(5 - 3*q)/(25 - 18*q)
def curve(eta, L0=2.5715, B0=0.99999, Lend=1.90):
    f = lambda L, y: [(y[0] - (kappa(q_of(y[0], L)) - eta))/(L - (kappa(q_of(y[0], L)) - eta))]
    return solve_ivp(f, [L0, Lend], [B0], method='DOP853', rtol=1e-12, atol=1e-14, dense_output=True)

eta = float(sys.argv[1]); h = float(sys.argv[2])
sol = curve(eta)
cfg = C2.Cfg(gain=1.0, floor=0.5, dfac=0.999, boot=False, dL=h, nu_mode='range', eps=1e-9)
guess = (np.log(0.6), np.log(400.0))
print('eta=%g h=%g' % (eta, h))
for L in [2.45, 2.20, 2.00, 1.95]:
    B0 = float(sol.sol(L)[0]); B1 = float(sol.sol(L - h)[0])
    chord = (B0 - B1)/h
    res = C2.best_step(cfg, B0, L, 0.1, guess, maxeval=90)
    if res is None:
        print('Lam=%.4f  no admissible step' % L); continue
    s0, A, D, n = res
    guess = (np.log(A), np.log(D))
    q = q_of(B0, L)
    print('Lam=%.4f q=%.4f chord=%.7f  s0_min=%.7f  slack=%+.2e  (A=%.3f D=%.0f)' % (L, q, chord, s0, chord - s0, A, D))
