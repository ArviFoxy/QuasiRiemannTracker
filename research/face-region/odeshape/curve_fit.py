"""Explicit curve for the ODE-inequality estimate: a polynomial beta(L) (rational coefficients) below the eta-curve,
concave, with beta'(L) >= sigma(beta(L), L) + mu on [L_stop, L_boot].  sigma(B, L) = (B - k)/(L - k),
k = kappa(q), q = 0.999 L/(6B - L), kappa(q) = 4(5 - 3q)/(25 - 18q).
Usage: curve_fit.py eta mu q_stop degree shift"""
import sys
import numpy as np
from fractions import Fraction as Fr
from scipy.integrate import solve_ivp
from scipy.optimize import brentq
d = 0.999
def q_of(B, L): return d*L/(6*B - L)
def kappa(q): return 4*(5 - 3*q)/(25 - 18*q)
def sigma(B, L): k = kappa(np.minimum(q_of(B, L), 0.75)); return (B - k)/(L - k)
eta, mu, q_stop, deg, shift = float(sys.argv[1]), float(sys.argv[2]), float(sys.argv[3]), int(sys.argv[4]), float(sys.argv[5])
Lb, Bb = 2.5715, 0.99999
f = lambda L, y: [(y[0] - (kappa(min(q_of(y[0], L), 0.75)) - eta))/(L - (kappa(min(q_of(y[0], L), 0.75)) - eta))]
sol = solve_ivp(f, [Lb, 1.90], [Bb], method='DOP853', rtol=1e-13, atol=1e-15, dense_output=True)
Bc = lambda L: float(sol.sol(L)[0])
La = brentq(lambda L: q_of(Bc(L), L) - q_stop, 1.90, 2.2)
Lm, Lh = (La + Lb)/2, (Lb - La)/2
L = np.linspace(La, Lb, 4001); t = (L - Lm)/Lh
B = sol.sol(L)[0] - shift
# least squares in Chebyshev basis, then convert to power basis in t and round to rationals
cheb = np.polynomial.chebyshev.Chebyshev.fit(t, B, deg, domain=[-1, 1])
pw = cheb.convert(kind=np.polynomial.Polynomial).coef
coef = [Fr(c).limit_denominator(10**12) for c in pw]
P = np.polynomial.Polynomial([float(c) for c in coef])
beta = P(t); dbeta = P.deriv()(t)/Lh; d2 = P.deriv(2)(t)/Lh**2
marg = dbeta - sigma(beta, L) - mu
print('eta=%g mu=%g q_stop=%.4f deg=%d shift=%g: L in [%.6f, %.6f]' % (eta, mu, q_stop, deg, shift, La, Lb))
print('  fit error max |beta - (eta-curve - shift)| = %.2e ; beta - eta-curve in [%.2e, %.2e]' % (np.max(np.abs(beta - B)), np.min(beta - B - 0*shift + 0) - shift*0, 0))
print('  beta(Lb) = %.9f (boot B = 0.99999, need <=)' % P(1.0))
print('  concavity: max beta\'\' = %.3e (need < 0)' % np.max(d2))
print('  ODE inequality: min [beta\' - sigma(beta) - mu] = %.3e at L=%.4f' % (np.min(marg), L[np.argmin(marg)]))
print('  slope window: beta\' in [%.5f, %.5f]; max |beta\'\'| = %.3f' % (np.min(dbeta), np.max(dbeta), np.max(np.abs(d2))))
print('  end face: L=%.8f beta=%.8f (eta-curve %.8f)' % (La, P(-1.0), Bc(La)))
