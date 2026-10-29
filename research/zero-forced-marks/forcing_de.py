"""E3c (2). Global adversary (differential evolution) against the forced slot.

Toy explicit formula: the slot at log-scale x evaluated at s0 = 1/2 (heights measured from the target) is
S(x) = sum_j What(rho_j - s0) e^{x (rho_j - s0)} over the target rho0 = beta0 and k extra zeros with real parts in
[beta0 - 0.06, beta0] (the target is the row's highest zero) and heights in [-3, 3].  Forcing ratio
F = max over x in [x1, 2 x1] and over the weights of |S(x)| / |c0(x)|.  [numerical toy]
usage: python3 forcing_de.py x1
"""
import sys
import numpy as np
from scipy.optimize import differential_evolution

TT = np.linspace(1, 2, 2001)


def bump(t):
    u = (t - 1.5) / 0.5
    return np.where(np.abs(u) < 1, np.exp(-1 / np.maximum(1 - u * u, 1e-300)), 0.0)


BUMP = bump(TT)


def mellin(a, s):
    return np.trapezoid(BUMP * TT ** a * TT ** (s - 1), TT)


NU = 0.6
BETA0 = 0.5 + NU / 2
S0 = 0.5
X1 = float(sys.argv[1]) if len(sys.argv) > 1 else 10.0
XS = np.linspace(X1, 2 * X1, 61)


def ratio(params, k, weights):
    zs = [complex(BETA0 - 0.06 * params[2 * i], params[2 * i + 1]) for i in range(k)]
    best = 0.0
    for a in weights:
        c0 = mellin(a, BETA0 - S0)
        tot = c0 * np.exp(XS * (BETA0 - S0))
        for z in zs:
            tot = tot + mellin(a, z - S0) * np.exp(XS * (z - S0))
        best = max(best, np.max(np.abs(tot) / np.abs(c0 * np.exp(XS * (BETA0 - S0)))))
    return best


if __name__ == '__main__':
    for weights in ((0,), (0, 1, 2)):
        for k in (1, 2, 3, 4, 6):
            bounds = [(0, 1), (-3, 3)] * k
            r = differential_evolution(ratio, bounds, args=(k, weights), seed=1, maxiter=200, popsize=25,
                                       tol=1e-7, polish=True)
            zs = [complex(BETA0 - 0.06 * r.x[2 * i], r.x[2 * i + 1]) for i in range(k)]
            print('x1=%g weights %-10s k=%d  worst forcing ratio %.4f  zeros %s' % (
                X1, str(weights), k, r.fun, ', '.join('%.3f%+.3fi' % (z.real, z.imag) for z in zs)), flush=True)
