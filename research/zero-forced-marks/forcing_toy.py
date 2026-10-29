"""E3c. Can other off-line zeros cancel the slot that a zero rho0 forces?  Toy explicit formula.

Slot at scale D = e^x evaluated at s0 = 1/2 + i gamma0 with weight W:  S_W(x) = sum_j m_j What(rho_j - s0) e^{x (rho_j - s0)}.
Target alone: |c0(x)| = |What(rho0 - s0)| e^{x nu/2}.  The adversary places k extra zeros rho_j (Re rho_j >= Re rho0 - eta,
|Im| <= 3) to minimise the forcing ratio  F = max over x in [x1, x2] and over the weights W of |S_W(x)| / |c0_W(x)|.
Weights: W_a(t) = bump on [1, 2] times t^a (a = 0, 1, 2 give different Mellin transforms).  [numerical]"""
import numpy as np
from scipy.integrate import quad
from scipy.optimize import minimize

def bump(t):
    u = (t - 1.5) / 0.5
    return np.where(np.abs(u) < 1, np.exp(-1 / np.maximum(1 - u * u, 1e-300)), 0.0)

def mellin(a, s):
    re = quad(lambda t: bump(t) * t ** a * (t ** (s - 1)).real, 1, 2, limit=200)[0]
    im = quad(lambda t: bump(t) * t ** a * (t ** (s - 1)).imag, 1, 2, limit=200)[0]
    return re + 1j * im

NU = 0.6; BETA0 = 0.5 + NU / 2; RHO0 = BETA0 + 0j; S0 = 0.5 + 0j
XS = np.linspace(10, 20, 41)          # log D over a factor-2 range of slot widths
WEIGHTS = (0, 1, 2)

def ratio(zeros, weights=WEIGHTS):
    best = 0.0
    for a in weights:
        c0 = mellin(a, RHO0 - S0)
        cs = [mellin(a, r - S0) for r in zeros]
        for x in XS:
            tot = c0 * np.exp(x * (RHO0 - S0)) + sum(c * np.exp(x * (r - S0)) for c, r in zip(cs, zeros))
            best = max(best, abs(tot) / abs(c0 * np.exp(x * (RHO0 - S0))))
    return best

def adversary(k, weights, trials=12, seed=0):
    rng = np.random.default_rng(seed)
    best = (np.inf, None)
    def f(v):
        zs = [complex(BETA0 + 0.05 * np.tanh(v[2 * i]), 3 * np.tanh(v[2 * i + 1])) for i in range(k)]
        return ratio(zs, weights)
    for _ in range(trials):
        v0 = rng.normal(size=2 * k)
        r = minimize(f, v0, method='Nelder-Mead', options=dict(maxiter=300, xatol=1e-4, fatol=1e-5))
        if r.fun < best[0]:
            best = (r.fun, r.x)
    zs = [complex(BETA0 + 0.05 * np.tanh(best[1][2 * i]), 3 * np.tanh(best[1][2 * i + 1])) for i in range(k)]
    return best[0], zs

if __name__ == '__main__':
    for weights in ((0,), (0, 1), (0, 1, 2)):
        for k in (1, 2, 3):
            f, zs = adversary(k, weights)
            print('weights %-10s k=%d  worst forcing ratio %.3f  at zeros %s' % (str(weights), k, f,
                  ', '.join('%.4f%+.4fi' % (z.real, z.imag) for z in zs)), flush=True)
