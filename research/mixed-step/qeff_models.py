"""Price candidate LOW exchange rates for a mixed fourth/sixth-power source step.

The face family is the switching flow E' = -Qeff(q)·E/((1 - Qeff(q)·s)(1 - den)), q = max(q*, 1/2),
where q* is the HIGH threshold (closed_flow.q6star). The pure step has Qeff(q) = 6q.
Started on Sil's face at its tangency; C = last face, P = last face with slope >= 3.
usage: python3 qeff_models.py MODEL [MODEL ...]   (models below)
"""
import sys, os
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', 'faceless-chain'))
import numpy as np
from fractions import Fraction as Fr
from scipy.optimize import brentq
import closed_flow as CF
import theta_eval as T

DEN, PHI, CAP = 2**-15, 1e-4, Fr(549989, 10**7)
MODELS = {
    'pure':      lambda q: 6*q,                              # Collet: pool only
    'silbase':   lambda q: min(6*q, (2 + 6*q)/(1 + q)),      # live excess kept at 2, native q paid at 6
    'erase6':    lambda q: 6*q/(1 + q),                      # selected: saves 1, costs 6; rest erased at q
    'erase4':    lambda q: 4*q/(1 + q),                      # selected: saves 1, costs 4; rest erased at q
    'transfer4': lambda q: min(6*q, 4.0),                    # selected: no saving, costs 4 (useless below 4)
}

def run(model, B0=0.99999, lam=3.72, n=40000, qfloor=0.5):
    Qf = MODELS[model]
    def slope(s, E):
        q = max(CF.q6star(s, E)[0]/6, qfloor)
        Q = Qf(q)
        return Q*E/((1 - Q*s)*(1 - DEN))*(1 + PHI), q
    g = lambda s: slope(s, B0 - lam*s)[0] - lam
    # start at the tangency with the start face; if the flow is flatter everywhere, start at s = 1e-4
    s0 = brentq(g, 1e-4, 0.0599, xtol=1e-14) if g(1e-4) > 0 else 1e-4
    E, s, out = B0 - lam*s0, s0, []
    h = (0.06 - s0)/n
    for _ in range(n):
        L, q = slope(s, E)
        out.append((s, E, L, q, E + L*s))
        if q <= qfloor + 1e-12 and len(out) > 2 and abs(out[-1][4] - out[-2][4]) < 1e-12:
            break
        f = lambda s_, E_: -slope(s_, E_)[0]
        k1 = f(s, E); k2 = f(s + h/2, E + h*k1/2); k3 = f(s + h/2, E + h*k2/2); k4 = f(s + h, E + h*k3)
        E += h*(k1 + 2*k2 + 2*k3 + k4)/6; s += h
    # the family ends where the HIGH floor is reached (q = 1/2) or at the cap
    end = next((i for i, o in enumerate(out) if o[3] <= qfloor + 1e-9), len(out) - 1)
    C = out[end]
    P = next((o for o in reversed(out[:end + 1]) if o[2] >= 3.0), out[0])
    return s0, C, P

if __name__ == '__main__':
    for m in sys.argv[1:]:
        s0, C, P = run(m)
        fr = lambda x: Fr(x).limit_denominator(10**12)
        Cf = (fr(C[4]*(1 - 2e-9)), fr(C[2]), CAP)
        Pf = (fr(P[4]*(1 - 2e-9)), fr(P[2]), CAP)
        th = T.theta_star(Cf, Pf)
        print(f"{m:10s} s0={s0:.6f} end s={C[0]:.5f} C=({C[4]:.6f},{C[2]:.5f}) "
              f"P: s={P[0]:.5f} ({P[4]:.6f},{P[2]:.5f}) theta*={th}", flush=True)
