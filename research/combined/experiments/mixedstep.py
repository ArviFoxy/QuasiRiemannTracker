# Float model: the flow with the step's slot cost 6q* replaced by min(6q*, (2+6q*)/(1+q*))
# (Sil's selected/unselected mix with the native gate q*·s < d), q* unchanged.
import sys
sys.path.insert(0, '/home/user/QuasiRiemannTracker/research/faceless-chain')
import numpy as np
import closed_flow as CF
from scipy.optimize import brentq
den, phi = 2**-15, 1e-4
def Q6(s, E, mixed):
    Q, _ = CF.q6star(s, E)      # Q = 6 q*
    q = Q/6
    return min(Q, (2 + 6*q)/(1 + q)) if mixed else Q
def slope(s, E, mixed):
    Q = Q6(s, E, mixed)
    return Q*E/((1 - Q*s)*(1 - den))*(1 + phi)
def run(mixed, B0=0.99999, lam=3.72, s1=0.06, n=60000):
    s0 = brentq(lambda s: slope(s, B0 - lam*s, mixed) - lam, 1e-3, 0.059, xtol=1e-14)
    ss = np.linspace(s0, s1, n + 1); h = ss[1] - ss[0]; E = B0 - lam*s0; out = []
    for s in ss:
        L = slope(s, E, mixed); q = CF.q6star(s, E)[0]/6
        out.append((s, E, L, q, E + L*s))
        k1 = -L; k2 = -slope(s + h/2, E + h*k1/2, mixed); k3 = -slope(s + h/2, E + h*k2/2, mixed); k4 = -slope(s + h, E + h*k3, mixed)
        E += h*(k1 + 2*k2 + 2*k3 + k4)/6
    return s0, out
for mixed in (False, True):
    s0, out = run(mixed)
    P = next(o for o in out if o[2] <= 3)                       # physical face: slope 3
    C = next((o for o in out if o[4] > 0 and o[2]/o[4] < 3.0003), out[-1])   # q floor: L/B = 3
    print(f"mixed={mixed}: tangency s0={s0:.5f}; P face s={P[0]:.5f} B={P[4]:.6f}; end (L/B=3) s={C[0]:.5f} C=({C[4]:.6f},{C[2]:.5f}); q* at s0 {out[0][3]:.4f}")
