"""Binding pair at p = 1/2, as exact functions of (v, nu):
 Gamma_12(v,nu) = nu[(L-1)w - B + R(nu)] - u[6 nu R(nu) - nu - 1],    R = (L0-1+x B0)/(L0-1+x L0),  x = w/(2(5+w)), w=5-6nu
 Gamma_10(v,nu) = nu[(L-1)w - B + (1 + x S)/(1+x)] + u[nu + 1 - 6 nu/(1+x)],  S = w_v - u
(child B, L in highJ; parent B0, L0 in the gain).  Check: min over the full gate (all p, facets, nu) equals
min over v of min(Gamma_10, Gamma_12)(v, q(v)) on real chain steps."""
import json, sys
import numpy as np
from fractions import Fraction as Fr
sys.path.insert(0, __import__('os').path.join(__import__('os').path.dirname(__import__('os').path.abspath(__file__)), '..', 'continuum'))
from vec import phis_vec
steps = json.load(open(__import__('os').path.join(__import__('os').path.dirname(__import__('os').path.abspath(__file__)), '..', '..', 'chain', 'steps_f050_dL200.json')))
def pair(v, nu, B0, L0, B, L, s0, A, D):
    w_ = 5 - 6*nu; x = w_/(2*(5 + w_))
    u = A*v/(1 + D*v); wv = s0 + v; S = wv - u
    R = (L0 - 1 + x*B0)/(L0 - 1 + x*L0)
    g12 = nu*((L - 1)*wv - B + R) - u*(6*nu*R - nu - 1)
    g10 = nu*((L - 1)*wv - B + (1 + x*S)/(1 + x)) + u*(nu + 1 - 6*nu/(1 + x))
    return g10, g12
P = np.linspace(0, 0.5, 801)
for idx in [0, 40, 80, 120, 128]:
    st = steps[idx]
    B0, L0, c0, B, L, A, D = (float(Fr(st[k])) for k in ('B0', 'L0', 'c0', 'B', 'L', 'A', 'D'))
    h = L0 - L; s0 = (B0 - B)/h; vmax = 0.1 - s0
    V = vmax*np.linspace(0, 1, 401)**2
    full_min = np.inf; pair_min = np.inf; pair_q_min = np.inf
    for v in V:
        u = A*v/(1 + D*v); wv = s0 + v; S = wv - u; Q = 1 - 6*u
        q = min(0.999*L0*A/(h*(1 + D*v) + (6*B0 - L0)*A), 0.75)
        NU = q + (0.75 - q)*np.linspace(0, 1, 41)
        m = 10*NU/(15 - 6*NU)
        J = m - NU*B + NU*(L - 1)*wv - (6*m - NU - 1)*u
        F = phis_vec(NU[:, None], P[None, :], B0, L0, c0, S, Q)          # (41, P, 6)
        full = J + NU*F.min(axis=(1, 2))
        full_min = min(full_min, full.min())
        g10, g12 = pair(v, NU, B0, L0, B, L, s0, A, D)
        pair_min = min(pair_min, np.minimum(g10, g12).min())
        g10q, g12q = pair(v, q, B0, L0, B, L, s0, A, D)
        pair_q_min = min(pair_q_min, min(g10q, g12q))
    print('step %3d: full gate min %.3e | pair min over nu %.3e | pair at nu=q(v) min %.3e' % (idx + 1, full_min, pair_min, pair_q_min))
