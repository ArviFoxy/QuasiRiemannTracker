"""Critical ratios: phi_k(p; S, Q) is linear in (S, Q): phi_k = a_k S - b_k Q.  For the comparison with the binding value
phi*(nu) = min(phi_10(1/2), phi_12(1/2)) (also linear: phi_10(1/2) = a S - b Q, phi_12(1/2) = -b' Q) we need
phi_k(p) - phi_12(1/2) >= 0  <=>  S/Q >= rho_k(p, nu).   Evaluate max over p, nu in [q(vmax), 3/4] along the chain."""
import json, sys
import numpy as np
from fractions import Fraction as Fr
import sympy as sp
from facets_exact import phi, p, w, B, L, S, Q, h0, half
# linear coefficients a_k(p,w,B,L), b_k(p,w,B,L) with phi_k = a_k*S - b_k*Q  (h0 = 1/10)
phi = {k: sp.together(f.subs(h0, sp.Rational(1, 10))) for k, f in phi.items()}
coef = {}
for k, f in phi.items():
    a = sp.simplify(sp.diff(f, S)); b = sp.simplify(-sp.diff(f, Q))
    assert sp.simplify(f - (a*S - b*Q)) == 0
    coef[k] = (sp.lambdify((p, w, B, L), a, 'numpy'), sp.lambdify((p, w, B, L), b, 'numpy'))
a12, b12 = coef[(1, 2)]
steps = json.load(open(__import__('os').path.join(__import__('os').path.dirname(__import__('os').path.abspath(__file__)), '..', '..', 'chain', 'steps_f050_dL200.json')))
P = np.linspace(0, 0.5, 501)[:, None]
for idx in [0, 32, 64, 96, 120, 127, 128]:
    st = steps[idx]
    B0, L0, Bc, Lc, A, D = (float(Fr(st[k])) for k in ('B0', 'L0', 'B', 'L', 'A', 'D'))
    h = L0 - Lc; s0 = (B0 - Bc)/h; vmax = 0.1 - s0
    qmin = 0.999*L0*A/(h*(1 + D*vmax) + (6*B0 - L0)*A)
    NU = np.linspace(qmin, 0.75, 121)[None, :]
    W = 5 - 6*NU
    phistar_b = b12(0.5, W, B0, L0)                    # phi_12(1/2) = -b12 Q  (a12 = 0 at p = 1/2?)
    a12h = a12(0.5, W, B0, L0)
    out = []
    for k in [(0, 0), (0, 1), (0, 2), (1, 0), (1, 1), (1, 2)]:
        ak, bk = coef[k]
        a_ = ak(P, W, B0, L0) - a12h; b_ = bk(P, W, B0, L0) - phistar_b
        # condition a_ S - b_ Q >= 0 ; if a_ > 0: S/Q >= b_/a_ ; if a_ <= 0 need b_ <= 0 (and then S large hurts)
        with np.errstate(divide='ignore', invalid='ignore'):
            rho = np.where(a_ > 0, b_/a_, np.where(b_ <= 0, -np.inf, np.inf))
        out.append((k, float(np.max(rho))))
    print('step %3d s0=%.5f qmin=%.4f  ' % (idx + 1, s0, qmin) + '  '.join('%s:%.4f' % (k, r) for k, r in out))
