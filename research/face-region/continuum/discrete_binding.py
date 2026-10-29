"""Discrete marked HIGH gate of each chain step: argmin over (v, nu, p, facet).
gate = highJ(B, L, w, u, nu) + gainP_k(nu, p; B0, L0, c0, S = w - u, Q = H)   (all six facets, p in [0,1/2])."""
import sys, json, os
import numpy as np
from fractions import Fraction as Fr
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from faces import load_faces
K = 8
def facet_vals(nu, p, B0, L0, h0, S, Q):
    w = 5 - 6*nu; base = 10/(15 - 6*nu)
    inv = [(1.0, -2*p*K*S), (1/(1-p), -p*Q/(1-p))]
    d2 = 1 - 2*p/L0
    pl = [(1.0, -2*p*S), (1.0, -2*p*h0*Q), (1/d2, -(2*p*B0*Q/L0)/d2)]
    out = []
    for si, oi in inv:
        for sj, oj in pl:
            slope = 6*nu + w*(si + sj/2); off = w*(oi + oj/2)
            out.append((1 - 2*p)*nu*S + nu*((5*Q - off)/slope - base*Q))
    return np.stack(out, -1)
def highJ(B, L, w, u, nu):
    m = 10*nu/(15 - 6*nu)
    return m - nu*B + nu*(L - 1)*w - (6*m - nu - 1)*u
steps = json.load(open(os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', 'chain', 'steps_f050_dL200.json')))
P = np.linspace(0, 0.5, 401)
NU = np.linspace(0, 1, 41)
for idx in list(range(0, 129, 8)) + [127, 128]:
    st = steps[idx]
    B0, L0, c0, B, L, c, A, D = (float(Fr(st[k])) for k in ('B0','L0','c0','B','L','c','A','D'))
    s0 = (B0 - B)/(L0 - L)
    V = (c - s0)*np.linspace(0, 1, 81)**2
    best = (np.inf, None)
    for v in V:
        w = s0 + v; u = A*v/(1 + D*v); H = 1 - 6*u
        q = 0.999*L0*A/((L0 - L)*(1 + D*v) + (6*B0 - L0)*A)
        for t in NU:
            nu = q + (0.75 - q)*t
            g = highJ(B, L, w, u, nu) + facet_vals(nu, P[:, None], B0, L0, c0, w - u, H)[:, 0, :]
            i, k = np.unravel_index(np.argmin(g), g.shape)
            if g[i, k] < best[0]:
                best = (g[i, k], (v, t, P[i], k, q))
    g, (v, t, p, k, q) = best
    q0 = 0.999*L0*A/((L0 - L) + (6*B0 - L0)*A)
    y0 = (5 - 6*q0)/(25 - 18*q0)
    sig = (B0 - 1 + y0)/(L0 - 1 + y0)
    print(f'step {idx+1:3d} A={A:.4f} D={D:8.2f} s0={s0:.6f} sigma(q(0))={sig:.6f} diff={s0-sig:+.2e}  min gate={g:.2e} at v={v:.4f} nu-frac={t:.2f} p={p:.4f} facet={k} q(v)={q:.4f}')
