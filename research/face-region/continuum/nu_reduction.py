"""Full discrete HIGH gate G(nu) = highJ(B, L, w, u, nu) + nu * min_{p,k} phi_k(p; parent B0, L0, S, Q) on nu in [q(v), 3/4]:
is the minimum at nu = q(v)?  Is G increasing in nu?  (child B = B0 - s0 h, L = L0 - h)"""
import numpy as np
from vec import phis_vec, sample
rng = np.random.default_rng(44)
P = np.linspace(0, 0.5, 401)
NUF = np.linspace(0, 1, 41)
h = 0.005
worst_gap = -np.inf; worst_slope = -np.inf; info = None
for batch in range(10):
    s = sample(1500, rng)
    n = len(s['B0'])
    nu = s['qv'][:, None] + (0.75 - s['qv'])[:, None]*NUF[None, :]            # (n, 41)
    F = phis_vec(nu[:, :, None], P[None, None, :], s['B0'][:, None, None], s['L0'][:, None, None], 0.1,
                 s['S'][:, None, None], s['Q'][:, None, None])                   # (n, 41, P, 6)
    gm = F.min(axis=(2, 3))                                                      # (n, 41)
    B = s['B0'] - s['s0']*h; L = s['L0'] - h; w = s['s0'] + s['v']; u = s['u']
    m = 10*nu/(15 - 6*nu)
    J = m - nu*B[:, None] + nu*(L - 1)[:, None]*w[:, None] - (6*m - nu - 1)*u[:, None]
    G = J + nu*gm
    gap = G[:, 0] - G.min(axis=1)                                                 # > 0 iff interior/upper nu binds
    slope = (-(np.diff(G, axis=1))).max(axis=1)                                  # max decrease between grid nus
    j = int(np.argmax(gap))
    if gap[j] > worst_gap:
        worst_gap = gap[j]; info = {k: round(float(v_[j]), 6) for k, v_ in s.items()}
    worst_slope = max(worst_slope, slope.max())
print('max [G(q(v)) - min_nu G] = %.3e ; max decrease of G between consecutive nu = %.3e' % (worst_gap, worst_slope))
print(info)
