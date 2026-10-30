"""Worth of hypothetical new inputs at the selected-leaf binding point (float model of the newTop row).
Patches the long slope 5/6 (V = LONG - delta) in the branch polynomials; theta* by bisection on the newTop edge only.
[numerical, float model; relative changes only]"""
import numpy as np
import fast
from ideal import face_count

def make_branch(LONG):
    orig = fast.branch.__wrapped__ if hasattr(fast.branch, '__wrapped__') else fast.branch
    src = orig
    def branch(d, p, B, L, cap, capped):
        b = src(d, p, B, L, cap, capped)
        # recompute with V = LONG - d
        d_, p_ = np.asarray(d, float), np.asarray(p, float)
        V = LONG - d_
        D, A, C0, U, Z = b['D'], b['A'], b['C0'], b['U'], b['Z']
        J = V * D + d_ * (1 - p_) * A
        N = (1 - d_) * J + V * d_ * U
        T = J + d_ * U
        RN = A * T + (Z - p_) * J
        MN = D * T - RN
        dJ = b['dD'] * V + d_ * (-A + b['dA'] * (1 - p_)) if 'dD' in b else b['dJ']
        out = dict(b); out.update(V=V, J=J, N=N, T=T, RN=RN, MN=MN, DJ=D * J)
        return out
    branch.__wrapped__ = src
    return branch

def old_count(d, p, kappa, LONG):
    k3 = 3 * kappa; V = LONG - d
    oldD = 3 - p - 2 * p / k3; oldC = 2 * (1 - p) * (1 - p / k3)
    J = V * oldD + d * oldC; N = (1 - d) * J + d * oldC * V / 2
    return N / J

d = np.round(np.arange(0.30, 0.65, 0.0005), 6)
p = np.round(np.array([0.40, 0.45, 0.48, 0.49, 0.495, 0.499, 0.5]), 6)
DD, PP = np.meshgrid(d, p, indexing='ij')

def theta_star(LONG, L=401/200, B=0.99999, cap=None, h=0.8001361, numCap=0.075, reserve=1e-8):
    if cap is None: cap = 0.1 + 0.06 * (5143/2000 - L)
    fast.branch = make_branch(LONG)
    import ideal; ideal.branch = fast.branch
    ok, v = face_count(DD, PP, B, L, cap)
    env = np.where(ok, v, np.inf)
    lo, hi = 0.86, 0.885
    for _ in range(50):
        th = (lo + hi) / 2
        c = 1 - th; ell = 4 * c - 1 / 3; y = h - 2 * ell; kappa = 1 - 2 * c; dd = h + 1e-10
        C = min(numCap * dd, (2 * y - (2 - B) * dd) / L)
        e = np.minimum(env, old_count(DD, PP, kappa, LONG))
        E = 0.5 + 13 * h / 75 - y / 2 - ell / 2 - 0.09 * dd + DD / 2 + DD * PP * (ell - C / 2) + 0.75 * dd * e
        if E.max() > th - reserve: lo = th
        else: hi = th
    k = np.unravel_index(np.argmax(E), E.shape)
    return hi, DD[k], PP[k], e[k]

base = theta_star(5/6)
print('base (5/6): theta* %.8f  bind delta %.4f p %.3f count %.5f' % base)
for LONG in (5/6 - 0.002, 5/6 - 0.005, 5/6 - 0.0107, 0.82, 0.80, 0.75):
    t = theta_star(LONG)
    print('long slope %.5f: theta* %.8f (dtheta %+.2e)  bind delta %.4f p %.3f count %.5f' % ((LONG, t[0], t[0] - base[0]) + t[1:]))
for L in (2.0, 1.97, 1.9, 1.8):
    t = theta_star(5/6, L=L)
    print('face Lambda %.3f: theta* %.8f (dtheta %+.2e)' % (L, t[0], t[0] - base[0]))
