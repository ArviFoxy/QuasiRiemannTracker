"""Pointwise ideal: count = max(v_cap, v_slope) of one face (both pieces; Collet's window only needs
plainCurve(m) <= value, which max(v_cap, v_slope) always satisfies), with guards r in [23/37, 1], t in [1, tmax],
antitone, natural tail at mHi (per face), and the witness >= mLo.  Compare with the merged guard set."""
import numpy as np
from fractions import Fraction as Fr
from fast import branch, old_count
from model import hceiling
ETA = 1e-7

def face_count(d, p, B, L, cap, tmax=1.5, mLo=0.0, mHi=None, K=4.5, need_antitone=True, tail=True):
    """returns (ok, value) for the 'max of both pieces' window of face (B, L, cap) at (d, p)"""
    bs = branch(d, p, B, L, cap, False)
    bc = branch(d, p, B, L, cap, True)
    vs = bs['N'] / bs['J']; vc = bc['N'] / bc['J']
    use_c = vc >= vs
    v = np.where(use_c, vc, vs)
    b = {k: np.where(use_c, bc[k], bs[k]) for k in bs}
    D, J, T, RN, DJ, U, dU, dJ = (b[k] for k in ('D', 'J', 'T', 'RN', 'DJ', 'U', 'dU', 'dJ'))
    t = T / J; r = RN / DJ
    # value v -> cutoff t(v), crossing r(v): from the lines (exact for the chosen branch); m = t - r
    m = t - r
    ok = (D > 0) & (J > 0) & (t > 1) & (t < tmax) & (r > 23 / 37) & (r < 1) & (m > mLo + ETA)
    if need_antitone:
        ok &= (U * dJ - dU * J > 0)
    if tail:
        if mHi is None: mHi = min((B - L * 1e-4) / 2, 0.4999)
        sM = (1 - 2 * mHi) / K
        ok &= (v >= 1 - 2 * mHi * d - 2 * sM * d * p)
    return ok, v

def E_newtop(theta, DD, PP, env, numCap=0.075, pB=0.99999, pL=2.02):
    h = float(hceiling(Fr(theta).limit_denominator(10 ** 12)))
    c = 1 - theta; ell = 4 * c - 1 / 3; y = h - 2 * ell; kappa = 1 - 2 * c; dd = h + 1e-10
    C = min(numCap * dd, (2 * y - (2 - pB) * dd) / pL)
    oc = old_count(DD, PP, kappa)
    envv = np.minimum(env, oc)
    E = 0.5 + 13 * h / 75 - y / 2 - ell / 2 - 0.09 * dd + DD / 2 + DD * PP * (ell - C / 2) + 0.75 * dd * envv
    return E, oc

def theta_star(DD, PP, env, reserve=1e-8, **kw):
    lo, hi = 0.86, 0.885
    for _ in range(44):
        mid = (lo + hi) / 2
        E, _ = E_newtop(mid, DD, PP, env, **kw)
        if E.max() > mid - reserve: lo = mid
        else: hi = mid
    E, oc = E_newtop(hi, DD, PP, env, **kw)
    k = np.unravel_index(np.argmax(E), E.shape)
    return hi, k, oc

if __name__ == '__main__':
    d = np.round(np.arange(0.20, 0.75, 0.0005), 6)
    p = np.round(np.concatenate([np.arange(0.0, 0.49, 0.01), [0.49, 0.495, 0.499, 0.5]]), 6)
    DD, PP = np.meshgrid(d, p, indexing='ij')
    src = (0.99999, 2.02, 0.13309)
    for label, kw in [('full face, relaxed (t<1.5, mLo=0, tail at B/2)', dict()),
                      ('full face, t<1.2499', dict(tmax=1.2499)),
                      ('full face, mLo=0.377', dict(mLo=0.377)),
                      ('full face, merged tail (mHi=0.4325)', dict(mHi=0.4325)),
                      ('full face, no antitone', dict(need_antitone=False)),
                      ('full face, no tail at all', dict(tail=False))]:
        ok, v = face_count(DD, PP, *src, **kw)
        env = np.where(ok, v, np.inf)
        th, k, oc = theta_star(DD, PP, env)
        who = 'old' if oc[k] <= env[k] else 'face'
        frac = ok.mean()
        print('%-48s theta* = %.8f  bind d=%.4f p=%.3f via %s  (admissible %.2f)' % (label, th, d[k[0]], p[k[1]], who, frac))
