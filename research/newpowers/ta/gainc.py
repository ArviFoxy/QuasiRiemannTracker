"""Lean-faithful repeated-mark gain (Submissions/arvi_repeated_marks_on_sil_face_20261025):
    Gain/Gain.lean   invSlope/invOffset/plainSlope/plainOffset/branchSlope/branchOffset/branchRoot/xiP/gainP/gainK
    Source/GainC.lean gainC nu B lam h S Q = if ParentParams nu 8 B lam h then gainK nu 8 B lam h (max S 0) (max Q 0) else 0

    ParentParams nu K B lam h :  0 < nu <= 3/4,  0 <= K,  22/23 <= B <= 1,  1 < lam,  0 <= h <= 1.

Notation:  w(nu) = 5 - 6 nu,  baseXi(nu) = 10/(15 - 6 nu),
    invSlope p   = [1, 1/(1-p)]           invOffset p K S Q   = [-(2 p K S), -(p Q)/(1-p)]
    plainSlope p = [1, 1, 1/(1-2p/lam)]   plainOffset p B lam h S Q = [-(2 p S), -(2 p h Q), -(2 p B Q/lam)/(1-2p/lam)]
    branchSlope  = 6 nu + w (invSlope_i + plainSlope_j / 2)       branchOffset = w (invOffset_i + plainOffset_j / 2)
    branchRoot   = (5 Q - branchOffset)/branchSlope               xiP = min over the 2 x 3 branches
    gainP nu p K B lam h S Q = (1-2p) nu S + nu (xiP - baseXi nu * Q),     gainK = inf_{p in [0,1/2]} gainP.

Two implementations:
  * float / numpy, vectorised, the inf over p by hierarchical grid refinement (error ~1e-11)   -> gainK, gainC
  * exact (Fractions) single point evaluation of gainP and of the six facets                    -> gainP_exact
"""
import numpy as np
from fractions import Fraction as Fr

K_COPIES = 8
B_MIN = 22.0 / 23.0


# ------------------------------------------------------------------ float implementation
def facets(nu, p, K, B, lam, h, S, Q):
    """six facet values  (1-2p) nu S + nu (branchRoot_k - baseXi nu Q);  arrays broadcast; returns list of 6 arrays"""
    nu, p, S, Q, B, lam, h = np.broadcast_arrays(*(np.asarray(a, dtype=float) for a in (nu, p, S, Q, B, lam, h)))
    w = 5.0 - 6.0 * nu
    base = 10.0 / (15.0 - 6.0 * nu)
    inv = [(np.ones_like(p), -(2.0 * p * K * S)), (1.0 / (1.0 - p), -(p * Q) / (1.0 - p))]
    d2 = 1.0 - 2.0 * p / lam
    pl = [(np.ones_like(p), -(2.0 * p * S)), (np.ones_like(p), -(2.0 * p * h * Q)),
          (1.0 / d2, -(2.0 * p * B * Q / lam) / d2)]
    out = []
    for (si, oi) in inv:
        for (sj, oj) in pl:
            slope = 6.0 * nu + w * (si + sj / 2.0)
            off = w * (oi + oj / 2.0)
            root = (5.0 * Q - off) / slope
            out.append((1.0 - 2.0 * p) * nu * S + nu * (root - base * Q))
    return out


def gainP(nu, p, K, B, lam, h, S, Q):
    f = facets(nu, p, K, B, lam, h, S, Q)
    r = f[0]
    for g in f[1:]:
        r = np.minimum(r, g)
    return r


def gainK(nu, K, B, lam, h, S, Q, ngrid=65, nref=33, levels=3, return_p=False):
    """inf_{p in [0,1/2]} gainP, vectorised over the broadcast of (nu, B, lam, h, S, Q); hierarchical refinement."""
    nu, B, lam, h, S, Q = np.broadcast_arrays(*(np.asarray(a, dtype=float) for a in (nu, B, lam, h, S, Q)))
    shp = nu.shape
    lo = np.zeros(shp)
    hi = np.full(shp, 0.5)
    best = None
    bp = None
    for lev in range(levels):
        m = ngrid if lev == 0 else nref
        t = np.linspace(0.0, 1.0, m)
        pg = lo[..., None] + (hi - lo)[..., None] * t
        vals = gainP(nu[..., None], pg, K, B[..., None], lam[..., None], h[..., None], S[..., None], Q[..., None])
        i = np.argmin(vals, axis=-1)
        v = np.take_along_axis(vals, i[..., None], -1)[..., 0]
        pb = np.take_along_axis(pg, i[..., None], -1)[..., 0]
        if best is None:
            best, bp = v, pb
        else:
            upd = v < best
            best = np.where(upd, v, best)
            bp = np.where(upd, pb, bp)
        step = (hi - lo) / (m - 1)
        lo, hi = np.maximum(pb - step, 0.0), np.minimum(pb + step, 0.5)
    return (best, bp) if return_p else best


def parent_ok(nu, B, lam, h, K=K_COPIES):
    nu, B, lam, h = np.broadcast_arrays(*(np.asarray(a, dtype=float) for a in (nu, B, lam, h)))
    return (nu > 0) & (nu <= 0.75) & (B >= B_MIN) & (B <= 1.0) & (lam > 1.0) & (h >= 0.0) & (h <= 1.0) & (K >= 0)


def gainC(nu, B, lam, h, S, Q, K=K_COPIES, **kw):
    """Lean `Source.gainC` (K = 8): gainK at the nonnegative parts, 0 outside ParentParams."""
    nu, B, lam, h, S, Q = np.broadcast_arrays(*(np.asarray(a, dtype=float) for a in (nu, B, lam, h, S, Q)))
    g = gainK(nu, K, B, lam, h, np.maximum(S, 0.0), np.maximum(Q, 0.0), **kw)
    return np.where(parent_ok(nu, B, lam, h, K), g, 0.0)


# ------------------------------------------------------------------ exact implementation
def facets_exact(nu, p, K, B, lam, h, S, Q):
    nu, p, K, B, lam, h, S, Q = (Fr(a) for a in (nu, p, K, B, lam, h, S, Q))
    w = 5 - 6 * nu
    base = Fr(10) / (15 - 6 * nu)
    inv = [(Fr(1), -(2 * p * K * S)), (1 / (1 - p), -(p * Q) / (1 - p))]
    d2 = 1 - 2 * p / lam
    pl = [(Fr(1), -(2 * p * S)), (Fr(1), -(2 * p * h * Q)), (1 / d2, -(2 * p * B * Q / lam) / d2)]
    out = {}
    for i, (si, oi) in enumerate(inv):
        for j, (sj, oj) in enumerate(pl):
            slope = 6 * nu + w * (si + sj / 2)
            off = w * (oi + oj / 2)
            root = (5 * Q - off) / slope
            out[(i, j)] = (1 - 2 * p) * nu * S + nu * (root - base * Q)
    return out


def gainP_exact(nu, p, K, B, lam, h, S, Q):
    f = facets_exact(nu, p, K, B, lam, h, S, Q)
    k = min(f, key=f.get)
    return f[k], k


if __name__ == '__main__':
    # self-checks
    rng = np.random.default_rng(1)
    for _ in range(5):
        nu = rng.uniform(0.5, 0.75); B = rng.uniform(0.96, 1); lam = rng.uniform(1.8, 3); h = rng.uniform(0.05, 0.14)
        S = rng.uniform(0.02, 0.12); Q = rng.uniform(0.9, 1.0); p = rng.uniform(0, 0.5)
        fl = float(gainP(nu, p, 8, B, lam, h, S, Q))
        ex, k = gainP_exact(*(Fr(float(a)) for a in (nu, p, 8, B, lam, h, S, Q)))
        print('gainP float vs exact: %.15f %.15f  facet %s  diff %.1e' % (fl, float(ex), k, fl - float(ex)))
    # p = 0 gives nu S ;  p = 1/2 slot-free
    nu, B, lam, h, S, Q = 0.62, 0.985, 2.3, 0.1, 0.07, 0.95
    print('gainP(p=0) - nu S =', float(gainP(nu, 0.0, 8, B, lam, h, S, Q)) - nu * S)
    g, p = gainK(nu, 8, B, lam, h, S, Q, return_p=True)
    print('gainK =', g, 'argmin p =', p, ' nu*S =', nu * S, ' gainC =', gainC(nu, B, lam, h, S, Q))
    # homogeneity: gainK(D S, D Q) = D gainK(S, Q)
    print('homogeneity defect', float(gainK(nu, 8, B, lam, h, 1.7 * S, 1.7 * Q)) - 1.7 * g)
    # p scan
    for pp in np.linspace(0, 0.5, 11):
        f = [float(x) for x in facets(nu, pp, 8, B, lam, h, S, Q)]
        print('p=%.2f gainP=%.6f facets=%s' % (pp, min(f), ' '.join('%.5f' % x for x in f)))
