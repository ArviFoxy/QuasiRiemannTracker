"""Generalized repeated-mark HIGH gate (float), for pricing new HIGH-count inputs.

The original gate (`../faceless-chain/gates.py: high_gate`) is the minimum over six closed-form
branch pairs.  Here the same-zero detector cutoff equation is solved numerically, so that new
witness options (extra inverse/plain/long branches, other slot costs, a separate count of
saturated rows) can be added without a closed form.

Notation (as in gates.py): node n = (B, L, cap, q, e, r, f); width b; S = b - 2e; F = F0 - e;
T = t + b; HIGH parent h = (B_H, L_H, h_H); density nu; amplitude class p in [0, 1/2].
margin = base/tt + nu*xi, with base/tt = (a - nu T) + (10 - 60 a) nu/tt + (1-2p) nu S - 10 nu F/tt - f,
and xi the root of the cutoff equation

    nu*xi + (kL - nu) * t_cut(xi) = kL * F,      t_cut(xi) = I(xi) + P(xi)/2,

(kL = 5/6: the unmarked long inverse moment (Q + 5r)/6 of (204)), with the witness thresholds
    I(xi) = max(xi - 2pKS, (xi - 2pF/cI)/(1 - 2p/cI))          (cI = 2: Theorem 7.3)
    P(xi) = max(xi - 2pS, xi - 2p h_H F, (xi - 2p B_H F/L_H)/(1 - 2p/L_H)).
For kL = 5/6, cI = 2 this is exactly 6 nu xi + w (I + P/2) = 5F, i.e. gates.high_gate.

`model` (dict) switches on the candidate modifications; see `thresholds`.
"""
import numpy as np


def basics_default(n, low, b):
    import gates as G
    return G.basics(n, low, b)


def _I_orig(xi, p, K, S, F, cI=2.0):
    return np.maximum(xi - 2*p*K*S, (xi - 2*p*F/cI)/(1 - 2*p/cI))


def _P_orig(xi, p, S, F, BH, LH, hc):
    return np.maximum(np.maximum(xi - 2*p*S, xi - 2*p*hc*F), (xi - 2*p*BH*F/LH)/(1 - 2*p/LH))


def thresholds(xi, nu, p, K, S, F, BH, LH, hc, model):
    """Return the cutoff t_cut(xi) = I + P/2 (the detector cutoff needed for target xi)."""
    cI = model.get('cI', 2.0)
    I = _I_orig(xi, p, K, S, F, cI)
    P = _P_orig(xi, p, S, F, BH, LH, hc)
    if 'plain_face2' in model:
        # an additional (stronger) face usable for the plain witness: the threshold is the min
        B2, L2, h2 = model['plain_face2']
        P2 = _P_orig(xi, p, S, F, B2, L2, h2)
        P = np.minimum(P, P2)
    return I + P/2


def solve_xi(nu, p, K, S, F, BH, LH, hc, model, iters=64):
    kL = model.get('kL', 5/6)
    lo = np.zeros(np.broadcast(nu, p).shape)
    hi = np.full_like(lo, 2.0*F)
    for _ in range(iters):
        mid = 0.5*(lo + hi)
        tc = thresholds(mid, nu, p, K, S, F, BH, LH, hc, model)
        lhs = nu*mid + (kL - nu)*tc - kL*F
        up = lhs > 0
        hi = np.where(up, mid, hi)
        lo = np.where(up, lo, mid)
    return 0.5*(lo + hi)


def high_gate_gen(n, low, h, b, nu, p, copies=8, model=None, basics=None):
    """Normalized HIGH margin on a (nu, p) grid: array (1, m, k) (single 'branch' = the min)."""
    model = model or {}
    basics = basics or basics_default
    B, L, cap, q, e, r, f = n
    t_, den, a, F0 = basics(n, low, b)
    T = t_ + b
    S = b - 2*e
    F = F0 - e
    K = copies
    BH, LH, hc = h[0], h[1], h[2]
    nu = np.asarray(nu, float)[:, None]; p = np.asarray(p, float)[None, :]
    tt = 15 - 6*nu
    base = (a - nu*T)*tt + (10 - 60*a)*nu + tt*(1 - 2*p)*nu*S - 10*nu*F - f*tt
    xi = solve_xi(nu, p, K, S, F, BH, LH, hc, model)
    xi = xi + model.get('dxi', 0.0)*np.where(p >= model.get('dxi_pmin', 0.0), 1.0, 0.0)
    marg = base/tt + nu*xi
    if 'extra' in model:
        # an additional complete bound for the class mass (e.g. a separate count of saturated rows):
        # the class is fine if EITHER bound pays; extra(...) returns its margin on the grid
        marg = np.maximum(marg, model['extra'](n, low, h, b, nu, p, dict(T=T, S=S, F=F, a=a, f=f, K=K)))
    return marg[None]
