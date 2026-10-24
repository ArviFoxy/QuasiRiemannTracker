"""Vectorized amplitude-resolved HIGH gain (p as an array axis).
G_K(nu,S,F) = min_p min_branches f_p ;  slope-capped G' = min(G_K, (nu-1/12) S)."""
import numpy as np

def f_all(nu, S, F, ps, K, BL, al=5/6):
    """nu: (n,), ps: (m,) -> array (m,n) of f_p over branch minima. K=None: cap-only inverse."""
    B, Lam, hc = BL
    p = ps[:, None]; nu_ = nu[None, :]
    kk = al - nu_
    q1 = 1 - p
    inv = [(1/q1, p*F/q1)]
    if K is not None:
        inv.append((np.ones_like(p), 2*p*K*S))
    pl = [(np.ones_like(p), 2*p*S), (np.ones_like(p), 2*p*hc*F),
          (1/(1-2*p/Lam), (2*p*B*F/Lam)/(1-2*p/Lam))]
    roots = None
    for (ai, bi) in inv:
        for (aj, bj) in pl:
            r = (al*F + kk*(bi + bj/2))/(nu_ + kk*(ai + aj/2))
            roots = r if roots is None else np.minimum(roots, r)
    xi0F = al*F/(nu_ + 1.5*kk)
    return (1-2*p)*nu_*S + nu_*(roots - xi0F)

PS = np.unique(np.concatenate([np.linspace(0, 0.44, 12), np.linspace(0.44, 0.5, 31)]))

def gain(HP, K=2, cap=False, ps=PS, margin=1/12):
    def g(nu, S, Fp):
        G = f_all(np.atleast_1d(nu), S, Fp, ps, K, HP).min(axis=0)
        if cap:
            G = np.minimum(G, (np.atleast_1d(nu) - margin)*S)
        return G
    return g
