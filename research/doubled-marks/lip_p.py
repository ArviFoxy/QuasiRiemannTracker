"""Slope check for the amplitude-resolved k-copy gain: for p in [p0,1/2] and every branch pair (i,j),
 a + 2b <= nu - 1/12 where f_p = (1-2p) nu S + nu (root_ij - xi0 F) and root_ij is affine in (S,F)."""
import os
HERE = os.path.dirname(os.path.abspath(__file__))
import numpy as np
def branch_slopes(nu, p, k, B, Lam, h, al=5/6):
    kk = al - nu; q1 = 1 - p
    inv = [((1/q1), (0.0, p/q1))]            # (a_i, (dS b_i, dF b_i))
    if k is not None: inv.append((1.0, (2*p*k, 0.0)))
    pl = [(1.0, (2*p, 0.0)), (1.0, (0.0, 2*p*h)), (1/(1-2*p/Lam), (0.0, (2*p*B/Lam)/(1-2*p/Lam)))]
    xi0 = al/(nu + 1.5*kk)
    out = []
    for ai, (si, fi) in inv:
        for aj, (sj, fj) in pl:
            den = nu + kk*(ai + aj/2)
            dS = kk*(si + sj/2)/den; dF = (al + kk*(fi + fj/2))/den
            a = (1-2*p)*nu + nu*dS; b = nu*(dF - xi0)
            out.append((a, b))
    return out
if __name__ == "__main__":
    import json
    ch = json.load(open(os.path.join(HERE, 'chainp_k2_0.0005.json')))
    faces = [(1.0, 4.4973108, 0.055)] + [(n['B'], n['L'], n['cap']) for n in ch[:-1]]
    worst = (1, None)
    for idx, (B, Lam, h) in enumerate(faces):
        q = ch[idx]['q']
        for nu in np.linspace(q, 0.75, 120):
            for p in np.linspace(0.476, 0.5, 25):
                for a, b in branch_slopes(nu, p, 2, B, Lam, h):
                    marg = nu - 1/12 - (a + 2*b)
                    if marg < worst[0]: worst = (marg, (idx, round(nu, 4), round(p, 4), round(a, 4), round(b, 4)))
    print("min over chain nodes, nu in [q,3/4], p in [0.476,1/2], branches of  nu-1/12-(a+2b):", worst)
