"""Window-based cover simulation (float, fine grid) for a branch set under a guard regime; all four edges.
Envelope(d, p) = min(old, min over windows [dlo, dhi] x [pLo, 1/2] containing (d, p) of the branch value),
where a window must be admissible on its whole rectangle (grid)."""
import numpy as np
from fractions import Fraction as Fr
from fast import branch, old_count
from model import hceiling
from pointwise import count_guarded

def edges(theta, h, numCap, pB, pL):
    c = 1 - theta; ell = 4 * c - 1 / 3; y = h - 2 * ell; kappa = 1 - 2 * c
    d0, dm, dp = 1 / 200, 19 / 25, h + 1e-10
    oldC = lambda d: min(d, 2 * y - d) / (6 * kappa)
    newC = lambda d: min(numCap * d, (2 * y - (2 - pB) * d) / pL)
    return [('oldSmall', d0, oldC(d0)), ('oldSwitch', dm, oldC(dm)), ('newSwitch', dm, newC(dm)), ('newTop', dp, newC(dp))], ell, y, kappa

def excess(theta, DD, PP, env_fn, numCap=0.075, pB=0.99999, pL=2.02, reserve=1e-8, h=None):
    h = float(hceiling(Fr(theta).limit_denominator(10 ** 12))) if h is None else h
    E_all, ell, y, kappa = edges(theta, h, numCap, pB, pL)
    env = np.minimum(env_fn, old_count(DD, PP, kappa))
    out = {}
    for nm, dd, C in E_all:
        E = 0.5 + 13 * h / 75 - y / 2 - ell / 2 - 0.09 * dd + DD / 2 + DD * PP * (ell - C / 2) + 0.75 * dd * env
        out[nm] = E - (theta - reserve)
    return out

def windows_for(DG, PG, ok_grid, plos):
    """ok_grid[i, j]: admissible at DG[i], PG[j] (PG ascending, last = 0.5). returns list of (ilo, ihi, jlo)"""
    W = []
    for jlo in plos:
        col = ok_grid[:, jlo:].all(axis=1)
        i = 0; n = len(DG)
        while i < n:
            if col[i]:
                k = i
                while k + 1 < n and col[k + 1]: k += 1
                W.append((i, k, jlo)); i = k + 1
            else:
                i += 1
    return W

def envelope(DG, PG, branches, regime, plos_idx=None):
    DD, PP = np.meshgrid(DG, PG, indexing='ij')
    env = np.full(DD.shape, np.inf)
    allw = []
    for name, (B, L, cap, capped) in branches.items():
        ok, v = count_guarded(DD, PP, B, L, cap, capped, regime)
        plos = plos_idx if plos_idx is not None else range(len(PG))
        W = windows_for(DG, PG, ok, plos)
        for (ilo, ihi, jlo) in W:
            sub = v[ilo:ihi + 1, jlo:]
            env[ilo:ihi + 1, jlo:] = np.minimum(env[ilo:ihi + 1, jlo:], sub)
            allw.append((name, DG[ilo], DG[ihi], PG[jlo]))
    return DD, PP, env, allw

def theta_cover(DG, PG, branches, regime, numCap=0.075, pB=0.99999, pL=2.02, reserve=1e-8, plos_idx=None, lo=0.868, hi=0.878):
    DD, PP, env, W = envelope(DG, PG, branches, regime, plos_idx)
    for _ in range(40):
        mid = (lo + hi) / 2
        ex = excess(mid, DD, PP, env, numCap, pB, pL, reserve)
        if max(e.max() for e in ex.values()) > 0: lo = mid
        else: hi = mid
    ex = excess(hi, DD, PP, env, numCap, pB, pL, reserve)
    worst = {k: (float(v.max()), DG[np.unravel_index(np.argmax(v), v.shape)[0]], PG[np.unravel_index(np.argmax(v), v.shape)[1]]) for k, v in ex.items()}
    return hi, worst, W, env

if __name__ == '__main__':
    from pointwise import REGIMES
    DG = np.round(np.arange(0.0, 0.7501, 0.0005), 6)
    PG = np.round(np.concatenate([np.arange(0.0, 0.48, 0.02), np.arange(0.48, 0.5, 0.0025), [0.5]]), 6)
    full = (0.99999, 2.02, 0.13309)
    for label, regime, br in [
        ('relaxed: C_full + capC_full', 'tail+t+mLo0', {'C': (*full, False), 'capC': (*full, True)}),
        ('relaxed: C_full + capC_full + capC(0.12)', 'tail+t+mLo0', {'C': (*full, False), 'capC': (*full, True), 'capC2': (0.99999, 2.02, 0.12, True)}),
        ('tail+t (mLo 0.377): C_full + capC(0.12) + capC(0.11)', 'tail+t', {'C': (*full, False), 'capC': (0.99999, 2.02, 0.12, True), 'capC2': (0.99999, 2.02, 0.11, True)}),
        ('merged guards: C_full + capC_full', 'merged', {'C': (*full, False), 'capC': (*full, True)}),
    ]:
        th, worst, W, env = theta_cover(DG, PG, br, REGIMES[regime])
        print('%-58s theta* = %.8f windows %d' % (label, th, len(W)))
        for k, v in worst.items(): print('     %-10s max excess %.2e at d=%.4f p=%.4f' % (k, *v))
