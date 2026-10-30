"""High-resolution pointwise model of the five-branch design (newTop edge only; other edges have slack > 8e-3
and are verified separately). theta* by bisection with h = exact floor-margin ceiling (continuous)."""
import numpy as np
from fractions import Fraction as Fr
from fast import admissible, old_count
from model import hceiling

def grid(dstep=0.0002, plo=0.30, phi=0.62, pstep=0.0125, pmin=0.35):
    d = np.round(np.arange(plo, phi + 1e-9, dstep), 6)
    p = np.round(np.arange(pmin, 0.5 + 1e-9, pstep), 6)
    return d, p

class D6:
    def __init__(self, DG, PG):
        self.DG, self.PG = DG, PG
        self.DD, self.PP = np.meshgrid(DG, PG, indexing='ij')
        self._hcache = {}

    def hceil(self, theta):
        k = round(theta * 1e12)
        if k not in self._hcache:
            self._hcache[k] = float(hceiling(Fr(theta).limit_denominator(10**12)))
        return self._hcache[k]

    def best_count(self, faces, mMinus=0.377, upper_t=1.2499):
        """faces: dict name -> (B, L, cap, capped). returns best admissible count and index of the branch"""
        names = list(faces)
        best = np.full(self.DD.shape, np.inf); who = np.full(self.DD.shape, -1)
        for k, nm in enumerate(names):
            B, L, cap, capped = faces[nm]
            ok, c = admissible(self.DD, self.PP, B, L, cap, capped, mMinus=mMinus, upper_t=upper_t)
            cc = np.where(ok, c, np.inf)
            upd = cc < best
            best = np.where(upd, cc, best); who = np.where(upd, k, who)
        return best, who, names

    def E_newtop(self, theta, best, numCap, pB, pL, reserve, h=None):
        h = self.hceil(theta) if h is None else h
        c = 1 - theta; ell = 4 * c - 1 / 3; y = h - 2 * ell; kappa = 1 - 2 * c; dd = h + 1e-10
        C = min(numCap * dd, (2 * y - (2 - pB) * dd) / pL)
        oc = old_count(self.DD, self.PP, kappa)
        env = np.minimum(best, oc)
        E = 0.5 + 13 * h / 75 - y / 2 - ell / 2 - 0.09 * dd + self.DD / 2 + self.DD * self.PP * (ell - C / 2) + 0.75 * dd * env
        return E, oc, C

    def theta_star(self, faces, numCap, pB=0.99999, pL=2.02, reserve=1e-8, **kw):
        best, who, names = self.best_count(faces, **kw)
        lo, hi = 0.865, 0.885
        for _ in range(42):
            mid = (lo + hi) / 2
            E, oc, C = self.E_newtop(mid, best, numCap, pB, pL, reserve)
            if E.max() > mid - reserve: lo = mid
            else: hi = mid
        E, oc, C = self.E_newtop(hi, best, numCap, pB, pL, reserve)
        k = np.unravel_index(np.argmax(E), E.shape)
        wh = 'old' if oc[k] <= best[k] else names[who[k]]
        return hi, (self.DG[k[0]], self.PG[k[1]], wh, C)

def faces_of(cB, cL, cCap, w, pB, pL, pCap):
    return {'C': (cB, cL, cCap, False), 'capC': (cB, cL, cCap, True), 'weakC7': (cB - w, cL, cCap, False), 'capP': (pB, pL, pCap, True)}
