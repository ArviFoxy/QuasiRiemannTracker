"""Pointwise theta* of the E5 retune design (newTop edge) when the natural join mHi is per branch
(mHi_b = (B_b - L_b*sig)/2, natural tail 1-2 d mHi - 2 d p (1-2 mHi)/K) and the cutoff bound is 3/2.
Guards that Lean never consumes (1, 2, 12, 14) are dropped; for uncapped branches the upper witness bound is
dropped (unused in CountDecode), for capped branches only (B - L Zc)/2 - eta is kept."""
import numpy as np
from fractions import Fraction as Fr
from fast import branch, old_count
from model import hceiling
ETA = 1e-7
MMINUS, K = 0.377, 4.5

def guards_relaxed(d, p, B, L, cap, capped, nm, upper_t=1.5, mMinus=MMINUS, keep_unused=False):
    b = branch(d, p, B, L, cap, capped)
    Zc = b['Zc']
    sM = (1 - 2 * nm) / K
    lowerM = (mMinus + ETA) if capped else max(mMinus + ETA, (B - L * (cap - ETA)) / 2 + ETA)
    upperM = ((B - L * Zc) / 2 - ETA) if capped else 1.0
    D, A, C0, U, J, N, T, RN, MN, DJ, dU, dJ = (b[k] for k in ('D', 'A', 'C0', 'U', 'J', 'N', 'T', 'RN', 'MN', 'DJ', 'dU', 'dJ'))
    tail = 1 - 2 * nm * d - 2 * sM * d * p
    g = [D, J, T - J, upper_t * J - T, RN - 23 / 37 * DJ, DJ - RN, MN - lowerM * DJ, upperM * DJ - MN,
         N - tail * J, U * dJ - dU * J]
    # widths: (B - 2 nm)/L > nu (1e-7) ; nm in [2/5, 1/2)
    wid = (B - 2 * nm) / L - 2e-7
    return g, b, wid

def admissible(d, p, B, L, cap, capped, nm, **kw):
    g, b, wid = guards_relaxed(d, p, B, L, cap, capped, nm, **kw)
    ok = np.ones(np.broadcast(*[np.asarray(x) for x in g]).shape, dtype=bool)
    for x in g: ok &= (x > 0)
    ok &= (wid > 0) & (nm >= 0.4) & (nm < 0.5)
    return ok, b['N'] / b['J']

class Model:
    def __init__(self, DG, PG):
        self.DG, self.PG = DG, PG
        self.DD, self.PP = np.meshgrid(DG, PG, indexing='ij')
        self._h = {}
    def hceil(self, theta):
        k = round(theta * 1e12)
        if k not in self._h: self._h[k] = float(hceiling(Fr(theta).limit_denominator(10 ** 12)))
        return self._h[k]
    def best_count(self, faces, sig=1e-4, nm_override=None, upper_t=1.5, tail_off=False):
        names = list(faces)
        best = np.full(self.DD.shape, np.inf); who = np.full(self.DD.shape, -1)
        for k, nm_ in enumerate(names):
            B, L, cap, capped = faces[nm_]
            nm = nm_override if nm_override is not None else min((B - L * sig) / 2, 0.4999)
            ok, c = admissible(self.DD, self.PP, B, L, cap, capped, nm, upper_t=upper_t)
            cc = np.where(ok, c, np.inf)
            upd = cc < best
            best = np.where(upd, cc, best); who = np.where(upd, k, who)
        return best, who, names
    def E_newtop(self, theta, best, numCap, pB, pL):
        h = self.hceil(theta)
        c = 1 - theta; ell = 4 * c - 1 / 3; y = h - 2 * ell; kappa = 1 - 2 * c; dd = h + 1e-10
        C = min(numCap * dd, (2 * y - (2 - pB) * dd) / pL)
        oc = old_count(self.DD, self.PP, kappa)
        env = np.minimum(best, oc)
        E = 0.5 + 13 * h / 75 - y / 2 - ell / 2 - 0.09 * dd + self.DD / 2 + self.DD * self.PP * (ell - C / 2) + 0.75 * dd * env
        return E, oc, C
    def theta_star(self, faces, numCap=0.075, pB=0.99999, pL=2.02, reserve=1e-8, **kw):
        best, who, names = self.best_count(faces, **kw)
        lo, hi = 0.86, 0.885
        for _ in range(44):
            mid = (lo + hi) / 2
            E, oc, C = self.E_newtop(mid, best, numCap, pB, pL)
            if E.max() > mid - reserve: lo = mid
            else: hi = mid
        E, oc, C = self.E_newtop(hi, best, numCap, pB, pL)
        k = np.unravel_index(np.argmax(E), E.shape)
        wh = 'old' if oc[k] <= best[k] else names[who[k]]
        return hi, (float(self.DG[k[0]]), float(self.PG[k[1]]), wh, C)

def faces_of(cB, cL, cCap, w, pB, pL, pCap):
    return {'C': (cB, cL, cCap, False), 'capC': (cB, cL, cCap, True), 'weakC7': (cB - w, cL, cCap, False), 'capP': (pB, pL, pCap, True)}

if __name__ == '__main__':
    d = np.round(np.arange(0.28, 0.70, 0.0002), 6)
    p = np.round(np.concatenate([np.arange(0.30, 0.49, 0.01), [0.49, 0.495, 0.499, 0.5]]), 6)
    M = Model(d, p)
    fc = faces_of(3913/4000, 101/50, 21/200, 22/625, 0.99999, 2.02, 0.1097)
    nmC = (1 - 4.5 * 0.03) / 2
    print('retune design, merged guards (nm = 0.4325, t<1.2499):', M.theta_star(fc, nm_override=nmC, upper_t=1.2499))
    print('retune design, nm = 0.4325, t<1.5:', M.theta_star(fc, nm_override=nmC, upper_t=1.5))
    for sig in (0.03, 0.02, 0.01, 0.005, 0.002, 1e-3, 1e-4):
        print('per-branch natural join sig=%g:' % sig, M.theta_star(fc, sig=sig))
