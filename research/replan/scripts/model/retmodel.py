"""Python model of the 'return' of PR83-86 (Return/Formulas.lean, Constants.lean, Conductor.lean, Windows.lean).
Condition certified by the Lean rows: for each of the four conductor edges e and all (delta,p) in [0,3/4]x[0,1/2]
    Ebase(d_e,C_e,delta,p) + (3/4) d_e * envelope(delta,p) < theta - reserve,
where envelope = min(old count, counts of every admission window available at (delta,p))."""
import numpy as np
from dataclasses import dataclass, field

EPS7 = 1e-7

@dataclass
class Face:
    B: float
    L: float
    cap: float
    is_cap: bool = False   # True for the 'capP' branch (physical slot cap), False for count faces

@dataclass
class Ret:
    c: float
    h: float
    faces: dict                  # branch name -> Face   (e.g. 'C','capP','fourthC')
    physB: float                 # physicalB used by newCapacity
    physL: float                 # physicalLambda used by newCapacity
    mMinus: float
    sMinus: float = 0.03
    naturalK: float = 4.5
    numeratorCap: float = 0.06
    dm: float = 0.76
    d0: float = 0.005
    reserve: float = 1e-8
    windows: list = field(default_factory=list)   # (branch, dlo, dhi, plo)

    @property
    def theta(self): return 1 - self.c
    @property
    def ell(self): return 4 * self.c - 1 / 3
    @property
    def x(self): return 1 + self.ell - self.h
    @property
    def y(self): return self.h - 2 * self.ell
    @property
    def kappa(self): return 1 - 2 * self.c
    @property
    def dp(self): return self.h + 1e-10
    @property
    def naturalM(self): return (1 - self.naturalK * self.sMinus) / 2

    def oldCap(self, d): return min(d, 2 * self.y - d) / (6 * self.kappa)
    def newCap(self, d): return min(self.numeratorCap * d, (2 * self.y - (2 - self.physB) * d) / self.physL)

    def edges(self):
        return {'oldSmall': (self.d0, self.oldCap(self.d0)),
                'oldSwitch': (self.dm, self.oldCap(self.dm)),
                'newSwitch': (self.dm, self.newCap(self.dm)),
                'newTop': (self.dp, self.newCap(self.dp))}

    def Ebase(self, d, C, dl, p):
        return 0.5 + 13 * self.h / 75 - self.y / 2 - self.ell / 2 - 9 * d / 100 + dl / 2 + dl * p * (self.ell - C / 2)

    # ---- branch quantities --------------------------------------------------------
    def old_count(self, dl, p):
        k = self.kappa
        V = 5 / 6 - dl
        oD = 3 - p - 2 * p / (3 * k)
        oC = 2 * (1 - p) * (1 - p / (3 * k))
        J = V * oD + dl * oC
        N = (1 - dl) * J + dl * oC * V / 2
        return N / J

    def branch_vals(self, b, dl, p):
        f = self.faces[b]
        Bb, Lb, cap, isc = f.B, f.L, f.cap, f.is_cap
        Zb = cap - EPS7
        V = 5 / 6 - dl
        if isc:
            D = 3 - p; A = 2 - 0 * p; C0 = 1 - 2 * p * Zb; Zf = 2 * p * Zb
        else:
            D = 3 - p - 4 * p / Lb; A = 2 - 4 * p / Lb; C0 = 1 - 2 * p * Bb / Lb; Zf = 2 * p * Bb / Lb
        U = (1 - p) * C0
        J = V * D + dl * (1 - p) * A
        N = (1 - dl) * J + V * dl * U
        T = J + dl * U
        RN = A * T + (Zf - p) * J
        MN = D * T - RN
        DJ = D * J
        nm = self.naturalM
        lowerM = (self.mMinus + EPS7) if isc else max(self.mMinus + EPS7, (Bb - Lb * (cap - EPS7)) / 2 + EPS7)
        if isc:
            upperM = min(min(0.44 - EPS7, nm - EPS7), (Bb - Lb * Zb) / 2 - EPS7)
        else:
            upperM = min(min(0.44 - EPS7, nm - EPS7), (Bb - Lb * (self.sMinus + EPS7)) / 2 - EPS7)
        dD = -1.0 if isc else -1 - 4 / Lb
        dA = 0.0 if isc else -4 / Lb
        dC = -2 * Zb if isc else -2 * Bb / Lb
        dU = -C0 + (1 - p) * dC
        dJ = V * dD + dl * (-A + (1 - p) * dA)
        guards = [D, A, C0, J, T - J, 1.2499 * J - T, RN - (23 / 37) * DJ, DJ - RN, MN - lowerM * DJ,
                  upperM * DJ - MN, N - (1 - 2 * dl * nm - 2 * dl * p * self.sMinus) * J,
                  U * dJ - dU * J,
                  (0.44 - nm - EPS7) + 0 * dl,
                  (Bb - 2 * nm - Lb * (self.sMinus + EPS7) - 2 * EPS7) + 0 * dl,
                  ((Zb - self.sMinus - EPS7) * DJ) if isc else (1.0 + 0 * dl)]
        return N / J, guards

    def window_mask(self, w, DL, P):
        b, dlo, dhi, plo = w
        return (DL >= dlo) & (DL <= dhi) & (P >= plo) & (P <= 0.5)

    def envelope(self, DL, P, use_windows=None, pointwise=False, branches=None):
        """min of old count and the counts of windows available at (DL,P).
        pointwise=True: ignore window boxes, use any branch whose 15 guards hold at the point (optimistic)."""
        env = self.old_count(DL, P)
        if pointwise:
            for b in (branches or self.faces.keys()):
                val, g = self.branch_vals(b, DL, P)
                ok = np.ones_like(DL, dtype=bool)
                for gi in g: ok &= (gi > 0)
                env = np.where(ok, np.minimum(env, val), env)
            return env
        for w in (use_windows if use_windows is not None else self.windows):
            val, g = self.branch_vals(w[0], DL, P)
            m = self.window_mask(w, DL, P)
            env = np.where(m, np.minimum(env, val), env)
        return env

    def check_windows(self, n=121):
        """Check that all 15 admission guards are positive on each window (grid); returns min guard value per window"""
        out = []
        for w in self.windows:
            b, dlo, dhi, plo = w
            dls = np.linspace(dlo, dhi, n); ps = np.linspace(plo, 0.5, n)
            DL, P = np.meshgrid(dls, ps, indexing='ij')
            val, g = self.branch_vals(b, DL, P)
            out.append((w, min(float(np.min(gi)) for gi in g), int(np.argmin([float(np.min(gi)) for gi in g]))))
        return out

    def margins(self, nd=1501, npp=1001, **kw):
        dls = np.linspace(0, 0.75, nd); ps = np.linspace(0, 0.5, npp)
        DL, P = np.meshgrid(dls, ps, indexing='ij')
        env = self.envelope(DL, P, **kw)
        res = {}
        for name, (d, C) in self.edges().items():
            E = self.Ebase(d, C, DL, P) + 0.75 * d * env
            slack = self.theta - self.reserve - E
            i = np.unravel_index(np.argmin(slack), slack.shape)
            res[name] = (float(slack[i]), float(DL[i]), float(P[i]))
        return res

    def min_margin(self, **kw):
        r = self.margins(**kw)
        k = min(r, key=lambda e: r[e][0])
        return r[k][0], k, r

def parse_windows(path):
    import re
    txt = open(path).read()
    ws = re.findall(r'def returnWindow(\d+) : ReturnCountWindow where\n\s*branch := \.(\w+)\n.*?deltaLo := \(([^:]+):ℝ\)\n\s*deltaHi := \(([^:]+):ℝ\)\n\s*pLo := \(([^:]+):ℝ\)', txt, re.S)
    from fractions import Fraction as Fr
    return [(b, float(Fr(a)), float(Fr(bb)), float(Fr(cc))) for (_, b, a, bb, cc) in ws]
