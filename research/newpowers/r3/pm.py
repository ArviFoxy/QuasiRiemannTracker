"""Pointwise model (PM) of the PR 86 / Lemma-W final return at its binding edge (newTop, d = h, C branch, p = 1/2).

R3 (new powers in the final return).  Pure Python + scipy, no lake/lean.

What it is.  The exact toolchain (tc/pr86.py, tc/best.py: exact Bernstein cover, Fractions) certifies
        J (theta - r0 - Ebase) - 3/4 d N  >  0      on every edge and every branch.
At the binding point this is  Ebase(d=h, C, delta, p) + 3/4 h R(delta,p) = theta - r0  with R = N/J the count exponent of
the affine count branch C.  PM evaluates that scalar inequality directly, with the count R written from the three lines
        I(r)  = 1 - delta r - 2 delta p z,  z = (1 - r + e_I)/c_I                    (marked inverse, Lemma 17.1)
        P(m)  = 1 - 2 delta m - 2 delta p z,  z = (B - 2 m)/Lam                      (marked plain, face (B, Lam))
        L(t)  = 1 - delta + (k_L - delta)(t - 1) - sigma_L(t)                         (no-slot inverse, sixth powers)
crossed at the optimal cutoff t.  Calibration (calib.py): PM reproduces the exact theta* of the toolchain to <= 1e-9 on the
two reference scenarios and the exact prices of all levers of lemmaW.md s4.3 to <= 4e-9 (levers up to 2e-4).
PM is NOT valid once another edge/branch binds (e.g. 'Cfull': the old-branch edges bind at ~0.87364).
"""
import json, math, os
from fractions import Fraction as Fr
from scipy.optimize import brentq, minimize_scalar

HERE = os.path.dirname(os.path.abspath(__file__))
BAR = 0.8739358                      # coordinator's target (1e-5 below the 0.8739458 milestone)


def _load_faces():
    chain = json.load(open(os.path.join(HERE, 'tc', 'chain86.json')))
    ext = {}
    for l in open(os.path.join(HERE, 'tc', 'greedy_f060_dl005.jsonl')):
        r = json.loads(l)
        if not r.get('infeasible'):
            ext[r['k']] = (r['B'], r['L'])

    def face(k):
        if k <= 46:
            return float(Fr(chain[k]['B'])), float(Fr(chain[k]['L']))
        return ext[k]
    return face


face = _load_faces()


class Model:
    """Return at newTop.  Levers (all default to the PR 86 / Lean values):
       kL   long-line slope numerator (5/6)            cI   inverse slot cost (2)
       dE   additive change of the return exponent     dR   count lowered by dR
       dC   capacity added at the new edges            eps_half  selected slots save (1/2+eps)*delta p C
       eE   probe column excess: x+y = 1 - ell + eE   eI   inverse column excess: r + c_I z <= 1 + eI
       sP   constant shift of the plain line           sL   constant shift of the long line
       wL   supply-limited fourth-power width in the long moment (units of log U)
    """

    def __init__(self, BC, LC, BP, LP, sP=0.06, reserve=1e-8, hu=0.806):
        self.BC, self.LC, self.BP, self.LP, self.sPnum, self.reserve, self.hu = BC, LC, BP, LP, sP, reserve, hu
        self.kL = 5 / 6; self.cI = 2.0
        self.dE = 0.0; self.dR = 0.0; self.dC = 0.0; self.eps_half = 0.0
        self.eE = 0.0; self.eI = 0.0; self.sPl = 0.0; self.sL = 0.0; self.wL = 0.0
        self.free_h = False; self.use_floor = True

    # ------------------------------------------------------------------ geometry (Lean: Geometry.lean, TransportGeometry.lean)
    def geom(self, th, h):
        ell = 11 / 3 - 4 * th + self.eE / 3          # theta = 11/12 - ell/4 + eE/12   (x + y = 1 - ell + eE)
        x = 1 + ell - h                               # row_endpoint
        y = h - 2 * ell + self.eE                     # = 1 - ell + eE - x
        return ell, x, y

    def cap(self, th, h):
        ell, x, y = self.geom(th, h)
        return min(self.sPnum * h, (2 * y - (2 - self.BP) * h) / self.LP) + self.dC

    def hfloor(self, th):
        """largest h with BoundsN.floor_margin >= 0 (linear in h)."""
        def fm(h):
            ell, x, y = self.geom(th, h)
            dP = h + 1e-10
            signal = x / 2 + (y - x) / 12
            return signal - 1 / 200 - (4 / 25 * x - 3 / 20 - 51 / 100 * y + 67 / 100 * dP - 3 / 20 * ell)
        f0, f1 = fm(0.0), fm(1.0)
        return -f0 / (f1 - f0)

    # ------------------------------------------------------------------ count exponent R(delta, p)
    def _lines(self, delta, p, B, Lam):
        cI = self.cI
        a = self.kL - delta
        bI = delta * (1 - 2 * p / cI)
        aI = 1 - 2 * delta * p / cI * (1 + self.eI)
        bP = delta * (2 - 4 * p / Lam)
        aP = 1 - 2 * delta * p * B / Lam - self.sPl
        return a, aI, bI, aP, bP

    def R(self, delta, p, B=None, Lam=None):
        B = self.BC if B is None else B
        Lam = self.LC if Lam is None else Lam
        a, aI, bI, aP, bP = self._lines(delta, p, B, Lam)
        b = bI * bP / (bI + bP)
        S0 = (aI * bP + aP * bI) / (bI + bP)
        lam0 = 1 - self.kL - self.sL
        if self.wL == 0.0:
            t = (S0 - lam0) / (a + b)
            R = lam0 + a * t
        else:       # long line with supply-limited fourth-power width: shift min(wL/3, (t-1)/12)
            def g(t):
                return (S0 - b * t) - (lam0 + a * t - min(self.wL / 3, max(t - 1, 0) / 12))
            t = brentq(g, 0.5, 2.0, xtol=1e-14)
            R = S0 - b * t
        return R - self.dR

    # ------------------------------------------------------------------ return exponent and theta*
    def E(self, th, h, delta, p):
        ell, x, y = self.geom(th, h)
        C = self.cap(th, h)
        half = 0.5 + self.eps_half
        return 0.5 + 13 * h / 75 - y / 2 - ell / 2 - 9 * h / 100 + delta / 2 + delta * p * (ell - half * C) + self.dE

    def F(self, th, h, delta, p=0.5):
        return self.E(th, h, delta, p) + 0.75 * h * self.R(delta, p)

    def fmax(self, th, h, p=0.5):
        r = minimize_scalar(lambda d: -self.F(th, h, d, p), bounds=(0.30, 0.60), method='bounded',
                            options=dict(xatol=1e-12))
        return -r.fun, r.x

    def pick_h(self, th):
        if self.free_h:
            return 0.8054
        hf = min(self.hfloor(th) if self.use_floor else self.hu, self.hu - 1e-6)
        return math.floor(hf * 1e6) / 1e6

    def theta_star(self, lo=0.860, hi=0.8750):
        def g(th):
            return self.fmax(th, self.pick_h(th))[0] - (th - self.reserve)
        return brentq(g, lo, hi, xtol=1e-13)

    def binding(self, th=None):
        th = self.theta_star() if th is None else th
        h = self.pick_h(th)
        v, d = self.fmax(th, h)
        a, aI, bI, aP, bP = self._lines(d, 0.5, self.BC, self.LC)
        return dict(theta=th, h=h, delta=d, R=self.R(d, 0.5), C=self.cap(th, h))


def scenario(name, **kw):
    """A = lowered floor 0.60, count step 73 / physical step 38 (gap 1.05e-5);  B = PR 86 chain, count 46 / physical 38."""
    kc, kp = {'A': (73, 38), 'B': (46, 38)}[name]
    fc, fp = face(kc), face(kp)
    m = Model(fc[0], fc[1], fp[0], fp[1])
    for k, v in kw.items():
        setattr(m, k, v)
    return m


def needed(name, lever, lo, hi, target=BAR, **fixed):
    """value of `lever` (attribute of Model) that brings theta* exactly to `target` (monotone root find)."""
    def g(v):
        m = scenario(name, **fixed)
        setattr(m, lever, v)
        return m.theta_star() - target
    return brentq(g, lo, hi, xtol=1e-12)


if __name__ == '__main__':
    for s in 'AB':
        m = scenario(s)
        print(s, 'theta* = %.9f' % m.theta_star(), m.binding())
