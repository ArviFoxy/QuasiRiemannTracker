"""twisted_ode.py -- price the D^1 cubic j=0 twisted transfer (e,c,r) = (0, 2+kappa, 1) on the current record model
(TA's floor-1/2 marked chain, continuum limit, exact six-branch return, role split).

Model (R2 s5.1 mixture law, continuum dL -> 0):
  LOW payment per unit selected width:  simple pi_s(q) = 1 + q - 6 q beta,  twisted pi_t(q) = q (1 - (2+kappa) beta) - kroom
  (beta = B/L).  The LOW density is the largest q <= 3/4 for which SOME type has pi > 0 (the mass of the best type is not
  binding as dL -> 0).  => q = 3/4 while the twisted type pays, else the simple q_inf = dfac*L/(6B - L).
  kappa = scale-type conductor charge (R2's convention, c -> 2 + kappa); kroom = room-type charge (e -> -kroom).
The slope s0(B, L) is TA's marked HIGH gate at v = 0 (ode2.s0_inst) with nu in [q, 3/4]; u-terms vanish in the limit.
Usage: python3 twisted_ode.py KAPPA KROOM [floor]
"""
import sys, os, json, time
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, 'ta'))
import numpy as np
from scipy.integrate import solve_ivp
from scipy.optimize import brentq
import ode2, split

DFAC = 0.999


class TwistedChain:
    def __init__(self, kappa=0.0, kroom=0.0, gain=1.0, boot=False, Lend=1.80, rtol=1e-10, twisted=True):
        self.kappa, self.kroom, self.gain, self.twisted = kappa, kroom, gain, twisted
        B0, L0 = ode2.BOOT[boot]
        self.B0, self.L0 = B0, L0
        segs = []
        # phase 1: twisted type pays (q = 3/4); terminal event when it stops paying
        if self.twisted and self.tw_pays(B0, L0):
            ev = lambda L, y: self.tw_margin(y[0], L)
            ev.terminal, ev.direction = True, 0
            s1 = solve_ivp(lambda L, y: [self._s0(y[0], L, 0.75)], [L0, Lend], [B0], method='DOP853', rtol=rtol,
                           atol=1e-13, dense_output=True, events=[ev])
            segs.append(s1)
            Lsw, Bsw = float(s1.t[-1]), float(s1.y[0, -1])
        else:
            Lsw, Bsw = L0, B0
        self.Lsw, self.Bsw = Lsw, Bsw
        # phase 2: simple type
        dead = lambda L, y: self.q_simple(y[0], L) - 0.4
        dead.terminal = True
        if Lsw > Lend + 1e-6:
            s2 = solve_ivp(lambda L, y: [self._s0(y[0], L, min(0.75, self.q_simple(y[0], L)))], [Lsw, Lend], [Bsw],
                           method='DOP853', rtol=rtol, atol=1e-13, dense_output=True, events=[dead])
            segs.append(s2)
        self.segs = segs
        self.Lmin = float(segs[-1].t[-1])

    # LOW payments
    def tw_margin(self, B, L):
        beta = B / L
        return 0.75 * (1.0 - (2.0 + self.kappa) * beta) - self.kroom

    def tw_pays(self, B, L):
        return self.tw_margin(B, L) > 0

    def q_simple(self, B, L):
        return DFAC * L / (6.0 * B - L)

    def q(self, B, L):
        if self.twisted and self.tw_pays(B, L):
            return 0.75
        return min(0.75, self.q_simple(B, L))

    def _s0(self, B, L, q):
        return ode2.s0_inst(B, L, q, 0.1, self.gain, 8, 0.0, 'range')

    def B(self, L):
        for s in self.segs:
            lo, hi = min(s.t[0], s.t[-1]), max(s.t[0], s.t[-1])
            if lo - 1e-12 <= L <= hi + 1e-12:
                return float(s.sol(L)[0])
        raise ValueError('L out of range %g' % L)

    def slope(self, L):
        B = self.B(L)
        return self._s0(B, L, self.q(B, L))

    def qinf(self, L):
        return self.q(self.B(L), L)

    def wall(self, floor):
        """largest L where the LOW density first drops below the floor (scan downward from the boot face)."""
        Ls = np.linspace(self.L0 - 1e-9, self.Lmin + 1e-9, 4000)
        prev = Ls[0]
        for L in Ls[1:]:
            if self.qinf(L) < floor:
                try:
                    return brentq(lambda x: self.qinf(x) - floor, L, prev, xtol=1e-12)
                except ValueError:
                    return prev
            prev = L
        return self.Lmin


def price(kappa, kroom, floor=0.5, verbose=True):
    t0 = time.time()
    ch = TwistedChain(kappa=kappa, kroom=kroom)
    wall = ch.wall(floor) + 1e-6
    # count candidates: wall and above; physical candidates: a broad scan (the slope may stay below 0.0598)
    Lc = [wall + o for o in (0.0, 0.006, 0.012, 0.03, 0.06, 0.10)]
    Lp = sorted(set(round(min(max(x, wall), ch.L0 - 1e-6), 6) for x in
                    np.concatenate([np.arange(wall, 2.50, 0.04), [2.2478, ch.Lsw, ch.Lsw + 0.01]])), reverse=True)
    faces = [(L, ch.B(L), ch.slope(L)) for L in Lc + Lp]
    c_c = list(range(len(Lc)))
    p_c = list(range(len(Lc), len(faces)))
    res = split.best_split(faces, c_c, p_c, P0=p_c[len(p_c) // 2], verbose=False)
    # local refinement around the best pair
    LPb, LCb = res['P']['L'], res['C']['L']
    refP = [x for x in (LPb - 0.02, LPb + 0.02, LPb - 0.01, LPb + 0.01, LPb - 0.005, LPb + 0.005) if wall <= x < ch.L0]
    refC = [LCb + d for d in (-0.006, 0.006, 0.018, -0.003, 0.003) if LCb + d >= wall - 1e-9]
    faces2 = faces + [(L, ch.B(L), ch.slope(L)) for L in refC + refP]
    c2 = c_c + list(range(len(faces), len(faces) + len(refC)))
    p2 = p_c + list(range(len(faces) + len(refC), len(faces2)))
    res = split.best_split(faces2, c2, p2, P0=p_c[len(p_c) // 2], verbose=False)
    out = dict(kappa=kappa, kroom=kroom, floor=floor, theta=res['theta'], C=res['C'], P=res['P'], wall=wall,
               Lswitch=ch.Lsw, Bswitch=ch.Bsw, Lmin=ch.Lmin, secs=time.time() - t0,
               profile=[(L, ch.B(L), ch.slope(L), ch.qinf(L)) for L in np.linspace(ch.L0 - 1e-6, wall, 12)])
    if verbose:
        print(json.dumps({k: v for k, v in out.items() if k != 'profile'}, default=str))
        for row in out['profile']:
            print('   L=%.4f B=%.6f s0=%.5f q=%.3f' % row)
    return out


if __name__ == '__main__':
    kappa = float(sys.argv[1]); kroom = float(sys.argv[2])
    floor = float(sys.argv[3]) if len(sys.argv) > 3 else 0.5
    o = price(kappa, kroom, floor)
    fn = os.path.join(HERE, 'out_k%.3f_r%.3f_f%.2f.json' % (kappa, kroom, floor))
    json.dump(o, open(fn, 'w'), indent=1, default=str)
