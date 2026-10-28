"""Continuum (ODE) scenarios: all floors for one (variant, boot, dfac); exact theta* with role split.
Count candidates: wall + offsets (and the count break-even slope 0.0857 if above the wall); physical candidates
around the physical break-even slope 0.0598 (lemmaW.md s3.1), then local refinement."""
import sys, os, json, time
import numpy as np
from scipy.optimize import brentq
import ode, split, exact
HERE = os.path.dirname(os.path.abspath(__file__))
RES = os.path.join(HERE, 'results'); os.makedirs(RES, exist_ok=True)
SC_BE, SP_BE = 0.0857, 0.0598


def L_at_slope(ch, s, lo=2.0, hi=2.57):
    f = lambda L: ch.slope(L) - s
    try:
        if f(lo) < 0:
            return None
        return brentq(f, lo, hi, xtol=1e-6)
    except ValueError:
        return None


def run_ode(var, boot, dfac, floors=(0.60, 0.55, 0.50), shift_R=0.0, tag='', sigma=None, s0scale=1.0, c6=6.0,
            offs=(0.0, 0.012, 0.03, 0.06), poffs=(-0.06, -0.03, 0.0, 0.03, 0.06), verbose=True, ch=None):
    if ch is None:
        ch = ode.Chain(var, dfac=dfac, boot=boot, shift_R=shift_R, sigma=sigma, s0scale=s0scale, c6=c6)
    LP0 = L_at_slope(ch, SP_BE) or 2.30
    LC_be = L_at_slope(ch, SC_BE)
    out = []
    for fl in floors:
        t0 = time.time()
        wall = ch.wall(fl) + 1e-6
        Lc = [wall + o for o in offs]
        if LC_be is not None and LC_be > wall + offs[-1]:
            Lc.append(LC_be)
        Lp = [LP0 + o for o in poffs]
        faces = [(L, ch.B(L), ch.slope(L)) for L in Lc + Lp]
        c_c = list(range(len(Lc)))
        p_c = list(range(len(Lc), len(faces)))
        res = split.best_split(faces, c_c, p_c, verbose=False)
        LPb, LCb = res['P']['L'], res['C']['L']
        refP = [LPb - 0.015, LPb + 0.015]
        refC = [LCb + d for d in (-0.006, 0.006, 0.018) if LCb + d >= wall - 1e-9]
        faces2 = faces + [(L, ch.B(L), ch.slope(L)) for L in refC + refP]
        c2 = c_c + list(range(len(faces), len(faces) + len(refC)))
        p2 = p_c + list(range(len(faces) + len(refC), len(faces2)))
        res = split.best_split(faces2, c2, p2, verbose=False)
        name = 'ode_%s_f%.2f_b%d_d%.3f%s' % (var, fl, int(boot), dfac, tag)
        res.update(name=name, var=var, floor=fl, boot=boot, dfac=dfac, wall=wall, dL=0)
        json.dump(res, open(os.path.join(RES, 'eval_%s.json' % name), 'w'), indent=1, default=str)
        if verbose:
            print('%-34s theta=%.9f gap=%+.2e  wall %.4f C(L=%.4f,s0=%.4f) P(L=%.3f,s0=%.4f) [%.0fs]' % (
                name, res['theta'], res['theta'] - split.BAR, wall, res['C']['L'], res['C']['s0'], res['P']['L'], res['P']['s0'], time.time() - t0), flush=True)
        out.append(res)
    return out


if __name__ == '__main__':
    var = sys.argv[1]; boot = bool(int(sys.argv[2])); dfac = float(sys.argv[3])
    floors = [float(x) for x in sys.argv[4].split(',')] if len(sys.argv) > 4 else (0.60, 0.55, 0.50)
    run_ode(var, boot, dfac, floors)
