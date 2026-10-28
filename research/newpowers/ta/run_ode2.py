"""Continuum (ODE) scenarios, second generation: Chain2 (exact marked gate) -> role split -> exact return.
    python3 run_ode2.py GAIN BOOT DFAC [floors comma list]
Count candidates: wall + offsets (and the count break-even slope 0.0857 if above the wall); physical candidates around the
physical break-even slope 0.0598, then local refinement (as run_ode.py)."""
import sys, os, json, time
import numpy as np
from scipy.optimize import brentq
import ode2, split, exact

HERE = os.path.dirname(os.path.abspath(__file__))
RES = os.path.join(HERE, 'results')
os.makedirs(RES, exist_ok=True)
SC_BE, SP_BE = 0.0857, 0.0598


def L_at_slope(ch, s, lo=1.95, hi=2.57):
    f = lambda L: ch.slope(L) - s
    try:
        if f(lo) < 0:
            return None
        return brentq(f, lo, hi, xtol=1e-6)
    except ValueError:
        return None


def run_ode(gain, boot, dfac, floors=(0.60, 0.55, 0.50), tag='', ch=None, ret=None, verbose=True, scan_extra=True, **chkw):
    if ch is None:
        ch = ode2.Chain2(gain=gain, dfac=dfac, boot=boot, **chkw)
    ret = dict(ret or {})
    LP0 = L_at_slope(ch, SP_BE) or 2.30
    LC_be = L_at_slope(ch, SC_BE)
    out = []
    for fl in floors:
        t0 = time.time()
        wall = ch.wall(fl) + 1e-6
        offs = (0.0, 0.012, 0.03, 0.06, 0.10, 0.15) if scan_extra else (0.0, 0.012, 0.03, 0.06)
        poffs = (-0.12, -0.09, -0.06, -0.03, 0.0, 0.03, 0.06) if scan_extra else (-0.06, -0.03, 0.0, 0.03, 0.06)
        Lc = [wall + o for o in offs]
        if LC_be is not None and LC_be > wall + offs[-1]:
            Lc.append(LC_be)
        Lp = [max(LP0 + o, wall) for o in poffs]
        Lp = sorted(set(round(x, 6) for x in Lp), reverse=True)
        faces = [(L, ch.B(L), ch.slope(L)) for L in Lc + Lp]
        c_c = list(range(len(Lc)))
        p_c = list(range(len(Lc), len(faces)))
        res = split.best_split(faces, c_c, p_c, P0=p_c[len(p_c) // 2], verbose=False, **ret)
        LPb, LCb = res['P']['L'], res['C']['L']
        refP = [x for x in (LPb - 0.015, LPb + 0.015, LPb - 0.007, LPb + 0.007) if x >= wall]
        refC = [LCb + d for d in (-0.006, 0.006, 0.018, -0.003, 0.003) if LCb + d >= wall - 1e-9]
        faces2 = faces + [(L, ch.B(L), ch.slope(L)) for L in refC + refP]
        c2 = c_c + list(range(len(faces), len(faces) + len(refC)))
        p2 = p_c + list(range(len(faces) + len(refC), len(faces2)))
        res = split.best_split(faces2, c2, p2, P0=p_c[len(p_c) // 2], verbose=False, **ret)
        name = 'ode2_g%g_f%.2f_b%d_d%.3f%s' % (gain, fl, int(boot), dfac, tag)
        res.update(name=name, gain=gain, floor=fl, boot=boot, dfac=dfac, wall=wall, dL=0)
        json.dump(res, open(os.path.join(RES, 'e2_%s.json' % name), 'w'), indent=1, default=str)
        if verbose:
            print('%-40s theta=%.9f gap=%+.2e  wall %.4f C(L=%.4f,s0=%.4f) P(L=%.3f,s0=%.4f) [%.0fs]' % (
                name, res['theta'], res['theta'] - split.BAR, wall, res['C']['L'], res['C']['s0'], res['P']['L'], res['P']['s0'], time.time() - t0), flush=True)
        out.append(res)
    return out


if __name__ == '__main__':
    gain = float(sys.argv[1]); boot = bool(int(sys.argv[2])); dfac = float(sys.argv[3])
    floors = [float(x) for x in sys.argv[4].split(',')] if len(sys.argv) > 4 else (0.60, 0.55, 0.50)
    run_ode(gain, boot, dfac, floors)
