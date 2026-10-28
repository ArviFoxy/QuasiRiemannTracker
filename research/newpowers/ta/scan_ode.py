"""exact theta* on continuum chain faces: count at/near the floor wall (scan), physical scan; role split."""
import sys, time, json
import numpy as np
from ode import Chain
from exact import theta_exact

BAR = 0.8739058


def best_split(ch, floor, dLC=(0.0, 0.01, 0.03, 0.06, 0.10), LPs=(2.42, 2.40, 2.38, 2.36, 2.34, 2.32),
               LP0=2.38, verbose=True, unit=10**9, **kw):
    wall = ch.wall(floor) + 1e-6
    Bp0 = ch.B(LP0)
    res = []
    bestC = None
    for d in dLC:
        L = wall + d
        r = theta_exact(ch.B(L), L, Bp0, LP0, unit=unit, **kw)
        t = None if r is None else r[0]
        res.append(('C', L, t))
        if verbose:
            print('   count L=%.4f B=%.6f s0=%.4f -> theta %s' % (L, ch.B(L), ch.slope(L), t), flush=True)
        if t is not None and (bestC is None or t < bestC[0]):
            bestC = (t, L)
    Lc = bestC[1]
    bestP = None
    for LP in LPs:
        r = theta_exact(ch.B(Lc), Lc, ch.B(LP), LP, unit=unit, **kw)
        t = None if r is None else r[0]
        if verbose:
            print('   phys  L=%.4f B=%.6f s0=%.4f -> theta %s' % (LP, ch.B(LP), ch.slope(LP), t), flush=True)
        if t is not None and (bestP is None or t < bestP[0]):
            bestP = (t, LP)
    return bestP[0], Lc, bestP[1], wall


if __name__ == '__main__':
    var = sys.argv[1]; floor = float(sys.argv[2])
    dfac = float(sys.argv[3]) if len(sys.argv) > 3 else 0.999
    boot = bool(int(sys.argv[4])) if len(sys.argv) > 4 else False
    ch = Chain(var, dfac=dfac, boot=boot)
    t0 = time.time()
    t, Lc, Lp, wall = best_split(ch, floor)
    print('%s floor %.2f dfac %.3f boot %d: wall %.4f best theta %.9f (C at %.4f, P at %.2f) gap %+.2e  [%.0fs]' %
          (var, floor, dfac, boot, wall, t, Lc, Lp, t - BAR, time.time() - t0))
