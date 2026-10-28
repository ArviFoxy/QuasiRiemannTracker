"""pricing2.py -- coordinate-descent role-split pricing of a continuum chain with the exact return (R2).

Fixes the weak point of price_amp.price_parallel (separable line scans taken at a mid-grid reference face):
here the count face L_C and the physical face L_P are optimised alternately with the OTHER face at its current best,
with shrinking steps; every theta is the exact-cover Lean-return value of B2/tc (via price_amp.theta).
"""
import sys, os
from concurrent.futures import ProcessPoolExecutor
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import price_amp as PA  # noqa: E402

BAR = PA.BAR


def _ev(args):
    return PA.theta(*args)


def _pmap(jobs, workers=4):
    with ProcessPoolExecutor(workers) as ex:
        return list(ex.map(_ev, jobs))


def price_cd(ode, floor=0.60, Lmin=2.0, Lmax_c=2.50, workers=4, Lp0=2.38, verbose=False):
    wall = ode.wall(floor)
    Lend = max(Lmin, wall if wall is not None else Lmin)
    B = ode.B

    def th(Lc, Lp):
        return PA.theta(B(Lc), Lc, B(Lp), Lp)

    # stage 1: coarse count-face scan with physical face at Lp0
    nC = 9
    Lcs = sorted(set(round(Lend + i * (min(Lmax_c, Lend + 0.30) - Lend) / (nC - 1), 5) for i in range(nC)))
    vals = _pmap([(B(Lc), Lc, B(Lp0), Lp0) for Lc in Lcs], workers)
    cand = [(v, Lc) for v, Lc in zip(vals, Lcs) if v is not None]
    if not cand:
        return wall, None
    Lc = min(cand)[1]
    Lp = Lp0
    best = min(cand)[0]
    # stage 2: alternate with shrinking steps
    for step in (0.04, 0.02, 0.01, 0.005, 0.0025):
        improved = True
        rounds = 0
        while improved and rounds < 4:
            improved = False; rounds += 1
            # physical face
            cands = [Lp + k * step for k in (-2, -1, 1, 2) if 2.0 <= Lp + k * step <= 2.7]
            vals = _pmap([(B(Lc), Lc, B(x), x) for x in cands], workers)
            for v, x in zip(vals, cands):
                if v is not None and v < best - 1e-12:
                    best, Lp, improved = v, x, True
            # count face (only moves inside [Lend, Lmax_c])
            cands = [Lc + k * step for k in (-2, -1, 1, 2) if Lend - 1e-9 <= Lc + k * step <= Lmax_c]
            cands = [max(Lend, x) for x in cands]
            vals = _pmap([(B(x), x, B(Lp), Lp) for x in cands], workers)
            for v, x in zip(vals, cands):
                if v is not None and v < best - 1e-12:
                    best, Lc, improved = v, x, True
            if verbose:
                print('   step %.4f  Lc=%.4f Lp=%.4f theta=%.9f' % (step, Lc, Lp, best), flush=True)
    return wall, dict(theta=best, Lc=Lc, Lp=Lp, Bc=B(Lc), Bp=B(Lp), gap=best - BAR)
