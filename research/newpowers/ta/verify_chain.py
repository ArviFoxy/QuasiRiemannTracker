"""Re-check a generated chain on much finer grids (v: 600 cubic points, nu: 9 points of [q,3/4], x: 0..1/2 step 0.025 plus
class grid) and report the s0 shortfall per step (what a finer-grid greedy step would have to add)."""
import sys, json
import numpy as np
import chain


def fine_cfg(cfg):
    c = chain.Cfg(var=cfg.var, floor=cfg.floor, dfac=cfg.dfac, boot=cfg.boot, dL=cfg.dL, eps=cfg.eps, N=600,
                  xs=np.concatenate([np.arange(0, 0.5, 0.025), [0.475, 0.4875, 0.5]]),
                  nuf=np.array([0, 0.03, 0.08, 0.15, 0.25, 0.4, 0.55, 0.7, 0.85, 1.0]), shift_R=cfg.shift_R, sigma=cfg.sigma)
    return c


def verify(rows, cfg):
    fc = fine_cfg(cfg)
    short = []
    worst = []
    for r in rows:
        if r.get('infeasible'):
            continue
        B0, L0, c0, s0, A, D = r['B0'], r['L0'], r['c0'], r['s0'], r['A'], r['D']
        w, bk, m = chain.worst(fc, B0, L0, c0, s0, A, D)
        if w >= 0:
            short.append(0.0)
            worst.append((w, bk))
            continue
        # least s0' >= s0 feasible on the fine grid
        lo, hi = s0, min(s0 + 0.01, fc.cchild - 1e-4)
        if chain.worst(fc, B0, L0, c0, hi, A, D)[0] < 0:
            short.append(float('nan')); worst.append((w, bk)); continue
        for _ in range(40):
            mid = 0.5 * (lo + hi)
            if chain.worst(fc, B0, L0, c0, mid, A, D)[0] >= 0:
                hi = mid
            else:
                lo = mid
        short.append(hi - s0)
        worst.append((w, bk))
    return np.array(short), worst


if __name__ == '__main__':
    fn = sys.argv[1]
    var, floor, dfac, boot, dL = sys.argv[2], float(sys.argv[3]), float(sys.argv[4]), bool(int(sys.argv[5])), float(sys.argv[6])
    rows = json.load(open(fn))
    cfg = chain.Cfg(var=var, floor=floor, dfac=dfac, boot=boot, dL=dL)
    short, worst = verify(rows, cfg)
    print('steps', len(short), 'max shortfall s0: %.2e   sum shortfall*dL (cumulative loss in B if unrepaired): %.2e' % (np.nanmax(short), np.nansum(short) * dL))
    bad = [(i, s, w[1]) for i, (s, w) in enumerate(zip(short, worst)) if s > 1e-7]
    print('steps with shortfall > 1e-7:', bad[:10])
