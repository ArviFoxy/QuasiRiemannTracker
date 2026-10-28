"""Re-check a generated chain (chain2 rows) on much finer settings and report per-gate reserves.
    fine settings: v-grid N = 600 (cubic spacing), nu 'range' mode (6 values of [q, 3/4]), p-search (129, 65, 4).
    python3 verify2.py CHAIN.json GAIN FLOOR BOOT DFAC [dL]
Outputs: s0 shortfall per step (least s0' >= s0 feasible on the fine settings, same A, D), the gate that is binding at each step
(argmin of x - eps), the minimum reserve (x - eps) of every gate over the chain, and the steps that bind each gate."""
import sys, json
import numpy as np
import chain2 as C2

GATES = C2.GATES


def fine_cfg(cfg):
    return C2.Cfg(gain=cfg.gain, floor=cfg.floor, dfac=cfg.dfac, boot=cfg.boot, dL=cfg.dL, eps=cfg.eps, N=600,
                  nu_mode='range', K=cfg.K, pl=(129, 65, 4), shift=cfg.shift)


def gate_table(rows, cfg):
    """per step: margins x - eps of every gate (scale-free ones raw)"""
    out = []
    for r in rows:
        if r.get('infeasible'):
            continue
        m, _ = C2.gmin(cfg, r['B0'], r['L0'], r['c0'], r['s0'], r['A'], r['D'])
        out.append({k: (v if k in C2.SCALEFREE else v - cfg.eps) for k, v in m.items() if not k.startswith('_')})
    return out


def verify(rows, cfg):
    fc = fine_cfg(cfg)
    short, bind = [], []
    for r in rows:
        if r.get('infeasible'):
            continue
        B0, L0, c0, s0, A, D = r['B0'], r['L0'], r['c0'], r['s0'], r['A'], r['D']
        w, bk, m = C2.worst(fc, B0, L0, c0, s0, A, D)
        bind.append(bk)
        if w >= -1e-9:
            short.append(0.0)
            continue
        lo, hi = s0, min(s0 + 0.01, fc.cchild - 1e-4)
        if C2.worst(fc, B0, L0, c0, hi, A, D)[0] < 0:
            short.append(float('nan'))
            continue
        for _ in range(40):
            mid = 0.5 * (lo + hi)
            if C2.worst(fc, B0, L0, c0, mid, A, D)[0] >= 0:
                hi = mid
            else:
                lo = mid
        short.append(hi - s0)
    return np.array(short), bind


def summary(rows, cfg, verbose=True):
    short, bind = verify(rows, cfg)
    tab = gate_table(rows, cfg)
    mins = {g: min(t[g] for t in tab) for g in GATES if g not in ('low',) or cfg.dfac < 1}
    where = {g: int(np.argmin([t[g] for t in tab])) + 1 for g in mins}
    cnt = {}
    for b in bind:
        cnt[b] = cnt.get(b, 0) + 1
    res = dict(max_shortfall=float(np.nanmax(short)), sum_shortfall_dL=float(np.nansum(short) * cfg.dL),
               nbad=int(np.sum(short > 1e-7)), min_reserve=mins, min_at_step=where, binding_counts=cnt)
    if verbose:
        print('steps', len(short), 'max s0 shortfall (fine settings) %.2e  sum*dL %.2e  steps>1e-7: %d' % (
            res['max_shortfall'], res['sum_shortfall_dL'], res['nbad']))
        print('binding gate counts (fine settings):', cnt)
        print('min reserve per gate over chain (x - eps; scale-free raw):')
        for g in mins:
            print('   %-15s %.3e at step %d' % (g, mins[g], where[g]))
    return res


if __name__ == '__main__':
    fn = sys.argv[1]
    gain, floor, boot, dfac = float(sys.argv[2]), float(sys.argv[3]), bool(int(sys.argv[4])), float(sys.argv[5])
    dL = float(sys.argv[6]) if len(sys.argv) > 6 else 0.005
    rows = json.load(open(fn))
    cfg = C2.Cfg(gain=gain, floor=floor, boot=boot, dfac=dfac, dL=dL)
    summary(rows, cfg)
