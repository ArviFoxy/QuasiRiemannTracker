"""Second generation scenario runner: marked-gate chain (chain2.py, exact K = 8 gain) -> role split -> exact return.

    python3 run2.py GAIN FLOOR BOOT DFAC [dL] [tag]       one scenario, writes logs/c2_*.json and results/e2_*.json
Return = PR 86 `Return` constants/edges, transport box with `ell < 0.171` dropped (ell < 0.18), six branches
(old, C, Ccap, C-7, P, Pcap: PR 76 FinalReturn), Collet windows (PR 83/86 constants); `windows='lemmaW'` is the check.
"""
import sys, os, json, time
import numpy as np
import chain2 as C2
import exact

HERE = os.path.dirname(os.path.abspath(__file__))
RES = os.path.join(HERE, 'results')
LOGS = os.path.join(HERE, 'logs')
BAR = 0.8739058
RECORD = 0.8739558


def faces_of(rows):
    return [(r['L'], r['B'], r['s0']) for r in rows if not r.get('infeasible')]


def th(faces, iC, iP, guess, unit=10**9, span=400, **kw):
    r = exact.theta_exact(faces[iC][1], faces[iC][0], faces[iP][1], faces[iP][0], guess=guess, unit=unit,
                          span=span if unit == 10**9 else 300, **kw)
    return None if r is None else r


def split_search(faces, kw, c_cands=None, p_cands=None, verbose=False, guess=0.8739):
    n = len(faces)
    if p_cands is None:
        p_all = [i for i, f in enumerate(faces) if 2.10 <= f[0] <= 2.50]
        p_cands = p_all[::max(1, len(p_all) // 12)]
    if c_cands is None:
        c_cands = sorted(set(list(range(max(0, n - 12), n)) + list(range(max(0, n - 80), n, 6))
                             + [i for i, f in enumerate(faces) if 0.078 <= f[2] <= 0.095][::3]))
    P0 = min(p_cands, key=lambda i: abs(faces[i][0] - 2.30))
    log = []
    bestC = None
    g = guess
    for i in c_cands:
        r = th(faces, i, P0, g, unit=10**8, **kw)
        log.append(('C', i, faces[i][0], r and r[0]))
        if verbose:
            print('  C', i, faces[i][0], r and r[0], flush=True)
        if r is not None:
            g = r[0]
            if bestC is None or r[0] < bestC[0]:
                bestC = (r[0], i)
    iC = bestC[1]
    bestP = None
    g = bestC[0]
    for j in p_cands:
        r = th(faces, iC, j, g, unit=10**8, **kw)
        log.append(('P', j, faces[j][0], r and r[0]))
        if verbose:
            print('  P', j, faces[j][0], r and r[0], flush=True)
        if r is not None:
            g = r[0]
            if bestP is None or r[0] < bestP[0]:
                bestP = (r[0], j)
    iP = bestP[1]
    # joint local refinement at 1e-9
    best = None
    for a in range(iC - 3, iC + 4):
        for b in range(iP - 3, iP + 4):
            if 0 <= a < n and 0 <= b < n and abs(a - iC) + abs(b - iP) <= 3:
                r = th(faces, a, b, bestP[0], unit=10**9, **kw)
                if r is not None and (best is None or r[0] < best[0]):
                    best = (r[0], a, b, r)
    return best, log


def run_scenario(gain, floor, boot, dfac, dL=0.005, tag='', nu_mode='q', K=8, ret=None, verbose=False, shift=0.0, eps=1e-6):
    cfg = C2.Cfg(gain=gain, floor=floor, boot=bool(boot), dfac=dfac, dL=dL, nu_mode=nu_mode, K=K, shift=shift, eps=eps)
    name = cfg.name() + tag
    fn = os.path.join(LOGS, 'c2_%s.json' % name)
    t0 = time.time()
    if os.path.exists(fn):
        rows = json.load(open(fn))
    else:
        rows = C2.run(cfg, out=fn, verbose=False)
    t1 = time.time()
    faces = faces_of(rows)
    kw = dict(ret or {})
    best, log = split_search(faces, kw, verbose=verbose)
    th_, iC, iP, r = best
    res = dict(name=name, gain=gain, floor=floor, boot=boot, dfac=dfac, dL=dL, nu_mode=nu_mode, K=K, theta=th_,
               h=float(r[1]), theta_units=r[2], nsteps=len(faces),
               C=dict(idx=iC, L=faces[iC][0], B=faces[iC][1], s0=faces[iC][2]),
               P=dict(idx=iP, L=faces[iP][0], B=faces[iP][1], s0=faces[iP][2]),
               end=dict(L=faces[-1][0], B=faces[-1][1]),
               last_bind=[x.get('bind') for x in rows if not x.get('infeasible')][-1],
               infeasible=bool(rows and rows[-1].get('infeasible')), ret=kw, log=log,
               t_chain=t1 - t0, t_ret=time.time() - t1)
    json.dump(res, open(os.path.join(RES, 'e2_%s.json' % name), 'w'), indent=1, default=str)
    return res


if __name__ == '__main__':
    gain, floor, boot, dfac = float(sys.argv[1]), float(sys.argv[2]), int(sys.argv[3]), float(sys.argv[4])
    dL = float(sys.argv[5]) if len(sys.argv) > 5 else 0.005
    tag = sys.argv[6] if len(sys.argv) > 6 else ''
    r = run_scenario(gain, floor, boot, dfac, dL, tag)
    print('%-44s theta=%.9f gap=%+.2e  C(L=%.4f,s0=%.4f,%d/%d) P(L=%.3f) [chain %.0fs, return %.0fs]' % (
        r['name'], r['theta'], r['theta'] - BAR, r['C']['L'], r['C']['s0'], r['C']['idx'], r['nsteps'], r['P']['L'],
        r['t_chain'], r['t_ret']), flush=True)
