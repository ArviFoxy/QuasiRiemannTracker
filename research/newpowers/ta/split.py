"""Role split on a list of chain faces [(L, B, s0), ...] (sorted by decreasing L): count face = scan of the last faces
(or a given candidate list), physical face = scan of faces with L in [Lp_lo, Lp_hi]; exact theta* (exact.py).
theta*(C,P) = f(C) + g(P) to ~2e-9 (lemmaW.md), so the scans are done one after the other."""
import sys, time, json
import numpy as np
import exact

BAR = 0.8739058
RECORD = 0.8739558


def best_split(faces, c_cands, p_cands, guess=0.87390, P0=None, unit=10**8, verbose=True, refine=False, refine_range=None, **kw):
    """faces: list of (L,B,s0). c_cands / p_cands: indices into faces. returns dict."""
    log = []
    if P0 is None:
        P0 = min(p_cands, key=lambda i: abs(faces[i][0] - 2.38))
    LP0, BP0 = faces[P0][0], faces[P0][1]
    bestC = None
    g = guess
    for i in c_cands:
        L, B, s0 = faces[i]
        r = exact.theta_exact(B, L, BP0, LP0, guess=g, unit=unit, span=300 if unit == 10**8 else 2000, **kw)
        t = None if r is None else r[0]
        log.append(('C', i, L, B, s0, t))
        if verbose:
            print('   C idx %3d L=%.4f B=%.6f s0=%.5f -> %s' % (i, L, B, s0, t), flush=True)
        if t is not None:
            g = t
            if bestC is None or t < bestC[0]:
                bestC = (t, i)
    # refine: neighbours (+-1..3 indices) of the best count candidate
    if refine:
        done = set(c_cands)
        for j in range(bestC[1] - 3, bestC[1] + 4):
            if 0 <= j < len(faces) and j not in done and j in refine_range:
                L, B, s0 = faces[j]
                r = exact.theta_exact(B, L, BP0, LP0, guess=bestC[0], unit=unit, span=300 if unit == 10**8 else 2000, **kw)
                t = None if r is None else r[0]
                log.append(('C', j, L, B, s0, t))
                if t is not None and t < bestC[0]:
                    bestC = (t, j)
    iC = bestC[1]
    LC, BC = faces[iC][0], faces[iC][1]
    bestP = None
    g = bestC[0]
    for j in p_cands:
        L, B, s0 = faces[j]
        r = exact.theta_exact(BC, LC, B, L, guess=g, unit=unit, span=300 if unit == 10**8 else 2000, **kw)
        t = None if r is None else r[0]
        log.append(('P', j, L, B, s0, t))
        if verbose:
            print('   P idx %3d L=%.4f B=%.6f s0=%.5f -> %s' % (j, L, B, s0, t), flush=True)
        if t is not None:
            g = t
            if bestP is None or t < bestP[0]:
                bestP = (t, j)
    jP = bestP[1]
    # final at 1e-9
    LP, BP = faces[jP][0], faces[jP][1]
    r = exact.theta_exact(BC, LC, BP, LP, guess=bestP[0], unit=10**9, span=400, **kw)
    return dict(theta=r[0], h=float(r[1]), theta_units=r[2], C=dict(idx=iC, L=LC, B=BC, s0=faces[iC][2]),
                P=dict(idx=jP, L=LP, B=BP, s0=faces[jP][2]), log=log)


def chain_faces(rows):
    return [(r['L'], r['B'], r['s0']) for r in rows if not r.get('infeasible')]
