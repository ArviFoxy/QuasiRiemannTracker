"""Return-side binding diagnostics for a stored scenario (results/e2_*.json):
   - theta*, h, ell = 11/3 - 4 theta*, y, all BoundsN margins at theta* (`ell_needed` = the least ell-box numeral: ell < ell_needed)
   - the failing edge / box / best admitted branch at theta* - 1e-9 (exact.diagnose)
   - at theta*: number of Bernstein leaves per edge and per branch, and the tightest leaf of every edge (smallest Bernstein minimum)
usage: python3 diag2.py RESULT.json [windows]"""
import sys, os, json
from fractions import Fraction as Fr
from collections import Counter
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, 'tc'))
sys.path.insert(0, HERE)
import pr86, best
import cert_return as CR
import gen_return_lean as GR
import exact


def cover_stats(BC, LC, BP, LP, th_units, unit=10**9, **kw):
    cfg = exact.make_cfg(BC, LC, BP, LP, **kw)
    th = Fr(th_units, unit)
    h = best.h_for(th, cfg.bounds[1])
    c = cfg.copy(th=th, h=h)
    pr86.apply_globals(c)
    G = pr86.geometry(c)
    cands = pr86.candidate_list(c, G)
    out = {}
    for nm, d, C in pr86.edge_list(c, G):
        tree = GR.cover_tree(G, d, C, cands, maxdepth=c.maxdepth)
        lv = GR.leaves(tree)
        by = Counter(l.cand[0] for l in lv)
        tight = None
        for l in lv:
            name, br, meta = l.cand
            m = CR.bernstein_min(CR.return_poly(br, G, d, C), l.box)
            (d0, d1), (p0, p1) = l.box
            key = float(m)
            if tight is None or key < tight[0]:
                tight = (key, name, (float(d0), float(d1)), (float(p0), float(p1)))
        out[nm] = dict(leaves=len(lv), by_branch=dict(by), tightest=tight)
    return out


def diagnose(res, windows='collet', branches=None):
    kw = dict(windows=windows)
    if branches:
        kw['branches'] = branches
    C, P = res['C'], res['P']
    d = exact.diagnose(C['B'], C['L'], P['B'], P['L'], res['theta_units'], **kw)
    d['ell_needed'] = float(Fr(11, 3) - 4 * Fr(res['theta_units'], 10**9))
    d['cover'] = cover_stats(C['B'], C['L'], P['B'], P['L'], res['theta_units'], **kw)
    return d


if __name__ == '__main__':
    res = json.load(open(sys.argv[1]))
    windows = sys.argv[2] if len(sys.argv) > 2 else 'collet'
    d = diagnose(res, windows)
    print(json.dumps(d, indent=1, default=str))
