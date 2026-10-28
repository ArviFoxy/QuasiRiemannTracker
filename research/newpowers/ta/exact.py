"""Exact (Fraction) theta* of the Lean return for a (count face, physical face) pair, transport box widened.
Thin wrapper over tc/pr86.py + tc/best.py (copies of the validated lemmaW toolchain; exact rational equality with
PR 86's Lean at PR 86's faces).  Box: BoundsN of PR 83 with `ell < 0.171` dropped (ell_max = 0.18 by default);
h is floor-coupled (largest h on the 1e-6 grid allowed by BoundsN.floor_margin and h < 0.806); six branches, Lemma W windows.
"""
import os, sys
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, 'tc'))
from fractions import Fraction as Fr
import pr86, best

SIX = ['old', 'C', 'Ccap', 'C-7', 'P', 'Pcap']


def frac(x, den=10**10):
    return Fr(round(x * den), den)


def make_cfg(BC, LC, BP, LP, ell_max=Fr(18, 100), hu=Fr(806, 1000), yu=Fr(467, 1000), branches=SIX,
             windows='lemmaW', **kw):
    cfg = pr86.Cfg(windows=windows, branches=branches, BC=frac(BC), LC=frac(LC), BP=frac(BP), LP=frac(LP), **kw)
    cfg.bounds = (Fr(873, 1000), hu, yu, ell_max)
    return cfg


def _passes(cfg, t, unit):
    try:
        return best.passes(cfg, t, unit=unit)
    except (AssertionError, ValueError):
        return False


def theta_exact(BC, LC, BP, LP, guess=0.87394, unit=10**9, span=2000, maxexp=12, **kw):
    """-> (theta float, h Fraction, theta in 1/unit) or None.   guess: theta to bracket around (units unit*guess)."""
    cfg = make_cfg(BC, LC, BP, LP, **kw)
    g = int(round(guess * unit))
    hi, lo = g + span, g - span
    n = 0
    while not _passes(cfg, hi, unit):
        lo, hi = hi, hi + 4 * span
        n += 1
        if n > maxexp:
            return None
    n = 0
    while _passes(cfg, lo, unit):
        hi, lo = lo, lo - 4 * span
        n += 1
        if n > maxexp:
            return None
    while hi - lo > 1:
        mid = (lo + hi) // 2
        if _passes(cfg, mid, unit):
            hi = mid
        else:
            lo = mid
    th = Fr(hi, unit)
    return hi / unit, best.h_for(th, cfg.bounds[1]), hi


def diagnose(BC, LC, BP, LP, th_units, unit=10**9, **kw):
    """binding information at theta* (th_units = theta* in 1/unit): failing check one unit below, failing box,
    best branch there, and the BoundsN margins at theta*."""
    cfg = make_cfg(BC, LC, BP, LP, **kw)
    out = {}
    th = Fr(th_units, unit)
    h = best.h_for(th, cfg.bounds[1])
    c_ok = cfg.copy(th=th, h=h)
    pr86.apply_globals(c_ok)
    G = pr86.geometry(c_ok)
    rec = pr86.receipts(c_ok, G)
    box = {k: float(v) for k, v in rec.items() if k in ('theta>lo', 'h<hu', 'h>793/1000', 'y>458/1000', 'y<yu', 'ell>1672/10000',
                                                        'ell<eu', 'small_saving', 'floor_margin', 'floor', 'incumbent')}
    out['h'] = float(h)
    out['ell'] = float(G['ell'])
    out['y'] = float(G['y'])
    out['box_margins'] = box
    th1 = Fr(th_units - 1, unit)
    h1 = best.h_for(th1, cfg.bounds[1])
    c_bad = cfg.copy(th=th1, h=h1)
    ok, why = pr86.certifiable(c_bad, why=True)
    out['below'] = why
    if not ok and why.startswith('cover of edge'):
        edge = why.split()[-1]
        try:
            boxes = pr86.failing_boxes(c_bad, edge, maxdepth=12)
        except Exception as e:                      # noqa
            boxes = []
        if boxes:
            d0 = min(float(b[0][0]) for b in boxes); d1 = max(float(b[0][1]) for b in boxes)
            p0 = min(float(b[1][0]) for b in boxes); p1 = max(float(b[1][1]) for b in boxes)
            out['fail_edge'] = edge
            out['fail_box'] = dict(delta=(d0, d1), p=(p0, p1), n=len(boxes))
            # best candidate on the first failing box
            import cert_return as CR
            pr86.apply_globals(c_bad)
            Gb = pr86.geometry(c_bad)
            cands = pr86.candidate_list(c_bad, Gb)
            edges = {nm: (d, C) for nm, d, C in pr86.edge_list(c_bad, Gb)}
            d, Cc = edges[edge]
            bx = boxes[0]
            res = []
            for name, br, meta in cands:
                rp = CR.return_poly(br, Gb, d, Cc)
                res.append((float(CR.bernstein_min(rp, bx)), name))
            res.sort(reverse=True)
            out['branch_margins_first_box'] = res[:3]
    return out


if __name__ == '__main__':
    import time
    t0 = time.time()
    C = (0.9888151, 2.3415005)
    P = (2478297 / 2500000, 5953751 / 2500000)
    r = theta_exact(C[0], C[1], P[0], P[1], guess=0.873955)
    print(r, time.time() - t0)
    print(diagnose(C[0], C[1], P[0], P[1], r[2]))
