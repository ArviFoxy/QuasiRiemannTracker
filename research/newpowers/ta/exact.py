"""Exact (Fraction) theta* of the Lean return for a (count face, physical face) pair, transport box widened.
Thin wrapper over tc/pr86.py + tc/best.py (copies of the validated lemmaW toolchain, exact rational equality
with PR 86's Lean at PR 86's faces).  Box: BoundsN of PR 83 with `ell < 0.171` dropped (default ell_max = 0.18).
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

def theta_exact(BC, LC, BP, LP, unit=10**9, anchor=873960000, lo=873500000, step=1000, maxstep=80, **kw):
    """-> (theta float, h Fraction, theta in 1/unit)  or None"""
    cfg = make_cfg(BC, LC, BP, LP, **kw)
    r = best.theta_best(cfg, unit=unit, anchor=anchor, lo=lo, step=step, maxstep=maxstep)
    if r is None:
        return None
    return r[0] / unit, r[1], r[0]

if __name__ == '__main__':
    import time
    t0 = time.time()
    # PR 86 final face, role split with step 38 (lemmaW.md: 0.873954831)
    C = (0.9888151, 2.3415005)
    P = (2478297 / 2500000, 5953751 / 2500000)
    r = theta_exact(C[0], C[1], P[0], P[1])
    print(r, time.time() - t0)
