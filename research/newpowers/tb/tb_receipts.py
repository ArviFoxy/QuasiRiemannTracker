"""Scalar side conditions ("receipts") of the Lean return (pr86.receipts, which mirrors Return/*.lean) at lower theta.

This does NOT run the Bernstein cover; it only evaluates the scalar receipts (box fields, floor, conductor ordering,
physical schedule bounds, ...) at (theta, h) with PR 86's faces, with the BoundsN receipts evaluated against a given
box.  It shows which scalar conditions other than the box are affected by lowering theta.

usage: python3 tb_receipts.py
Uses the verbatim copies of the exact-return toolchain in ./tc (pr86.py, cert_return.py, gen_return_lean.py, chain_params.py).
"""
import os, sys
os.environ.setdefault('QRH_K', '9/2')
TC = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'tc')   # verbatim copies of pr86.py, cert_return.py, gen_return_lean.py, chain_params.py
sys.path.insert(0, TC)
from fractions import Fraction as Fr
import pr86
from tb_common import *

BOUNDS_WIDE = (Fr(873, 1000), Fr(806, 1000), Fr(467, 1000), Fr(175, 1000))   # theta>, h<, y<, ell<  (cfg.bounds layout)


def recs(th, h, bounds=BOUNDS_WIDE):
    cfg = pr86.Cfg(th=th, h=h, bounds=bounds)
    pr86.apply_globals(cfg)
    G = pr86.geometry(cfg)
    return pr86.receipts(cfg, G)


def main():
    pts = [('PR86 declared', Fr(4369779, 5000000), Fr(8051, 10000)),
           ('0.8739167', Fr(8739167, 10**7), Fr(8048, 10000)),
           ('target 0.8739058', Fr(8739058, 10**7), Fr(8047, 10000)),
           ('0.8738', Fr(8738, 10**4), Fr(8037, 10000)),
           ('0.8737', Fr(8737, 10**4), Fr(8028, 10000)),
           ('0.8736', Fr(8736, 10**4), Fr(8018, 10000)),
           ('0.8735', Fr(8735, 10**4), Fr(8009, 10000))]
    names = None
    table = {}
    for nm, th, h in pts:
        r = recs(th, h)
        table[nm] = r
        names = list(r)
    base = table['PR86 declared']
    print('receipts that change by more than 1e-4 between theta=0.8739558 and theta=0.8735 (value at each point):')
    cols = [p[0] for p in pts]
    print('%-34s' % 'receipt' + ''.join('%17s' % c[:16] for c in cols))
    for k in names:
        vals = [table[c][k] for c in cols]
        if max(vals) - min(vals) > Fr(1, 10**4) or min(vals) <= 0:
            print('%-34s' % k + ''.join('%17.3e' % float(v) for v in vals))
    print()
    print('negative receipts per point (box bounds widened to theta>0.873, h<0.806, y<0.467, ell<0.175):')
    for c in cols:
        bad = {k: float(v) for k, v in table[c].items() if v <= 0 and k not in ('wC<=capC', 'wP<=capP')}
        print('  %-18s %s' % (c, bad if bad else 'none'))


if __name__ == '__main__':
    main()
