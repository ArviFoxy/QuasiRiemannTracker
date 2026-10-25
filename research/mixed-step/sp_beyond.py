"""sP beyond the dMinus cliff: the fork's PhysicalSchedule only uses dMinus > 1/2 (all 9 uses), so the
receipt 'dMinus_lower_3_4' can become ds > 1/2. Face caps raised to CAP. Lemma D mode.
usage: CAP=0.065 python3 sp_beyond.py BC,LC,BP,LP sC sP1 sP2 ..."""
import sys, os
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', 'repeated-marks'))
from fractions import Fraction as Fr
import cert_return as CR
CR.GLOBAL_DROP = CR.GLOBAL_DROP + ('source_lambda_low',)
_rec = CR.receipt
def receipt(G, *a, **k):
    r = _rec(G, *a, **k)
    r['dMinus_lower_3_4'] = G['ds'] - Fr(1, 2)
    return r
CR.receipt = receipt
CAP = Fr(os.environ.get('CAP', '549989/10000000'))
def ok(th, C, P, sP, sC):
    CR.ADM_CACHE.clear()
    try:
        rec, cov, bad = CR.run(Fr(th, 10**7), Fr(401, 500), C, P, verbose=False, sP=sP, sC=sC, mode='global')
        return not bad
    except (ValueError, AssertionError, ZeroDivisionError):
        return False
def ts(C, P, sP, sC, lo=8730000, hi=8747700):
    if not ok(hi, C, P, sP, sC): return None
    while hi - lo > 1:
        mid = (lo + hi)//2
        lo, hi = (lo, mid) if ok(mid, C, P, sP, sC) else (mid, hi)
    return hi
BC, LC, BP, LP = (Fr(x) for x in sys.argv[1].split(','))
sC = Fr(sys.argv[2])
for v in sys.argv[3:]:
    print(v, ts((BC, LC, CAP), (BP, LP, CAP), Fr(v), sC), flush=True)
