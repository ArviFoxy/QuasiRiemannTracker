"""Return floor in the Lemma D schedule (lambda_P >= 2; slope receipt dropped) against faces and windows.
usage: python3 floor_lemmaD.py BC,LC,BP,LP,sP,sC ..."""
import sys, os
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', 'repeated-marks'))
from fractions import Fraction as Fr
import cert_return as CR
CR.GLOBAL_DROP = CR.GLOBAL_DROP + ('source_lambda_low',)
CAP = Fr(os.environ.get('CAP', '549989/10000000'))
def ok(th, C, P, sP, sC):
    CR.ADM_CACHE.clear()
    try:
        rec, cov, bad = CR.run(Fr(th, 10**7), Fr(401, 500), C, P, verbose=False, sP=sP, sC=sC, mode='global')
        return not bad
    except (ValueError, AssertionError, ZeroDivisionError):
        return False
def ts(C, P, sP, sC, lo=8735000, hi=8747700):
    if not ok(hi, C, P, sP, sC): return None
    while hi - lo > 1:
        mid = (lo + hi)//2
        lo, hi = (lo, mid) if ok(mid, C, P, sP, sC) else (mid, hi)
    return hi
for a in sys.argv[1:]:
    BC, LC, BP, LP, sP, sC = (Fr(x) for x in a.split(','))
    print(a, ts((BC, LC, CAP), (BP, LP, CAP), sP, sC), flush=True)
