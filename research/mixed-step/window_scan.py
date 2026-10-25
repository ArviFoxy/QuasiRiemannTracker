"""Return windows (sP, sC) with the mixed-step faces (c=6), slope receipt dropped."""
import sys, os
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', 'repeated-marks'))
from fractions import Fraction as Fr
import cert_return as CR
CR.GLOBAL_DROP = CR.GLOBAL_DROP + ('source_lambda_low',)
CAP = Fr(549989, 10**7)
fr = lambda x: Fr(x).limit_denominator(10**12)
C = (fr(0.96796*(1-2e-9)), fr(2.1688), CAP); P = (fr(0.97033*(1-2e-9)), fr(2.2148), CAP)
def ok(th, sP, sC):
    CR.ADM_CACHE.clear()
    try:
        rec, cov, bad = CR.run(Fr(th, 10**7), Fr(401, 500), C, P, verbose=False, sP=sP, sC=sC, mode='global')
        return not bad
    except (ValueError, AssertionError, ZeroDivisionError):
        return False
def ts(sP, sC, lo=8743000, hi=8747700):
    if not ok(hi, sP, sC): return None
    while hi - lo > 1:
        mid = (lo + hi)//2
        lo, hi = (lo, mid) if ok(mid, sP, sC) else (mid, hi)
    return hi
for a in sys.argv[1:]:
    sP, sC = (Fr(x) for x in a.split(','))
    print(a, ts(sP, sC), flush=True)
