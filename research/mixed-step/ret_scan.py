"""Exact return theta* with dMinus > 1/2 (fork field relaxed), Lemma D mode, arbitrary design.
usage: python3 ret_scan.py 'BC=..,LC=..,BP=..,LP=..,sP=..,sC=..,cap=..,h=..,sPp=..' ..."""
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
DEF = dict(BC='0.96796', LC='2.1688', BP='0.97033', LP='2.2148', sP='0.052', sC='0.054',
           cap='0.0549989', h='401/500', sPp='43/1000')
def ok(th, P):
    CR.ADM_CACHE.clear()
    C = (P['BC'], P['LC'], P['cap']); Pf = (P['BP'], P['LP'], P['cap'])
    try:
        rec, cov, bad = CR.run(Fr(th, 10**7), P['h'], C, Pf, verbose=False, sP=P['sP'], sC=P['sC'],
                               sPp=P['sPp'], mode='global')
        return not bad
    except (ValueError, AssertionError, ZeroDivisionError):
        return False
def ts(P, lo=8725000, hi=8747700):
    if not ok(hi, P): return None
    while hi - lo > 1:
        mid = (lo + hi)//2
        lo, hi = (lo, mid) if ok(mid, P) else (mid, hi)
    return hi
for a in sys.argv[1:]:
    P = dict(DEF)
    for kv in a.split(','):
        if kv: k, v = kv.split('='); P[k] = v
    P = {k: Fr(v) for k, v in P.items()}
    print(a, ts(P), flush=True)
