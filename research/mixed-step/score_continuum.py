"""Score a continuum face family (JSON rows s,E,B,L) with the exact return, physical slope receipt
dropped (Lemma D, hypothetical), scanning C and P over the family. usage: score_continuum.py FILE sC"""
import sys, os, json
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', 'repeated-marks'))
from fractions import Fraction as Fr
import cert_return as CR
CR.GLOBAL_DROP = CR.GLOBAL_DROP + ('source_lambda_low',)
CAP = Fr(549989, 10**7)
fr = lambda x: Fr(x).limit_denominator(10**12)
def ok(th, C, P, sC):
    CR.ADM_CACHE.clear()
    try:
        rec, cov, bad = CR.run(Fr(th, 10**7), Fr(401, 500), C, P, verbose=False, sP=Fr(9, 200), sC=sC, mode='global')
        return not bad
    except (ValueError, AssertionError, ZeroDivisionError):
        return False
def theta_star(C, P, sC, lo=8744000, hi=8747700):
    if not ok(hi, C, P, sC): return None
    while hi - lo > 1:
        mid = (lo + hi)//2
        lo, hi = (lo, mid) if ok(mid, C, P, sC) else (mid, hi)
    return hi
rows = json.load(open(sys.argv[1])); sC = Fr(sys.argv[2])
pick = lambda s: min(rows, key=lambda r: abs(r['s'] - s))
best = None
for sp in (0.02, 0.03, 0.04, 0.05):
    for sc in (0.04, 0.05, 0.054):
        p, c = pick(sp), pick(sc)
        C = (fr(c['B']*(1 - 2e-9)), fr(c['L']), CAP); P = (fr(p['B']*(1 - 2e-9)), fr(p['L']), CAP)
        th = theta_star(C, P, sC)
        print(f"P s={p['s']:.3f} ({p['B']:.5f},{p['L']:.4f}) C s={c['s']:.3f} ({c['B']:.5f},{c['L']:.4f}) theta*={th}", flush=True)
        if th and (best is None or th < best): best = th
print("best", best)
