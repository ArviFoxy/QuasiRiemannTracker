"""Exact-return theta* for a count face C and a physical face P, with the Lean branch's settings.

`gen_return_lean.py cchain_k8b.json 8747289/10000000 401/500 58 52 <out> 13/250 9/200 global`:
h = 401/500, count window sC = 13/250, physical width sP = 9/200, mode 'global' (all receipts kept,
including the physical slope receipt). Faces are (B, L, cap) as Fractions.
usage (module): theta_star(C, P, h=Fraction(401, 500)) -> integer theta*10^7 (smallest certified)
"""
import os, sys
from fractions import Fraction as Fr
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', 'repeated-marks'))
import cert_return as CR


def ok(th, C, P, h=Fr(401, 500)):
    CR.ADM_CACHE.clear()
    try:
        rec, cov, bad = CR.run(Fr(th, 10**7), h, C, P, verbose=False, sP=Fr(9, 200), sC=Fr(13, 250),
                               mode='global')
        return not bad
    except (ValueError, AssertionError):
        return False


def theta_star(C, P, h=Fr(401, 500), lo=8740000, hi=8747400):
    if not ok(hi, C, P, h):
        return None
    while hi - lo > 1:
        mid = (lo + hi)//2
        if ok(mid, C, P, h):
            hi = mid
        else:
            lo = mid
    return hi


if __name__ == "__main__":
    import json
    ch = json.load(open(os.path.join(HERE, '..', 'repeated-marks', 'cchain_k8b.json')))
    f = lambda nd: (Fr(nd['B']), Fr(nd['L']), Fr(nd['cap']))
    print("current Lean faces (58, 52):", theta_star(f(ch[58]), f(ch[52])))
