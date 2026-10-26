"""Add Sil's face (99999/100000, 93/25, cap 3/50) as a third affine count branch at the new design point.
usage: python3 silbranch_test.py s_plus 'design'"""
import sys, os
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', 'repeated-marks'))
from fractions import Fraction as Fr
import cert_return as CR
import ret_scan as RS
SPLUS = Fr(sys.argv[1])
_cand = CR.candidates
def candidates(faces, kap):
    f = dict(faces); f['S'] = (Fr(99999, 100000), Fr(93, 25), SPLUS)
    return _cand(f, kap)
CR.candidates = candidates
P = dict(RS.DEF)
for kv in sys.argv[2].split(','):
    k, v = kv.split('='); P[k] = v
P = {k: Fr(v) for k, v in P.items()}
print(sys.argv[1], RS.ts(P), flush=True)
