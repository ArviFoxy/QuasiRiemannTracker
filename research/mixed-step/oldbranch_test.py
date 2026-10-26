"""What if the old count branch used a better natural slope (Sil's 93/25 instead of 6κ)?
usage: python3 oldbranch_test.py KAPPA_EFF 'design'"""
import sys, os
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', 'repeated-marks'))
from fractions import Fraction as Fr
import cert_return as CR
import ret_scan as RS
KE = Fr(sys.argv[1])
_bo = CR.branch_old
CR.branch_old = lambda kappa: _bo(KE)
P = dict(RS.DEF)
for kv in sys.argv[2].split(','):
    k, v = kv.split('='); P[k] = v
P = {k: Fr(v) for k, v in P.items()}
print(sys.argv[1], RS.ts(P), flush=True)
