"""Upper bound on a better tail treatment: drop one FR8 admission test and recompute theta*."""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from fractions import Fraction as Fr
import atlas as A
A.init()
M = A.MOD
orig = M.admission_polys
def dropping(keys):
    def f(br, B, L, s_plus, capped):
        polys, scal = orig(br, B, L, s_plus, capped)
        for k in keys:
            polys.pop(k, None); scal.pop(k, None)
        return polys, scal
    return f
for arg in sys.argv[1:]:
    keys = [k for k in arg.split('+') if k]
    M.admission_polys = dropping(keys)
    print('drop', keys or 'nothing', A.theta_star(dict(A.BASE)), flush=True)
