import sys, numpy as np
from kwlib import run_from_base, worst_geo3, worst_geo2
K = float(sys.argv[1]); s0 = float(sys.argv[2]); Lstop = float(sys.argv[3]); kind = sys.argv[4]
Lend, cend, reason, path = run_from_base(K)
path = [p for p in path if p[0] >= Lstop - 1e-9]
idx = sorted(set([1] + [int(len(path)*f) for f in (0.2, 0.4, 0.6, 0.8)] + [len(path)-1]))
fn = worst_geo3 if kind == 'C' else worst_geo2
def passes(D):
    for i in idx:
        L, c, a = path[i]; L0, c0, _ = path[i-1]
        v, wh = fn(0.99999, L, c, a, L0, c0, K, D, s0)
        if v > 0: return False, (round(L,4), v, wh)
    return True, None
ok, info = passes(0.0)
msg = 'PASS' if ok else 'fail %s' % (info,)
hi = 0.0
if not ok:
    lo, hi = 0.0, 0.12
    for _ in range(10):
        mid = (lo+hi)/2; ok2, _ = passes(mid)
        if ok2: hi = mid
        else: lo = mid
print('K=%.3f s0=%.3f stop at L=%.4f [%s]: Delta=0 %s ; needed Delta ~ %.4f' % (K, s0, path[-1][0], kind, msg, hi), flush=True)
