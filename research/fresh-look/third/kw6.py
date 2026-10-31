import sys, time
from kwlib import run_from_base, worst_geo
K = float(sys.argv[1]); s0 = float(sys.argv[2]); kind = sys.argv[3]
Lend, cend, reason, path = run_from_base(K)
idx = sorted(set([1, len(path)//2, len(path)-1]))
print('K=%.3f s0=%.3f kind=%s: line ends %.4f' % (K, s0, kind, Lend), flush=True)
def passes(D):
    for i in idx:
        L, c, a = path[i]; L0, c0, _ = path[i-1]
        v, wh = worst_geo(0.99999, L, c, a, L0, c0, K, D, s0, kind)
        if v > 0: return False, (L, v, wh)
    return True, None
lo, hi = 0.0, 0.2
ok, info = passes(lo); print(' Delta=0 (geometry-resolved elementary bound):', 'PASS' if ok else 'fail %s' % (info,), flush=True)
if not ok:
    for _ in range(12):
        mid = (lo+hi)/2; ok, info = passes(mid)
        if ok: hi = mid
        else: lo = mid
    print(' extra saving needed over the elementary per-range bound: Delta ~ %.4f' % hi, flush=True)
