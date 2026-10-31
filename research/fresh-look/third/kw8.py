import sys
from kwlib import run_from_base, worst_geo3
K = float(sys.argv[1]); s0 = float(sys.argv[2])
Lend, cend, reason, path = run_from_base(K)
idx = sorted(set([1, len(path)//2, len(path)-1]))
def passes(D):
    for i in idx:
        L, c, a = path[i]; L0, c0, _ = path[i-1]
        v, wh = worst_geo3(0.99999, L, c, a, L0, c0, K, D, s0)
        if v > 0: return False, (round(L,4), v, wh)
    return True, None
ok, info = passes(0.0); print('K=%.3f s0=%.3f (line ends %.4f): Delta=0 %s' % (K, s0, Lend, 'PASS' if ok else 'fail %s' % (info,)), flush=True)
lo, hi = 0.0, 0.12
if not ok:
    for _ in range(11):
        mid = (lo+hi)/2; ok, _ = passes(mid)
        if ok: hi = mid
        else: lo = mid
    print('   needed extra saving Delta ~ %.4f' % hi, flush=True)
