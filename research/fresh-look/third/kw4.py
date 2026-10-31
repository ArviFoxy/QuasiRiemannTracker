import sys, time
from kwlib import run_from_base, worst
K = float(sys.argv[1]); modes = sys.argv[2].split(','); s0s = [float(x) for x in sys.argv[3].split(',')]
t0 = time.time()
for s0 in s0s:
    Lend, cend, reason, path = run_from_base(K)
    print('K=%.4f s0=%.3f: line from 2.0001 ends L=%.5f (%s), %d steps' % (K, s0, Lend, reason, len(path)), flush=True)
    idx = sorted(set([1, len(path)//3, 2*len(path)//3, len(path)-1]))
    for mode in modes:
        res = []
        for i in idx:
            L, c, a = path[i]; L0, c0, _ = path[i-1]
            v, wh = worst(0.99999, L, c, a, L0, c0, K, mode, s0)
            res.append('L=%.4f:%s' % (L, 'ok(%.1e)' % v if v <= 0 else 'FAIL(%+.1e S=%.3f x=%s,%s)' % (v, wh[0], wh[3], wh[4])))
        print('   %-9s ' % mode + '  '.join(res) + '  [%.0fs]' % (time.time()-t0), flush=True)
