import sys, time
from kwlib import run_from_base, worst2
Ks = [float(k) for k in sys.argv[1].split(',')]; gammas = sys.argv[2].split(','); s0s = [float(x) for x in sys.argv[3].split(',')]
t0 = time.time()
for K in Ks:
    Lend, cend, reason, path = run_from_base(K)
    print('K=%.4f: line from 2.0001 ends L=%.5f (%s), %d steps' % (K, Lend, reason, len(path)), flush=True)
    idx = sorted(set([1, len(path)//4, len(path)//2, 3*len(path)//4, len(path)-1]))
    for s0 in s0s:
        for g in gammas:
            res = []; okall = True
            for i in idx:
                L, c, a = path[i]; L0, c0, _ = path[i-1]
                v, wh = worst2(0.99999, L, c, a, L0, c0, K, g, s0)
                okall &= v <= 0
                if v > 0: res.append('L=%.4f FAIL(%+.1e S=%.3f s=%.3f x=%.3f)' % (L, v, wh[0], wh[1], wh[3]))
            print('   s0=%.3f gamma=%s: %s %s [%.0fs]' % (s0, g, 'PASS' if okall else 'fail', ' '.join(res[:2]), time.time()-t0), flush=True)
