"""K-wall ledger with the bilinear base-sieve excess gamma (balanced corner): which cut K passes?
Uses ledger_gamma2.worst_sel_min (min of the selected branch and the parent face, minus u) along the native line."""
import os, sys, time
sys.path.insert(0, '/home/user/QuasiRiemannTracker/research/selected-leaf')
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from native_line import run
from ledger_gamma2 import worst_sel_min
t0 = time.time()
for Kline in [float(k) for k in sys.argv[1].split(',')]:
    Lend, cend, reason, path = run(Kline)
    print('K=%.3f native line ends at L=%.4f (%s)' % (Kline, Lend, reason), flush=True)
    for gamma in [float(g) for g in sys.argv[2].split(',')]:
        for Lq in (2.3, 2.05, Lend + 2e-4):
            i = min(range(1, len(path)), key=lambda j: abs(path[j][0] - Lq)); L, c, a = path[i]; L0, c0, _ = path[i - 1]
            v, where = worst_sel_min(0.99999, L, c, a, 0.99999, L0, c0, Kline, gamma, nS=21, nt=7)
            print('  gamma=%.3f L=%.4f: max(min(sel,parent)-u) = %+.2e  at S=%s x=%s M=%s sel=%s par=%s  (%.0fs)'
                  % (gamma, L, v, where['S'], where['x'], where['M'], where['sel'], where['par'], time.time() - t0), flush=True)
