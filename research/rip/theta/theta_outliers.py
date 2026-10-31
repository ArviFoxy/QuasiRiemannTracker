"""How many eigenvalues of E^H E / S sit above the masked random edge, and how far?

The top of the sextic spectrum is a cluster of outliers, not a single spike.  This script computes the top k eigenvalues of
the sextic E^H E / S with the compiled kernel (matrix-free, any B = L the tables fit) and counts those above
edge * (1 + delta) for delta = 1%, 2%, 5%, 10%, where the edge is the mean top eigenvalue of the masked random phases
read from the theta_top_free*_B<B>.log of the same size (run theta_top_free2.py first), or given with --edge.
It also prints the implied spike strength theta_i of each outlier from lambda_i / edge = (sqrt(theta) + 1/sqrt(theta))^2/4.

usage: python3 -I theta_outliers.py B L [--k 24] [--threads 3] [--edge 3.99] [--tol 1e-4]
"""
import os, sys, math, time, glob, argparse
os.environ.setdefault('OPENBLAS_NUM_THREADS', '1')
sys.dont_write_bytecode = True
import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import theta_core as tc          # noqa: E402
import theta_ckernel as ck       # noqa: E402

ap = argparse.ArgumentParser()
ap.add_argument('B', type=int); ap.add_argument('L', type=int)
ap.add_argument('--k', type=int, default=24)
ap.add_argument('--threads', type=int, default=3)
ap.add_argument('--edge', type=float, default=None)
ap.add_argument('--tol', type=float, default=1e-4)
a = ap.parse_args()
HERE = os.path.dirname(os.path.abspath(__file__))
edge = a.edge
if edge is None:
    vals = []
    for path in sorted(glob.glob(os.path.join(HERE, 'theta_top_free*_B%d.log' % a.B))):
        for line in open(path):
            if line.startswith('masked random') and '[' in line:
                vals.append(float(line.split('[')[1].split()[0]))
    if not vals:
        sys.exit('no masked random edge found for B=%d: run theta_top_free2.py first or pass --edge' % a.B)
    edge = float(np.mean(vals))
t0 = time.time()
tb = tc.build_tables(a.B, a.L)
K = ck.Kernel(tb.T, tb.LOC, nthreads=a.threads)
ev = K.top(k=a.k, tol=a.tol, ncv=max(2 * a.k + 1, 60), log=lambda s: print(s, flush=True))
print('B=%d: masked random edge %.4f; top %d eigenvalues of E^H E / S:' % (a.B, edge, a.k))
print('  ' + ' '.join('%.3f' % e for e in ev))
print('  lambda_i / edge - 1 (%%): ' + ' '.join('%.1f' % (100 * (e / edge - 1)) for e in ev))
print('  theta_i: ' + ' '.join(('%.2f' % ((math.sqrt(e / edge) + math.sqrt(e / edge - 1)) ** 2)) if e > edge else '-' for e in ev))
for dl in (0.01, 0.02, 0.05, 0.10):
    n = int(np.sum(ev > edge * (1 + dl)))
    print('  eigenvalues above edge*(1+%.2f): %d%s   (%.0fs)' % (dl, n, ' (>= k: more not shown)' if n >= a.k else '', time.time() - t0))
