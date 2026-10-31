"""Top of the sextic spectrum at B = L up to 3e5, matrix-free, with the compiled kernel (theta_ckernel).

E[z, x] = chi_z(x) is rebuilt row by row from the symbol table (int8, row prime x source, 3 GB at 3e5) and
E^H E v is applied in one fused pass, so no R x S array is ever stored.  Compared models, all with E's exact zero
pattern (shared primes):
  * sextic    : the true symbols;
  * random    : i.i.d. phases (32nd roots of unity) on the zero pattern, a few seeds;
  * rchar     : each row prime's character conjugated at random (reciprocity broken, rows still characters), a few draws.
Prints the top k eigenvalues of E^H E / S (= top singular values squared over S) of each, and at the end the excess of
the sextic top over the masked random mean, the implied rank-one spike strength theta from
lambda / lambda_edge = (sqrt(theta) + 1/sqrt(theta))^2 / 4, and the RCHAR level.

usage: python3 -I theta_top_free2.py B L [--k 4] [--threads 3] [--nrandom 3] [--nrchar 2] [--tol 1e-4]
                                        [--models sextic,random,rchar] [--ncv 40]
"""
import os, sys, math, time, argparse
sys.dont_write_bytecode = True
import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import theta_core as tc          # noqa: E402
import theta_ckernel as ck       # noqa: E402

ap = argparse.ArgumentParser()
ap.add_argument('B', type=int); ap.add_argument('L', type=int)
ap.add_argument('--k', type=int, default=4)
ap.add_argument('--threads', type=int, default=3)
ap.add_argument('--nrandom', type=int, default=3)
ap.add_argument('--nrchar', type=int, default=2)
ap.add_argument('--tol', type=float, default=1e-4)
ap.add_argument('--ncv', type=int, default=40)
ap.add_argument('--models', default='sextic,random,rchar')
a = ap.parse_args()
models = a.models.split(',')
t0 = time.time()
tb = tc.build_tables(a.B, a.L)
T, LOC, R, S, uid = tb.T, tb.LOC, tb.R, tb.S, tb.uid
K = ck.Kernel(T, LOC, nthreads=a.threads)
assert K.T is T
v = np.random.default_rng(0).standard_normal(S) + 0j
tm = time.time(); K.matvec(v, 0); tm = time.time() - tm
print('kernel: %d threads, %.2fs per matvec (R x S = %.2e entries), %.0fs elapsed' % (a.threads, tm, float(R) * S, time.time() - t0),
      flush=True)
log = lambda s: print(s, flush=True)


def top(mode, seed=0):
    return K.top(a.k, mode, seed, tol=a.tol, ncv=a.ncv, log=log)


res = {}
if 'sextic' in models:
    res['sextic'] = top(0)
    print('sextic E      : %s   (%.0fs)' % (np.round(res['sextic'], 4), time.time() - t0), flush=True)
if 'random' in models:
    res['random'] = []
    for s in range(a.nrandom):
        res['random'].append(top(1, s + 1))
        print('masked random : %s   seed %d  (%.0fs)' % (np.round(res['random'][-1], 4), s + 1, time.time() - t0), flush=True)
if 'rchar' in models:
    res['rchar'] = []
    flip = np.zeros(len(uid), bool)                       # rows of T currently conjugated
    for s in range(a.nrchar):
        want = np.random.default_rng(31 + s).integers(0, 2, size=len(uid)).astype(bool)
        for i in np.nonzero(want != flip)[0]:             # conjugation t -> -t (mod 6) is an involution
            t = T[i]
            T[i] = np.where(t < 6, (6 - t) % 6, t)
        flip = want
        res['rchar'].append(top(0))
        print('RCHAR         : %s   draw %d  (%.0fs)' % (np.round(res['rchar'][-1], 4), s + 1, time.time() - t0), flush=True)
print('MP edge (no mask) %.3f' % ((math.sqrt(R) + math.sqrt(S)) ** 2 / S))


def spike(r):
    """theta from lambda / lambda_edge = (sqrt(theta) + 1/sqrt(theta))^2 / 4  (r >= 1)."""
    return (math.sqrt(r) + math.sqrt(r - 1.0)) ** 2 if r > 1 else float('nan')


if 'sextic' in res and 'random' in res:
    edge = float(np.mean([e[0] for e in res['random']]))
    lam = float(res['sextic'][0])
    sd = float(np.std([e[0] for e in res['random']])) if len(res['random']) > 1 else float('nan')
    print('SUMMARY B=%d L=%d R=%d S=%d: sextic %.4f  masked random edge %.4f (sd %.4f, %d seeds)  excess %+.1f%%  theta %.3f' %
          (a.B, a.L, R, S, lam, edge, sd, len(res['random']), 100 * (lam / edge - 1), spike(lam / edge)))
    if 'rchar' in res:
        print('SUMMARY RCHAR top %s' % ', '.join('%.4f' % e[0] for e in res['rchar']))
