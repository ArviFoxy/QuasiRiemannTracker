# Build and cache the P1 model data over Z[omega]:
#   rows k (split-squarefree primary, N(k) <= K), columns n (N/2 < N(n) <= N),
#   marks P (primary split primes, L < N(P) <= 2L),
#   Phi[k,n] = (n/k)_2, gt[n] = normalized cubic Gauss sum, Xe[n,P] = exponent of (n/P)_3.
# usage: python3 build.py K N L
import sys, os, math, time, numpy as np
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from zw import *

def build(K, N, L, outdir='data'):
    os.makedirs(outdir, exist_ok=True)
    fn = os.path.join(outdir, f'm_K{K}_N{N}_L{L}.npz')
    if os.path.exists(fn):
        return fn
    t0 = time.time()
    ar = Arith(max(N, 2 * L, K) + 10)
    rows = ar.elems(1, K)
    cols = ar.elems(N // 2, N)
    marks = ar.elems(L, 2 * L, primes_only=True)
    # prime Gauss sums for every prime dividing some column norm
    need = set()
    for c in cols:
        for p, r in zip(c['ps'], c['rs']): need.add((p, r))
    allp = [e for e in ar.elems(1, N, primes_only=True) if (e['ps'][0], e['rs'][0]) in need]
    gtab = GaussTable(ar, allp)
    gt = np.array([gtab.gt(c) for c in cols])
    A, B = col_arrays(cols)
    Phi = np.zeros((len(rows), len(cols)), dtype=np.int8)
    for i, k in enumerate(rows):
        Phi[i] = quad_row(ar, A, B, k)
    Xe = np.zeros((len(cols), len(marks)), dtype=np.int8)
    for j, P in enumerate(marks):
        Xe[:, j] = cubic_exp(ar, A, B, P)
    lam = np.array([complex(c['a'] - c['b'] / 2, c['b'] * math.sqrt(3) / 2) for c in cols])
    lam = lam / np.abs(lam)
    np.savez_compressed(fn, Phi=Phi, gt=gt, Xe=Xe, lam=lam,
                        colN=np.array([c['N'] for c in cols]), rowN=np.array([k['N'] for k in rows]),
                        markN=np.array([P['N'] for P in marks]),
                        colA=A, colB=B,
                        rowps=np.array([str(k['ps']) for k in rows]),
                        colps=np.array([str(c['ps']) for c in cols]))
    print(f'built {fn}: rows={len(rows)} cols={len(cols)} marks={len(marks)} in {time.time()-t0:.1f}s', flush=True)
    return fn

def load(K, N, L, outdir='data'):
    fn = build(K, N, L, outdir)
    d = np.load(fn)
    return {k: d[k] for k in d.files}

if __name__ == '__main__':
    K, N, L = map(int, sys.argv[1:4])
    build(K, N, L, os.path.join(os.path.dirname(os.path.abspath(__file__)), 'data'))
