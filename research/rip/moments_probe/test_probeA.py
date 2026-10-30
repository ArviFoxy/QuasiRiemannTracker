"""End-to-end check of probeA.py against a slow reference built only from the original round7 code
(zw.GaussTable with direct Gauss sums, zw.quad_row, zw.cubic_val).

usage: python3 -I test_probeA.py [K]          (default K = 150, columns up to K*N(P)_max = 5550)
Runs probeA.py for a single K, then recomputes S(k,P) and G_{PP'}(K) with plain loops and compares.
"""
import sys, os, math, subprocess, tempfile
sys.dont_write_bytecode = True
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import numpy as np
import fastgauss as fg                       # sets sys.path for zw
from zw import Arith, GaussTable, quad_row, col_arrays, cubic_val

K = int(sys.argv[1]) if len(sys.argv) > 1 else 150
tmp = tempfile.mkdtemp()
out = os.path.join(tmp, 'a.npz')
subprocess.run([sys.executable, '-I', os.path.join(HERE, 'probeA.py'), out, '--kmax', str(K), '--kmin', str(K), '--ngrid', '1',
                '--nprimes', '10', '--w', 'lin', '--gmode', 'true'], check=True, stdout=subprocess.DEVNULL, env=dict(os.environ))
d = np.load(out)
G_fast = d['G'][0]
PN = d['PN']

# ---- slow reference
ar = Arith(40 * K + 50)
P = sorted(ar.elems(1, 300, primes_only=True), key=lambda e: (e['N'], e['a'], e['b']))[:10]
Nmax = max(e['N'] for e in P)
cols = ar.elems(1, K * Nmax)
rows = ar.elems(1, K)
allp = [e for e in cols if len(e['ps']) == 1]
gtab = GaussTable(ar, allp)                                   # direct O(p) numpy Gauss sums
gt = np.array([gtab.gt(c) for c in cols])
A, B = col_arrays(cols)
N = np.array([c['N'] for c in cols], float)
S = np.zeros((len(rows), len(P)), dtype=complex)
for j, Pj in enumerate(P):
    w = np.clip(1.0 - N / (K * Pj['N']), 0, None)
    chi = np.conj(cubic_val(ar, A, B, Pj))                    # conj((n/P)_3), 0 if P | n
    for i, k in enumerate(rows):
        S[i, j] = np.sum(gt * quad_row(ar, A, B, k) * chi * w)
G_slow = S.T @ S.conj()
print(f'K={K}: rows {len(rows)} (probeA R={int(d["R"][0])}), columns {len(cols)}')
print(f'max |G_fast - G_slow| / max|G_slow| = {np.max(np.abs(G_fast - G_slow)) / np.max(np.abs(G_slow)):.3e}')

# conjugation symmetry used to explain the (P, Pbar) class: S(kbar, P) = conj S(k, Pbar), hence G_{P Pbar} = 2 * (sum over pairs {k, kbar})
rpos = {(r['a'], r['b']): i for i, r in enumerate(rows)}
ppos = {(e['a'], e['b']): j for j, e in enumerate(P)}
dmax = 0.0
for i, r in enumerate(rows):
    ik = rpos[(r['a'] - r['b'], -r['b'])]
    for j, e in enumerate(P):
        jb = ppos[(e['a'] - e['b'], -e['b'])]
        dmax = max(dmax, abs(S[ik, j] - np.conj(S[i, jb])))
print(f'max |S(kbar,P) - conj S(k,Pbar)| over all rows and P = {dmax:.3e}   (max |S| = {np.max(np.abs(S)):.1f})')
