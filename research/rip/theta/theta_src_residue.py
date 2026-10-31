"""Is the sextic outlier's row vector a residue?  Rows fixed, sources of several lengths L.

Heuristic.  For the source theta f(x) = conj g6(x) N(x)^{-1/3} (times class phases), reciprocity and twisted
multiplicativity give E f(z) = sum_x conj g6(z, x) N(x)^{-1/3} (classes aside): a partial sum of the sextic Kubota
series psi6(z, s) = sum_x g6(z, x) N(x)^{-s} at the index z.  Its pole at s = 2/3 gives the main term
L^{1/3} conj tau6(z), with tau6 the coefficients of the sextic theta function.  So the outlier's row vector would be
tau6 itself, the same vector for every L, and its spike strength would scale like B^{5/6} L^{-2/3} (at L = B the
observed B^{1/6}).  For q = 3 the same argument gives Patterson's tau3 ~ cubic Gauss sums: the row theta (one theta).

The script keeps the rows (N z in [B, 2B]) and takes sources up to each L in the list.  For each L it prints the
top s^2/S of E and of the masked random matrix (theta_ckernel mode 1), and it compares the top left singular vectors
u_L = E v_L / |E v_L| across L, rows matched by their prime factorization: |<u_L, u_L'>|^2 against 1/R for random
vectors, and the same for the second vectors.

usage: python3 -I theta_src_residue.py B L1,L2,... [k] [threads]
"""
import os, sys, time
sys.dont_write_bytecode = True
os.environ.setdefault('OMP_NUM_THREADS', '1')
os.environ.setdefault('OPENBLAS_NUM_THREADS', '2')
import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import theta_core as tc          # noqa: E402
import theta_ckernel as ck       # noqa: E402

B = int(sys.argv[1])
Ls = [int(t) for t in sys.argv[2].split(',')]
k = int(sys.argv[3]) if len(sys.argv) > 3 else 3
nth = int(sys.argv[4]) if len(sys.argv) > 4 else 3
t0 = time.time()


def row_keys(Tb):
    """a key per row that does not depend on the ideal tables: the sorted (p, r) of its split primes and the inert q."""
    ID = Tb.ID
    keys = []
    for pids in Tb.rows['PID']:
        key = []
        for i in pids:
            i = int(i)
            if i < 0:
                continue
            if i < ID.ns:
                p, r = ID.split_pr(np.array([i]))
                key.append((int(p[0]), int(r[0])))
            else:
                key.append((int(ID.inert_q[i - ID.ns]), -1))
        keys.append(tuple(sorted(key)))
    return keys


U = {}
ref = None
for L in Ls:
    Tb = tc.build_tables(B, L)
    K = ck.Kernel(Tb.T, Tb.LOC, nthreads=nth)
    lam, vec = K.top(k=k, vectors=True, tol=1e-6)
    null = K.top(k=k, mode=1, seed=3, tol=1e-6)
    Uf = K.forward(vec)
    Uf /= np.linalg.norm(Uf, axis=0, keepdims=True)
    keys = row_keys(Tb)
    if ref is None:
        ref = {key: i for i, key in enumerate(keys)}
        perm = np.arange(len(keys))
    else:
        perm = np.array([ref[key] for key in keys])
        assert len(set(perm.tolist())) == len(perm) == len(ref), 'row sets differ'
    Ualigned = np.zeros_like(Uf)
    Ualigned[perm] = Uf
    U[L] = Ualigned
    print('L=%d: R=%d S=%d   top s^2/S %s   masked null %s   (%.0fs)'
          % (L, Tb.R, Tb.S, np.round(lam, 3), np.round(null, 3), time.time() - t0), flush=True)
R = len(ref)
print('overlaps |<u_L, u_L\'>|^2 of the top left vectors (random level %.1e):' % (1.0 / R))
for a in range(len(Ls)):
    for b in range(a + 1, len(Ls)):
        M = np.abs(U[Ls[a]].conj().T @ U[Ls[b]]) ** 2
        print('  L=%d vs L=%d:' % (Ls[a], Ls[b]))
        for i in range(k):
            print('    u%d(L=%d) against u0..u%d(L=%d): %s' % (i, Ls[a], k - 1, Ls[b], np.round(M[i], 3)))
print('done in %.0fs' % (time.time() - t0))
