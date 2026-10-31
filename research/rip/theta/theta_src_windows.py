"""The outlier's row vector on disjoint source windows: a residue, or small sources?

theta_src_residue.py finds the top left singular vector of E nearly the same for sources up to L = 1e3 ... 1e4 (rows
fixed).  Two explanations: (a) a residue -- the source sums E f(z) = sum_x f(x) chi_z(x) carry a main term
L^{1/3} conj tau6(z) that is the same row vector at every scale of x; (b) the small sources, which every L shares.
Here the sources are split into disjoint dyadic windows of N(x) and the row vector is computed on each window alone
(E restricted to the window's columns, matrix-free).  Under (a) disjoint windows give the same row direction; under
(b) they give unrelated vectors (overlap about 1/R).

For each window the script prints the top s^2/S_W of E_W and of the masked random matrix on the same columns, and
the overlaps |<u_W, u_W'>|^2 of the top left vectors between windows.

usage: python3 -I theta_src_windows.py B L nwin [k] [threads]   (windows (L/2^j, L/2^{j-1}], j = 1..nwin)
"""
import os, sys, time
sys.dont_write_bytecode = True
os.environ.setdefault('OMP_NUM_THREADS', '1')
os.environ.setdefault('OPENBLAS_NUM_THREADS', '2')
import numpy as np
from scipy.sparse.linalg import eigsh, LinearOperator

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import theta_core as tc          # noqa: E402
import theta_ckernel as ck       # noqa: E402

B = int(sys.argv[1]); L = int(sys.argv[2]); nwin = int(sys.argv[3])
k = int(sys.argv[4]) if len(sys.argv) > 4 else 2
nth = int(sys.argv[5]) if len(sys.argv) > 5 else 3
t0 = time.time()
Tb = tc.build_tables(B, L)
K = ck.Kernel(Tb.T, Tb.LOC, nthreads=nth)
R, S = Tb.R, Tb.S
SN = Tb.SN.astype(float)


def top_window(mask, mode=0):
    """top k eigenpairs of P_W E^H E P_W / |W| (rows: all), and the left vectors E v / |E v|."""
    idx = np.nonzero(mask)[0]
    SW = len(idx)

    def mv(w):
        v = np.zeros(S, complex)
        v[idx] = np.asarray(w).ravel()
        return K.adjoint(K.forward(v[:, None], mode=mode, seed=5), mode=mode, seed=5)[idx, 0]
    op = LinearOperator((SW, SW), dtype=complex, matvec=mv)
    v0 = np.random.default_rng(1).standard_normal(SW) + 0j
    lam, vec = eigsh(op, k=k, which='LA', tol=1e-6, v0=v0)
    o = np.argsort(-lam)
    lam, vec = lam[o] / SW, vec[:, o]
    V = np.zeros((S, k), complex)
    V[idx] = vec
    U = K.forward(V, mode=mode, seed=5)
    U /= np.linalg.norm(U, axis=0, keepdims=True)
    return lam, U, SW


wins = [(L / 2 ** j, L / 2 ** (j - 1)) for j in range(1, nwin + 1)]
Us = []
for lo, hi in wins:
    mask = (SN > lo) & (SN <= hi)
    lam, U, SW = top_window(mask)
    lamn, _, _ = top_window(mask, mode=1)
    Us.append(U)
    print('window N(x) in (%.0f, %.0f]: %d sources (R/S_W = %.2f); top s^2/S_W %s, masked null %s   (%.0fs)'
          % (lo, hi, SW, R / SW, np.round(lam, 3), np.round(lamn, 3), time.time() - t0), flush=True)
print('overlaps |<u0_W, u_W\'>|^2 between windows (random level %.1e):' % (1.0 / R))
for a in range(len(wins)):
    row = []
    for b in range(len(wins)):
        row.append(float(np.abs(np.vdot(Us[a][:, 0], Us[b][:, 0])) ** 2))
    print('  window %d: %s' % (a + 1, np.round(row, 3)))
print('u0 of each window against u0, u1 of the others (max over the first k): ')
for a in range(len(wins)):
    row = []
    for b in range(len(wins)):
        row.append(float(np.max(np.abs(Us[a][:, 0].conj() @ Us[b]) ** 2)))
    print('  window %d: %s' % (a + 1, np.round(row, 3)))
print('done in %.0fs' % (time.time() - t0))
