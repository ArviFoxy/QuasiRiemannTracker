"""Row-side Poisson levels: powers of the row Gauss sum times angular characters, best class phases.

The row-side analogue of theta_level2.py.  For each (j, l) the row vector c = w^j (z/|z|)^l (w = conj g~(z), the row
theta's Gauss sum; z/|z| the angle of the row's generator) is restricted to the row classes (generator mod 4, chi_z(-1),
the parity of the number of prime factors, and the cube-root class mod 9), mapped to the sources by the adjoint, and
the top eigenvalue of the normalized class-compressed row Gram E E^H is divided by the same for the masked random
matrix (mode 1, mean of two seeds).  Gauss sums from theta_twosided_grow.py's cache ($SCRATCH).

usage: python3 -I theta_level2_rows.py B order [threads]
"""
import os, sys, time
sys.dont_write_bytecode = True
os.environ.setdefault('OMP_NUM_THREADS', '1')
os.environ.setdefault('OPENBLAS_NUM_THREADS', '1')
import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import theta_core as tc          # noqa: E402
import theta_ckernel as ck       # noqa: E402
import theta_util as tu          # noqa: E402

B = L = int(sys.argv[1]); q = int(sys.argv[2])
nth = int(sys.argv[3]) if len(sys.argv) > 3 else 2
modeE = 0 if q == 6 else 2
t0 = time.time()
Tb = tc.build_tables(B, L, verbose=False)
R, S = Tb.R, Tb.S
d = np.load(tu.scratch_path('gauss_B%d_L%d.npz' % (B, L) if q == 6 else 'gauss_B%d_L%d_q%d.npz' % (B, L, q)))
Grow, gen, ut = d['Grow'], d['gen'], d['ut']
K = ck.Kernel(Tb.T, Tb.LOC, nthreads=nth)
g0, g1 = gen[:, 0].astype(np.int64), gen[:, 1].astype(np.int64)
zc = g0 + g1 * np.exp(2j * np.pi / 3)
ang = zc / np.abs(zc)
w = np.conj(Grow) / np.where(np.abs(Grow) > 1e-9, np.abs(Grow), 1)
npr = np.array([int(np.sum(np.asarray(p) >= 0)) for p in Tb.rows['PID']])
cls = ((((g0 % 4) * 4 + g1 % 4) * 2 + (np.rint(ut[:, 3].real) > 0)) * 2 + npr % 2) * 3 + (g1 % 9) // 3


def top_ratio(v):
    X = tu.class_span(cls, v)
    X = X[:, np.linalg.norm(X, axis=0) > 1e-12]
    X = X / np.linalg.norm(X, axis=0, keepdims=True)
    out = []
    for mode, seed in ((modeE, 0), (1, 3), (1, 4)):
        EX = np.zeros((S, X.shape[1]), complex)
        for st in range(0, X.shape[1], 8):
            EX[:, st:st + 8] = K.adjoint(X[:, st:st + 8], mode=mode, seed=seed)
        G = EX.conj().T @ EX
        out.append(np.linalg.eigvalsh((G + G.conj().T) / 2)[-1])
    return out[0] / np.mean(out[1:]), X.shape[1]


js = range(6) if q == 6 else range(3)
print('order %d, B = L = %d: R=%d S=%d; top of the class-compressed row Gram of w^j (z/|z|)^l, w = conj g~(z), '
      'over the masked null' % (q, B, R, S), flush=True)
print('   j \\ l ' + ''.join('%8d' % l for l in range(-3, 4)), flush=True)
for j in js:
    row = []
    for l in range(-3, 4):
        r, ncol = top_ratio(w ** j * ang ** l)
        row.append(r)
    print('   %3d   ' % j + ''.join('%8.3f' % r for r in row) + '   (%d classes, %.0fs)' % (ncol, time.time() - t0),
          flush=True)
print('done in %.0fs' % (time.time() - t0))
