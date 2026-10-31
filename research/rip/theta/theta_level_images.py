"""Do the higher Poisson levels' row images lie in the row family V?

theta_level2.py finds source spikes beyond the theta: for q = 6 the levels u^2 (x/|x|) (the conjugate cubic Gauss sum up
to classes), conj(x/|x|) and the plain level; for q = 3 the level u^2 and the plain level (u = conj g~).  If their row
images lie in the row family V of theta_twosided_grow.py (row thetas and plain characters on classes mod 36, twisted
parts for N(m) <= M on the unit classes), the two-sided projection already removes them.  For each level the script
takes the best class-phase combination (top eigenvector of the class-compressed source Gram), maps it to the rows, and
prints the fraction of its energy in V, against the random level dim V / R and against the same fraction for the
theta level u itself.

usage: python3 -I theta_level_images.py B order M [threads]
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

B = L = int(sys.argv[1]); q = int(sys.argv[2]); M = int(sys.argv[3])
nth = int(sys.argv[4]) if len(sys.argv) > 4 else 1
modeE = 0 if q == 6 else 2
t0 = time.time()
Tb = tc.build_tables(B, L, verbose=False)
R, S, rows = Tb.R, Tb.S, Tb.rows
d = np.load(tu.scratch_path('gauss_B%d_L%d.npz' % (B, L) if q == 6 else 'gauss_B%d_L%d_q%d.npz' % (B, L, q)))
Grow, gen, ut, Gsrc, nprime = d['Grow'], d['gen'], d['ut'], d['Gsrc'], d['nprime']
K = ck.Kernel(Tb.T, Tb.LOC, nthreads=nth)
SA, SB = Tb.SA.astype(np.int64), Tb.SB.astype(np.int64)
SN = Tb.SN.astype(float)
xang = (SA + SB * np.exp(2j * np.pi / 3)) / np.abs(SA + SB * np.exp(2j * np.pi / 3))
u = np.conj(Gsrc) / np.where(np.abs(Gsrc) > 1e-9, np.abs(Gsrc), 1)
cls = ((((SA % 4) * 4 + SB % 4) * 2 + nprime % 2) * 3 + (SB % 9) // 3)
prof = SN ** (-(0.5 - 1.0 / q))
levels = ([('theta u', u), ('u^2 (x/|x|)', u ** 2 * xang), ('conj(x/|x|)', np.conj(xang)), ('plain', np.ones(S))]
          if q == 6 else [('theta u', u), ('u^2', u ** 2), ('plain', np.ones(S))])
# row family V as in theta_twosided_grow.row_family(M) with J = 2 profiles
c36 = ((gen[:, 0] % 4) * 4 + gen[:, 1] % 4) * 81 + (gen[:, 0] % 9) * 9 + gen[:, 1] % 9
unit = (np.rint(ut[:, 3].real) > 0) * 3 + np.rint(np.angle(ut[:, 1]) / (2 * np.pi / 3)).astype(int) % 3
rprof = [(rows['N'].astype(float) / B) ** (-j / 2) for j in range(2)]
order = np.argsort(SN, kind='stable')
twists = [int(j) for j in order if SN[j] <= M]
cols = [tu.class_span(c36, Grow * p) for p in rprof] + [tu.class_span(c36, p.astype(complex)) for p in rprof]
for st in range(0, len(twists), 8):
    blk = twists[st:st + 8]
    V = np.zeros((S, len(blk)), complex)
    V[blk, np.arange(len(blk))] = 1
    E = K.forward(V, mode=modeE)
    for c in range(E.shape[1]):
        e = E[:, c]
        for p in rprof:
            cols += [tu.class_span(unit, Grow * np.conj(e) * p), tu.class_span(unit, e * p),
                     tu.class_span(unit, np.conj(e) * p)]
Q, Rr = np.linalg.qr(np.concatenate(cols, axis=1))
dd = np.abs(np.diag(Rr))
Q = Q[:, dd > 1e-8 * dd.max()]
print('order %d, B = L = %d: R=%d S=%d; row family V with twists N(m) <= %d: dim %d (random level %.3f)   (%.0fs)'
      % (q, B, R, S, M, Q.shape[1], Q.shape[1] / R, time.time() - t0), flush=True)
for name, lv in levels:
    X = tu.class_span(cls, lv * prof)
    X = X[:, np.linalg.norm(X, axis=0) > 1e-12]
    X = X / np.linalg.norm(X, axis=0, keepdims=True)
    EX = np.zeros((R, X.shape[1]), complex)
    for st in range(0, X.shape[1], 8):
        EX[:, st:st + 8] = K.forward(X[:, st:st + 8], mode=modeE)
    G = EX.conj().T @ EX
    w, Vv = np.linalg.eigh((G + G.conj().T) / 2)
    y = EX @ Vv[:, -1]
    frac = float(np.linalg.norm(Q.conj().T @ y) ** 2 / np.linalg.norm(y) ** 2)
    print('  %-14s best class combination: energy fraction of its row image in V %.3f' % (name, frac), flush=True)
print('done in %.0fs' % (time.time() - t0))
