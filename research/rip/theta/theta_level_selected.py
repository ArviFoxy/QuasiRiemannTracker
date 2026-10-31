"""Are the higher Poisson levels' row images flat on slot-selected rows?  (Lambda_src for the levels, K-wall)

For each source level of theta_level2.py (best class-phase combination), the row image Phi = E v is compared with the
slot-selected row sets W = the top rho*R rows by |T(z)|, T(z) = sum over the split primes pi with N(pi) in [P0, 2 P0]
of chi_z(pi) (as in theta_src_twisted_selected.py).  Printed: the concentration (sum_W |Phi|^2 / sum |Phi|^2) / rho,
which is 1 for a flat image, and the same for random row sets of the same size.

usage: python3 -I theta_level_selected.py B order P0[,P0..] rho[,rho..] [threads]
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
P0s = [int(t) for t in sys.argv[3].split(',')]
rhos = [float(t) for t in sys.argv[4].split(',')]
nth = int(sys.argv[5]) if len(sys.argv) > 5 else 1
modeE = 0 if q == 6 else 2
t0 = time.time()
Tb = tc.build_tables(B, L, verbose=False)
R, S = Tb.R, Tb.S
d = np.load(tu.scratch_path('gauss_B%d_L%d.npz' % (B, L) if q == 6 else 'gauss_B%d_L%d_q%d.npz' % (B, L, q)))
Gsrc, nprime = d['Gsrc'], d['nprime']
K = ck.Kernel(Tb.T, Tb.LOC, nthreads=nth)
SA, SB = Tb.SA.astype(np.int64), Tb.SB.astype(np.int64)
SN = Tb.SN.astype(float)
xang = (SA + SB * np.exp(2j * np.pi / 3)) / np.abs(SA + SB * np.exp(2j * np.pi / 3))
u = np.conj(Gsrc) / np.where(np.abs(Gsrc) > 1e-9, np.abs(Gsrc), 1)
cls = ((((SA % 4) * 4 + SB % 4) * 2 + nprime % 2) * 3 + (SB % 9) // 3)
prof = SN ** (-(0.5 - 1.0 / q))
levels = ([('theta u', u), ('u^2 (x/|x|)', u ** 2 * xang), ('conj(x/|x|)', np.conj(xang)), ('plain', np.ones(S))]
          if q == 6 else [('theta u', u), ('u^2', u ** 2), ('plain', np.ones(S))])
isprime = np.array([int(Tb.spf[int(n)]) == int(n) for n in SN])
rng = np.random.default_rng(29)
print('order %d, B = L = %d: R=%d S=%d   (%.0fs)' % (q, B, R, S, time.time() - t0), flush=True)
Ws = {}
for P0 in P0s:
    T = K.forward(((SN >= P0) & (SN <= 2 * P0) & isprime).astype(complex)[:, None], mode=modeE)[:, 0]
    rank = np.argsort(-np.abs(T))
    for rho in rhos:
        Ws[(P0, rho)] = rank[:max(1, int(rho * R))]
for name, lv in levels:
    X = tu.class_span(cls, lv * prof)
    X = X[:, np.linalg.norm(X, axis=0) > 1e-12]
    X = X / np.linalg.norm(X, axis=0, keepdims=True)
    EX = np.zeros((R, X.shape[1]), complex)
    for st in range(0, X.shape[1], 8):
        EX[:, st:st + 8] = K.forward(X[:, st:st + 8], mode=modeE)
    G = EX.conj().T @ EX
    w, Vv = np.linalg.eigh((G + G.conj().T) / 2)
    phi2 = np.abs(EX @ Vv[:, -1]) ** 2
    out = []
    for (P0, rho), W in Ws.items():
        conc = phi2[W].sum() / phi2.sum() / rho
        rnd = np.mean([phi2[rng.choice(R, len(W), replace=False)].sum() / phi2.sum() / rho for _ in range(20)])
        out.append('P0=%d rho=%.2f: %.3f (random %.3f)' % (P0, rho, conc, rnd))
    print('  %-14s concentration on W: %s' % (name, ';  '.join(out)), flush=True)
print('done in %.0fs' % (time.time() - t0))
