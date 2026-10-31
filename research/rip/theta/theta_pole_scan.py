"""Locate the source theta's pole: the split weight's zero swept across s.

For the class-signed source theta level u with weight U_s(t) = t^{-1/3}(1_{t<=1/2} - c(s) 1_{t>1/2}),
c(s) = 2^{-(s-1/3)}/(1 - 2^{-(s-1/3)}), the Mellin transform of t^{-1/3}-normalized weights vanishes at s.  The excess
of the top of the class-compressed source Gram (72 classes) over the masked null should be smallest when s is the
pole (2/3 if the residue picture is right) and grow like |s - s0|^2 on either side.

usage: python3 -I theta_pole_scan.py B s1,s2,... [threads]
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

B = L = int(sys.argv[1])
ss = [float(x) for x in sys.argv[2].split(',')]
nth = int(sys.argv[3]) if len(sys.argv) > 3 else 3
t0 = time.time()
Tb = tc.build_tables(B, L, verbose=False)
R, S = Tb.R, Tb.S
d = np.load(tu.scratch_path('gauss_B%d_L%d.npz' % (B, L)))
Gsrc, nprime = d['Gsrc'], d['nprime']
K = ck.Kernel(Tb.T, Tb.LOC, nthreads=nth)
SA, SB = Tb.SA.astype(np.int64), Tb.SB.astype(np.int64)
t = Tb.SN.astype(float) / L
u = np.conj(Gsrc) / np.where(np.abs(Gsrc) > 1e-9, np.abs(Gsrc), 1)
cls = ((((SA % 4) * 4 + SB % 4) * 2 + nprime % 2) * 3 + (SB % 9) // 3)


def top_ratio(v):
    X = tu.class_span(cls, v)
    X = X[:, np.linalg.norm(X, axis=0) > 1e-12]
    X = X / np.linalg.norm(X, axis=0, keepdims=True)
    out = []
    for mode, seed in ((0, 0), (1, 3), (1, 4)):
        EX = np.zeros((R, X.shape[1]), complex)
        for st in range(0, X.shape[1], 8):
            EX[:, st:st + 8] = K.forward(X[:, st:st + 8], mode=mode, seed=seed)
        G = EX.conj().T @ EX
        out.append(np.linalg.eigvalsh((G + G.conj().T) / 2)[-1])
    return out[0] / np.mean(out[1:])


print('B = L = %d: R=%d S=%d   (%.0fs)' % (B, R, S, time.time() - t0), flush=True)
for s in ss:
    q = 2 ** (-(s - 1 / 3))
    c = q / (1 - q)
    r = top_ratio(u * t ** (-1 / 3) * np.where(t <= 0.5, 1.0, -c))
    print('  zero at s = %.3f (c = %.3f): %.4f' % (s, c, r), flush=True)
print('done in %.0fs' % (time.time() - t0))
