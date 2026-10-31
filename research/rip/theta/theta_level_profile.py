"""Do the source spikes vanish for radial weights with zero Mellin transform at the pole?  (reference-wall rescue)

The spike part of a source vector v is a Kubota-type sum whose main term is L^{s0} times the Mellin transform
I(U) = int U(t) t^{s0-1} dt of v's radial weight U(N x / L) at the pole s0.  For the sextic matrix the source theta
grows like L^{1/3} with the weight N^{-1/3}, so s0 = 2/3 in this normalization, and for the weight
U(t) = t^{-1/3} w(t) the condition is int w(t) t^{-2/3} dt = 0.  The script compares, for the theta level u and the
plain level (best class phases over 72 classes, as theta_level2.py), three weights:
  U1 = t^{-1/3}                                  (I != 0, the scan's profile)
  U2 = t^{-1/3} (1_{t<=1/2} - c 1_{t>1/2}),  c = 2^{-1/3}/(1 - 2^{-1/3})   (I = 0)
  U3 = t^{-1/3} (1_{t<=1/2} + c 1_{t>1/2})                                  (control: same pieces, I != 0)
printing the top of the class-compressed source Gram over the masked null; also for the higher Poisson levels
u^2 (x/|x|) (the conjugate cubic Gauss sum up to classes) and conj(x/|x|), whose poles may differ.

usage: python3 -I theta_level_profile.py B [threads]
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
nth = int(sys.argv[2]) if len(sys.argv) > 2 else 3
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
c = 2 ** (-1 / 3) / (1 - 2 ** (-1 / 3))
prof = {'U1 = t^-1/3 (I != 0)': t ** (-1 / 3),
        'U2 split, I = 0': t ** (-1 / 3) * np.where(t <= 0.5, 1.0, -c),
        'U3 split, I != 0': t ** (-1 / 3) * np.where(t <= 0.5, 1.0, c)}


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


print('B = L = %d: R=%d S=%d; c = %.3f   (%.0fs)' % (B, R, S, c, time.time() - t0), flush=True)
xang = (SA + SB * np.exp(2j * np.pi / 3)) / np.abs(SA + SB * np.exp(2j * np.pi / 3))
for lname, lv in (('theta u', u), ('plain', np.ones(S, complex)), ('u^2(x/|x|)', u ** 2 * xang),
                  ('conj(x/|x|)', np.conj(xang))):
    print('  %-12s %s' % (lname, ';  '.join('%s: %.3f' % (pn, top_ratio(lv * p)) for pn, p in prof.items())),
          flush=True)
print('done in %.0fs' % (time.time() - t0))
