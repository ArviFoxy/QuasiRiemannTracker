"""Task B3 at sizes where E does not fit: the class-signed source theta by the compiled matrix-free kernel (theta_ckernel).

Builds only the symbol tables (theta_core.build_tables), the source Gauss sums (theta_util.free_namespace: the same primary
generators and Gauss sums as theta_core.build) and the 12-dim class-signed span of theta_mech_corner.py
   f(x) = A(x mod 4) * (3/x)_3 * parsign(x) * conj g~(x) * N(x)^(-1/3),
then, with E V computed by Kernel.forward (b <= 8 vectors per call, single precision):
  * the compressed matrix Q^*(E^*E)Q/R of the span, its top eigenvalue against random-phase spans with the same classes and profile;
  * the top right singular vector v0 of E (Lanczos on the kernel), the overlap |<f, v0>| and the left overlap |<E f, u0>|, u0 = E v0/s;
  * the kernel prediction sigma^2/R = fit * kappa * B^(-1/6) sum_x N(x)^(-2/3) (kappa, fit as in theta_mech_growth.py) against the
    measured excess (compressed top minus random-phase span).
It validates against the dense theta_mech_corner.py at B = 3000 and extends the check to B = 10^5 and beyond.

usage: python3 -I theta_mech_free.py B L [threads=3]
"""
import os, sys, math, time
sys.dont_write_bytecode = True
os.environ.setdefault('OMP_NUM_THREADS', '1')
os.environ.setdefault('OPENBLAS_NUM_THREADS', '1')
import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import theta_core as tc          # noqa: E402
import theta_ckernel as ck       # noqa: E402
import theta_util as tu          # noqa: E402

B = int(sys.argv[1]); L = int(sys.argv[2])
nth = int(sys.argv[3]) if len(sys.argv) > 3 else 3
KAPPA, FIT, V0N = 0.497, 0.893, 0.952
t0 = time.time()
Tb = tc.build_tables(B, L)
R, S = Tb.R, Tb.S
Ff = tu.free_namespace(Tb)
sd = tu.source_data(Ff)
sc = tu.src_class_data(Ff, sd)
print('source Gauss sums done (%.0fs); |g~| in [%.3f, %.3f]' % (time.time() - t0, np.abs(sd['Gsrc']).min(), np.abs(sd['Gsrc']).max()), flush=True)
K = ck.Kernel(Tb.T, Tb.LOC, nthreads=nth)
SN = Tb.SN.astype(float)
rng = np.random.default_rng(7)


def EQ_of(Q):
    return np.concatenate([K.forward(Q[:, i:i + 8]) for i in range(0, Q.shape[1], 8)], axis=1)


def compressed_top(base):
    X = tu.class_span(sc['c4'], base)
    X = X[:, np.linalg.norm(X, axis=0) > 1e-12]
    Xn = X / np.linalg.norm(X, axis=0, keepdims=True)
    EQ = EQ_of(Xn)
    M = EQ.conj().T @ EQ / R
    w, V = np.linalg.eigh((M + M.conj().T) / 2)
    o = np.argsort(-w)
    return w[o], Xn @ V[:, o[0]], Xn, V[:, o]


lam = None
print('top eigenvalues of E^H E / S (Lanczos on the kernel) ...', flush=True)
ev, vec = K.top(k=3, vectors=True, tol=1e-5, log=lambda s_: print(s_, flush=True))
v0 = vec[:, 0]
s0 = math.sqrt(ev[0] * S)
u0 = K.forward(v0.reshape(-1, 1))[:, 0] / s0
print('top s^2/S = %s  (%.0fs)' % (np.round(ev, 4), time.time() - t0), flush=True)
res = {}
for alpha in (0.2, 0.3, 1 / 3, 0.4):
    base = np.conj(sd['Gsrc']) * SN ** (-alpha) * tu.lam3(Ff, 0, -1) * sc['parsign']
    w, f, Xn, V = compressed_top(base)
    Ef = K.forward(f.reshape(-1, 1))[:, 0]
    ov = abs(np.vdot(v0, f)); ou = abs(np.vdot(u0, Ef)) / np.linalg.norm(Ef)
    tr = []
    for _ in range(3):
        Xr = tu.class_span(sc['c4'], np.exp(2j * np.pi * rng.random(S)) * SN ** (-alpha))
        Xr = Xr[:, np.linalg.norm(Xr, axis=0) > 1e-12]
        Xrn = Xr / np.linalg.norm(Xr, axis=0, keepdims=True)
        EQr = EQ_of(Xrn)
        Mr = EQr.conj().T @ EQr / R
        tr.append(np.linalg.eigvalsh((Mr + Mr.conj().T) / 2)[-1])
    res[alpha] = (w[0], np.mean(tr), ov, ou)
    print('alpha = %.3f: 12-dim class-signed span top s^2/R %s (random phases %.3f +- %.3f) ; |<f,v0>| = %.3f ; |<Ef,u0>| = %.3f   (%.0fs)' %
          (alpha, np.round(w[:3], 3), np.mean(tr), np.std(tr), ov, ou, time.time() - t0), flush=True)
a = 1 / 3
w1, tr1, ov1, ou1 = res[a]
exc = w1 - tr1
ID = Tb.ID
SNi = Tb.SN.astype(np.int64)
s23 = float(np.sum(SN ** (-2 / 3)))
pred = FIT * KAPPA * B ** (-1 / 6) * s23
sig2 = exc * R / V0N
thp = sig2 / math.sqrt(R * S)
top_pred = V0N * (sig2 + R) * (sig2 + S) / sig2 / S if thp > 1 else float('nan')
print('\nB = %d: sum N^-2/3 = %.2f ; kernel-predicted sigma^2/R = %.3f ; measured excess (compressed top - random span) = %.3f ; ratio %.3f' % (B, s23, pred, exc, exc / pred))
print('BBP from the measured excess: theta_span = %.3f ; predicted top s^2/S = %.3f ; observed %.4f' % (thp, top_pred, ev[0]))
print('max possible overlap^2 for theta = %.2f is %.3f ; observed |<f,v0>|^2 = %.3f' % (thp, (1 - 1 / thp ** 2) / (1 + 1 / thp) if thp > 1 else 0, ov1 ** 2))
print('\ndone in %.0fs' % (time.time() - t0))
