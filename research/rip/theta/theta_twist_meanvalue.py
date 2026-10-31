"""Twist-aspect mean values of the spike correlations of a Mellin-zero plain vector.

The corrected sieve subtracts sum_{N(m) <= mu} w_m |<lambda, f_m>|^2, f_m the twisted source thetas.  For the K-wall
this must stay below B^{1+gamma} ||lambda||^2, which needs the correlations at square-root size on average over the
twists:  sum_{m ~ H} |<lambda, f_m>|^2  ~  H ||lambda||^2  (no growth in H).  A theta loss in the twist aspect would
show as growth like H^{1/q} (journal, "Sil's inclusion monotonicity ...").

lambda = V(N(b)/L) is a plain smooth vector on [L/8, L] whose Mellin transform vanishes at three points around the
pole s0 = 1/2 + 1/q (as in theta_twist_conductor.py).  The control V0 is a single smooth bump (no zero).  For twists
m with N(m) in dyadic ranges [Bz, 2 Bz] the script prints

    R = mean_m |sum_b lambda_b g(b) chi_m(b)|^2 / ||lambda||^2      (g = Gauss sum, both orientations g and conj g),

the same for the control, for the plain vector itself (Hecke: no pole for m != 1), and for the masked null (i.i.d.
phases on the same zero pattern, applied to lambda * g).

usage: python3 -I theta_twist_meanvalue.py L order Bz1,Bz2,... [threads]
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

L = int(sys.argv[1]); q = int(sys.argv[2])
Bzs = [int(x) for x in sys.argv[3].split(',')]
nth = int(sys.argv[4]) if len(sys.argv) > 4 else 3
modeE = 0 if q == 6 else 2
s0 = 0.5 + 1.0 / q
zeros = [s0 - 0.03, s0, s0 + 0.04]
t0 = time.time()

yy = np.linspace(-3.0, 0.0, 30001)
tt = 2.0 ** yy


def bump(y, a, b):
    out = np.zeros_like(y)
    m = (y > a) & (y < b)
    out[m] = np.exp(-1.0 / ((y[m] - a) * (b - y[m])))
    return out


def mellin(f, s):
    return np.trapezoid(f * tt ** s * np.log(2.0), yy)


centres = [(-3.0, -1.5), (-2.25, -0.75), (-1.5, 0.0), (-2.6, -0.4)]
PH = np.array([bump(yy, a, b) for a, b in centres])
Mm = np.array([[mellin(PH[k], s) for k in range(1, 4)] for s in zeros])
rhs = -np.array([mellin(PH[0], s) for s in zeros])
Vz = np.concatenate([[1.0], np.linalg.solve(Mm, rhs)]) @ PH
V0 = bump(yy, -3.0, 0.0)


def onto(grid, t):
    out = np.zeros_like(t)
    m = (t > 0.125) & (t < 1.0)
    out[m] = np.interp(np.log2(t[m]), yy, grid)
    return out


print('order %d, sources N(b) <= %d; V: Mellin zeros at %s (V~(s0) = %.1e); control V0: V0~(s0) = %.3f'
      % (q, L, ', '.join('%.3f' % z for z in zeros), mellin(Vz, s0), mellin(V0, s0)), flush=True)
print('   twists N(m)      R   lam*g  lam*conj g  V0*g  V0*conj g   plain    null', flush=True)
cols = None
for Bz in Bzs:
    Tb = tc.build_tables(Bz, L, verbose=False)
    R = Tb.R
    if cols is None:
        cand = ([tu.scratch_path('srcgauss_q%d_L%d.npz' % (q, L)), tu.scratch_path('gauss_B%d_L%d_q%d.npz' % (L, L, q))]
                if q != 6 else [tu.scratch_path('gauss_B%d_L%d.npz' % (L, L)), tu.scratch_path('srcgauss_L%d.npz' % L)])
        d = np.load([c for c in cand if os.path.exists(c)][0])
        G = d['Gsrc']
        assert len(G) == Tb.S, (len(G), Tb.S)
        g = G / np.where(np.abs(G) > 1e-9, np.abs(G), 1)
        tsrc = Tb.SN.astype(float) / L
        lam, lam0 = onto(Vz, tsrc), onto(V0, tsrc)
        cols = np.stack([lam * g, lam * np.conj(g), lam0 * g, lam0 * np.conj(g), lam.astype(complex)], axis=1)
        nrm = np.sum(np.abs(cols) ** 2, axis=0)
    K = ck.Kernel(Tb.T, Tb.LOC, nthreads=nth)
    EV = K.forward(cols, mode=modeE)
    EN = K.forward(cols[:, :1], mode=1, seed=3)
    r = np.mean(np.abs(EV) ** 2, axis=0) / nrm
    rn = np.mean(np.abs(EN[:, 0]) ** 2) / nrm[0]
    print('  [%6d,%6d] %5d  %7.3f  %9.3f  %6.3f  %9.3f  %7.3f  %6.3f   (%.0fs)'
          % (Bz, 2 * Bz, R, r[0], r[1], r[2], r[3], r[4], rn, time.time() - t0), flush=True)
    del K, Tb
print('done in %.0fs' % (time.time() - t0))
