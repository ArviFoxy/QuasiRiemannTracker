"""The twist-aspect conductor of the Kubota series, measured from where smooth sums stop.

For a Dirichlet series with conductor Q, a smooth sum sum_b V(N(b)/X) a_b with no pole term is negligible once
X >> Q (its dual sum has length Q/X).  We measure that point for the twisted theta sums

    T_z(X) = sum_b u_b V(N(b)/X) chi_z(b),      u = conj(Gauss sum) (the source theta), chi_z = (./z)_q,

over twists z with N(z) in dyadic ranges [B_z, 2 B_z], and for the plain sums sum_b V(N(b)/X) chi_z(b) (Hecke
L-functions, conductor N(z)) as the calibration.  V is smooth on [1/8, 1] with Mellin zeros at the pole (three
zeros around s0 = 1/2 + 1/q, to absorb the finite-size offset seen in theta_pole_scan), so the residue term
X^{s0} tau(z) V~(s0) is removed and only the off-pole part is left.  The ratio printed is

    r(z-range, X) = mean_z |T_z(X)|^2 / ||v_X||^2,

about 1 while X << Q(z) and dropping fast once X >> Q(z).  If Q(z) ~ N(z) the theta and plain transitions sit at the
same X/N(z); if Q(z) ~ N(z)^2 the theta transition moves out like N(z)^2.

usage: python3 -I theta_twist_conductor.py L order Bz1,Bz2,... [threads]
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

# smooth weight on [1/8, 1]: V = sum_k c_k phi_k (bumps in log2 t), c_0 = 1, V~(s) = 0 at the three zeros
yy = np.linspace(-3.0, 0.0, 30001)
tt = 2.0 ** yy


def bump(y, a, b):
    out = np.zeros_like(y)
    m = (y > a) & (y < b)
    out[m] = np.exp(-1.0 / ((y[m] - a) * (b - y[m])))
    return out


centres = [(-3.0, -1.5), (-2.25, -0.75), (-1.5, 0.0), (-2.6, -0.4)]
PH = np.array([bump(yy, a, b) for a, b in centres])


def mellin(f, s):
    # int f(t) t^{s-1} dt = int f(2^y) 2^{ys} ln2 dy
    return np.trapezoid(f * tt ** s * np.log(2.0), yy)


Mm = np.array([[mellin(PH[k], s) for k in range(1, 4)] for s in zeros])
rhs = -np.array([mellin(PH[0], s) for s in zeros])
coef = np.concatenate([[1.0], np.linalg.solve(Mm, rhs)])
Vgrid = coef @ PH
print('order %d, sources N(b) <= %d; V = smooth on [1/8, 1] with Mellin zeros at %s; V~(s0) = %.2e, V~(1) = %.3f'
      % (q, L, ', '.join('%.3f' % z for z in zeros), mellin(Vgrid, s0), mellin(Vgrid, 1.0)), flush=True)


def V(t):
    out = np.zeros_like(t)
    m = (t > 0.125) & (t < 1.0)
    out[m] = np.interp(np.log2(t[m]), yy, Vgrid)
    return out


Xs = [L / 2 ** k for k in range(0, 11)]
G = None
for Bz in Bzs:
    Tb = tc.build_tables(Bz, L, verbose=False)
    R, S = Tb.R, Tb.S
    if G is None:
        d = np.load(tu.scratch_path('srcgauss_q%d_L%d.npz' % (q, L)) if q != 6 else
                    tu.scratch_path('gauss_B%d_L%d.npz' % (L, L)))
        G = d['Gsrc']
        assert len(G) == S, (len(G), S)
        u = np.conj(G) / np.where(np.abs(G) > 1e-9, np.abs(G), 1)
        SN = Tb.SN.astype(float)
    K = ck.Kernel(Tb.T, Tb.LOC, nthreads=nth)
    print('rows N(z) in [%d, %d]: R = %d   (%.0fs)' % (Bz, 2 * Bz, R, time.time() - t0), flush=True)
    print('      X      X/Bz     theta     plain      null', flush=True)
    for X in Xs:
        w = V(SN / X)
        nrm = np.sum(w ** 2)
        if nrm <= 0:
            continue
        cols = np.stack([u * w, w.astype(complex)], axis=1)
        EV = K.forward(cols, mode=modeE)
        EN = K.forward(cols[:, :1], mode=1, seed=3)
        r = np.mean(np.abs(EV) ** 2, axis=0) / nrm
        rn = np.mean(np.abs(EN[:, 0]) ** 2) / nrm
        print('%9.0f %8.2f %9.4f %9.4f %9.4f' % (X, X / Bz, r[0], r[1], rn), flush=True)
    del K, Tb
print('done in %.0fs' % (time.time() - t0))
