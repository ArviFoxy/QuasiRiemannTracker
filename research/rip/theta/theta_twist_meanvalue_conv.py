"""Twist-aspect spike correlations of a convolution of two plain factors (the K-wall's leaf shape).

lambda = U1 * U2 on the source set: lambda_b = sum_{b = b1 b2} U1(N(b1)/X1) U2(N(b2)/X2).  Sources have squarefree
norm, so the divisors of b are the subsets of the primes of N(b), and lambda_b = F(N(b)) with
F(n) = sum_{d | n} U1(d/X1) U2(n/(d X2)).  The correlations with the twisted thetas are bilinear Kubota sums with a
pole in each variable, so each factor should need its own Mellin zero.  Variants: both factors with Mellin zeros
(zz), only the first (zb), only the second (bz), neither (bb).  Printed per dyadic twist range:

    R = mean_m |sum_b lambda_b conj(g(b)) chi_m(b)|^2 / ||lambda||^2      (the spike orientation, see
                                                                          theta_twist_meanvalue.py)

with the masked null (i.i.d. phases) for the zz vector.

usage: python3 -I theta_twist_meanvalue_conv.py L order X1 Bz1,Bz2,... [threads]      (X2 = L / X1)
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

L = int(sys.argv[1]); q = int(sys.argv[2]); X1 = float(sys.argv[3]); X2 = L / X1
Bzs = [int(x) for x in sys.argv[4].split(',')]
nth = int(sys.argv[5]) if len(sys.argv) > 5 else 3
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


def divisors_of_sqfree(n, spf):
    ps = []
    while n > 1:
        p = int(spf[n]); ps.append(p); n //= p
    ds = [1]
    for p in ps:
        ds = ds + [d * p for d in ds]
    return ds


print('order %d, sources N(b) <= %d, X1 = %.0f, X2 = %.0f; zero weights: Mellin zeros at %s' %
      (q, L, X1, X2, ', '.join('%.3f' % z for z in zeros)), flush=True)
print('   twists N(m)      R      zz       zb       bz       bb   mu*bb     null', flush=True)
cols = None
for Bz in Bzs:
    Tb = tc.build_tables(Bz, L, verbose=False)
    if cols is None:
        cand = ([tu.scratch_path('srcgauss_q%d_L%d.npz' % (q, L)), tu.scratch_path('gauss_B%d_L%d_q%d.npz' % (L, L, q))]
                if q != 6 else [tu.scratch_path('gauss_B%d_L%d.npz' % (L, L)), tu.scratch_path('srcgauss_L%d.npz' % L)])
        dd = np.load([c for c in cand if os.path.exists(c)][0])
        G = dd['Gsrc']
        assert len(G) == Tb.S, (len(G), Tb.S)
        g = G / np.where(np.abs(G) > 1e-9, np.abs(G), 1)
        if q == 6 and os.environ.get('THETA_CANON') == '1':
            # canonical normalization: undo mu(c) on the classes N(c) = 7 mod 12 (see theta_twist_meanvalue.py)
            g = g * np.where(Tb.SN % 12 == 7, (-1.0) ** dd['nprime'], 1.0)
        SN = Tb.SN.astype(np.int64)
        lam = {}
        for k1, w1 in (('z', Vz), ('b', V0)):
            for k2, w2 in (('z', Vz), ('b', V0)):
                F = np.zeros(len(SN))
                for i, n in enumerate(SN):
                    ds = np.array(divisors_of_sqfree(int(n), Tb.spf), dtype=float)
                    F[i] = np.sum(onto(w1, ds / X1) * onto(w2, (n / ds) / X2))
                lam[k1 + k2] = F
        # Moebius block times plain block (the mollified detector's shape): sum_{d | n} mu(d) V0(d/X1) V0(n/(d X2))
        def nfac(d):
            k = 0
            while d > 1:
                p = int(Tb.spf[d]); d //= p; k += 1
            return k
        F = np.zeros(len(SN))
        for i, n in enumerate(SN):
            ds = divisors_of_sqfree(int(n), Tb.spf)
            mus = np.array([(-1.0) ** nfac(d) for d in ds])
            dd = np.array(ds, dtype=float)
            F[i] = np.sum(mus * onto(V0, dd / X1) * onto(V0, (n / dd) / X2))
        lam['mb'] = F
        cols = np.stack([lam[k] * np.conj(g) for k in ('zz', 'zb', 'bz', 'bb', 'mb')], axis=1)
        nrm = np.sum(np.abs(cols) ** 2, axis=0)
        print('  convolution weights built (%.0fs); support fractions %s' %
              (time.time() - t0, ', '.join('%.2f' % np.mean(lam[k] != 0) for k in ('zz', 'zb', 'bz', 'bb', 'mb'))),
              flush=True)
    K = ck.Kernel(Tb.T, Tb.LOC, nthreads=nth)
    EV = K.forward(cols, mode=modeE)
    EN = K.forward(cols[:, :1], mode=1, seed=3)
    r = np.mean(np.abs(EV) ** 2, axis=0) / nrm
    rn = np.mean(np.abs(EN[:, 0]) ** 2) / nrm[0]
    print('  [%6d,%6d] %5d  %7.3f  %7.3f  %7.3f  %7.3f  %7.3f  %7.3f   (%.0fs)'
          % (Bz, 2 * Bz, Tb.R, r[0], r[1], r[2], r[3], r[4], rn, time.time() - t0), flush=True)
    del K, Tb
print('done in %.0fs' % (time.time() - t0))
