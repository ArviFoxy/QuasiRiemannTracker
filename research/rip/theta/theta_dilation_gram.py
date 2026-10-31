"""Are the dilated residues well-conditioned?  The correlation matrix of the twisted source images.

The twisted source theta f_m = f (x/m)^{+1} has row image Phi_m(z) = Phi(zm) (rowImage_twist_dilation), the residue
at the dilated index.  For Lambda_src the K-wall needs the Bessel constant of {Phi_m} on slot-selected rows; with an
amplifier this becomes twisted Rankin-Selberg sums sum_z psi(z) tau(zm) conj tau(zm'), whose psi = 1 part is a
Petersson Gram of dilated thetas.  This script prints the spectrum of the normalized Gram
C_{m,m'} = <Phi_m, Phi_m'> / (|Phi_m| |Phi_m'|) over all rows for the twists N(m) <= M (with the untwisted m = 1),
for E and for the masked random matrix (mode 1).  A top eigenvalue that stays O(1) as M grows means the family is
well-conditioned, so its Bessel constant is about its largest member.

usage: python3 -I theta_dilation_gram.py B order M1,M2,.. [threads]
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
Ms = [int(t) for t in sys.argv[3].split(',')]
nth = int(sys.argv[4]) if len(sys.argv) > 4 else 2
kk = 6 // q
modeE = 0 if q == 6 else 2
t0 = time.time()
Tb = tc.build_tables(B, L, verbose=False)
R, S = Tb.R, Tb.S
Ff = tu.free_namespace(Tb)
d = np.load(tu.scratch_path('gauss_B%d_L%d.npz' % (B, L) if q == 6 else 'gauss_B%d_L%d_q%d.npz' % (B, L, q)))
Gsrc, utw, nprime = d['Gsrc'], d['utw'], d['nprime']
K = ck.Kernel(Tb.T, Tb.LOC, nthreads=nth)
SN = Tb.SN.astype(float)
if q == 6:
    parsign = np.where((utw[:, 3].real < 0) & (nprime % 2 == 1), -1.0, 1.0)
    f = np.conj(Gsrc) * tu.lam3(Ff, 0, -1) * parsign * SN ** (-1.0 / 3)
else:
    f = np.conj(Gsrc) * SN ** (-(0.5 - 1.0 / q))
uid = Tb.uid
order = np.argsort(SN, kind='stable')
tw = [int(j) for j in order if SN[j] <= max(Ms)]
cols = []
for j in tw:
    ids = tu.source_prime_ids(Ff, Tb.SA[j], Tb.SB[j], Tb.SN[j])
    pos = np.searchsorted(uid, ids)
    codes = np.zeros(S, np.int64); zero = np.zeros(S, bool)
    for p_ in pos:
        r = Tb.T[p_].astype(np.int64); zero |= (r & 0x40) != 0; codes += r & 7
    cols.append(f * np.where(zero, 0, np.exp(2j * np.pi * (kk * codes % 6) / 6)))
V = np.stack(cols, axis=1)
print('order %d, B = L = %d: R=%d S=%d; %d twisted source thetas with N(m) <= %d   (%.0fs)'
      % (q, B, R, S, V.shape[1], max(Ms), time.time() - t0), flush=True)
for name, mode in (('E', modeE), ('masked null', 1)):
    Phi = np.zeros((R, V.shape[1]), complex)
    for st in range(0, V.shape[1], 8):
        Phi[:, st:st + 8] = K.forward(V[:, st:st + 8], mode=mode, seed=5)
    nrm = np.linalg.norm(Phi, axis=0)
    C = (Phi / nrm).conj().T @ (Phi / nrm)
    out = []
    for M in Ms:
        k = int(np.sum(SN[tw] <= M))
        w = np.linalg.eigvalsh((C[:k, :k] + C[:k, :k].conj().T) / 2)
        out.append('N(m) <= %d (%d twists): top %.3f, 2nd %.3f, mean |off-diag|^2 %.4f'
                   % (M, k, w[-1], w[-2] if k > 1 else 0, (np.sum(np.abs(C[:k, :k]) ** 2) - k) / max(1, k * (k - 1))))
    print('  %s:\n    %s' % (name, '\n    '.join(out)), flush=True)
    print('    random level of |off-diag|^2: %.1e (1/R)' % (1.0 / R), flush=True)
print('done in %.0fs' % (time.time() - t0))
