"""Local spikes: does the (x/p)^{-1} twist of the source theta carry its excess on the rows divisible by p?

In the monotonicity step of the off-spike recursion (journal 2026-10-31), the row a of a smaller problem becomes the
row a*p, and chi_{ap}(x) = chi_a(x) chi_p(x).  So on the rows z = a p the image of f conj chi_p is the image of f at a
(restricted to x coprime to p):  E(f conj chi_p)(a p) = E_{p-free}(f)(a).  For f the source theta, the (x/p)^{-1}
twist should then carry the theta's excess on the rows divisible by p, a 1/N(p) fraction of the rows.  The script
prints, for split primes p of small norm, the energy per row of E(f conj chi_p) on the rows divisible by p and on
the others, each over the same for the masked random matrix (mode 1, mean of two seeds), and the same for f itself.

usage: python3 -I theta_local_spikes.py B order [Pmax] [threads]
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
Pmax = int(sys.argv[3]) if len(sys.argv) > 3 else 60
nth = int(sys.argv[4]) if len(sys.argv) > 4 else 1
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
pids = Tb.rows['PID']


def energies(v):
    out = []
    for mode, seed in ((modeE, 0), (1, 3), (1, 4)):
        out.append(np.abs(K.forward(v[:, None], mode=mode, seed=seed)[:, 0]) ** 2)
    return out[0], (out[1] + out[2]) / 2


eE, eN = energies(f)
print('order %d, B = L = %d: R=%d S=%d; source theta |Ef|^2 / null over all rows: %.3f   (%.0fs)'
      % (q, B, R, S, eE.sum() / eN.sum(), time.time() - t0), flush=True)
order = np.argsort(SN, kind='stable')
for j in order:
    n = int(SN[j])
    if n > Pmax:
        break
    if n < 7 or int(Tb.spf[n]) != n:
        continue
    ids = tu.source_prime_ids(Ff, Tb.SA[j], Tb.SB[j], Tb.SN[j])
    pos = np.searchsorted(uid, ids)
    row = Tb.T[pos[0]].astype(np.int64)
    zero = (row & 0x40) != 0
    ch = np.where(zero, 0, np.exp(2j * np.pi * (kk * (row & 7) % 6) / 6))
    div = np.array([int(ids[0]) in set(int(i) for i in pp if i >= 0) for pp in pids])
    out = []
    for name, v in (('(x/p)^-1', f * np.conj(ch)), ('(x/p)^+1', f * ch)):
        a, b = energies(v)
        out.append('%s: rows p|z %.3f, others %.3f' % (name, a[div].sum() / b[div].sum(), a[~div].sum() / b[~div].sum()))
    a, b = eE, eN
    print('  N(p) = %3d (%d rows divisible):  %s;  untwisted theta on the same rows %.3f'
          % (n, div.sum(), ';  '.join(out), a[div].sum() / b[div].sum()), flush=True)
print('done in %.0fs' % (time.time() - t0))
