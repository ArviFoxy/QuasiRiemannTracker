"""Which twists of the source theta carry a spike?  Energy of the twisted images against the masked null.

For the matrix of order q (6: E; 3: E^2, kernel mode 2) and the twists m with N(m) <= 30, the twisted source thetas
b(x) (x/m)^{+1} and b(x) (x/m)^{-1} (b as in theta_twosided_grow.py) are mapped to the rows, and |E f|^2 is divided by
the same for the masked random matrix (mean of 3 seeds).  In the residue picture the +1 twist is the residue at the
index zm, with strength decaying like N(m)^{-1/q}; the -1 twist is the index z m^{q-1}, where the theta coefficients
vanish, so it should sit at the null.  Gauss sums come from theta_twosided_grow.py's cache.

usage: python3 -I theta_twisted_norms.py B order
"""
import os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import numpy as np
import theta_core as tc, theta_ckernel as ck, theta_util as tu
B = L = int(sys.argv[1]); q = int(sys.argv[2]); kk = 6 // q; modeE = 0 if q == 6 else 2
Tb = tc.build_tables(B, L, verbose=False)
Ff = tu.free_namespace(Tb)
d = np.load(tu.scratch_path('gauss_B%d_L%d.npz' % (B, L) if q == 6 else 'gauss_B%d_L%d_q%d.npz' % (B, L, q)))
Gsrc, utw, nprime = d['Gsrc'], d['utw'], d['nprime']
K = ck.Kernel(Tb.T, Tb.LOC, nthreads=2)
SN = Tb.SN.astype(float)
if q == 6:
    parsign = np.where((utw[:, 3].real < 0) & (nprime % 2 == 1), -1.0, 1.0)
    b = np.conj(Gsrc) * tu.lam3(Ff, 0, -1) * parsign * SN ** (-1.0 / 3)
else:
    b = np.conj(Gsrc) * SN ** (-(0.5 - 1.0 / q))
uid = Tb.uid
order = np.argsort(SN, kind='stable')
tw = [int(j) for j in order if SN[j] <= 30]
rows = []
for j in tw:
    ids = tu.source_prime_ids(Ff, Tb.SA[j], Tb.SB[j], Tb.SN[j])
    pos = np.searchsorted(uid, ids)
    codes = np.zeros(Tb.S, np.int64); zero = np.zeros(Tb.S, bool)
    for p_ in pos:
        r = Tb.T[p_].astype(np.int64); zero |= (r & 0x40) != 0; codes += r & 7
    ch = np.where(zero, 0, np.exp(2j * np.pi * (kk * codes % 6) / 6))
    out = []
    for v in (b * ch, b * np.conj(ch)):
        e = np.linalg.norm(K.forward(v[:, None], mode=modeE)[:, 0]) ** 2
        n = np.mean([np.linalg.norm(K.forward(v[:, None], mode=1, seed=s)[:, 0]) ** 2 for s in range(3)])
        out.append(e / n)
    rows.append((int(SN[j]), out[0], out[1]))
print('order %d, B = L = %d: |E f_m|^2 / masked null for the twisted source thetas, (x/m)^+1 and (x/m)^-1:' % (q, B))
for n, a, c in rows:
    print('  N(m) = %4d:  +1 %.2f   -1 %.2f' % (n, a, c))
b0 = np.linalg.norm(K.forward(b[:, None], mode=modeE)[:, 0]) ** 2 / np.mean([np.linalg.norm(K.forward(b[:, None], mode=1, seed=s)[:, 0]) ** 2 for s in range(3)])
print('  untwisted source theta: %.2f' % b0)
