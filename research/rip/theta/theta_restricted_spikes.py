"""Restricted twisted thetas (gcd sorting in the off-spike recursion): do they carry excess of their own?

de Faveri's gcd sorting restricts the source vector to multiples of d = gcd(b1, b2), so a corrected recursion has to
know whether the source theta restricted to multiples of a small d, f 1_{d|x}, and its twists carry excess beyond
their overlap with the unrestricted family.  The script prints, for split primes d of small norm and twists m:
  * |E (f_m 1_{d|x})|^2 / |f_m 1_{d|x}|^2 over the masked null (the restricted spike's own excess);
  * the same after projecting f_m 1_{d|x} off the span of the unrestricted twisted thetas f_m', N(m') <= Mfam
    (excess left once the unrestricted family is removed);
with f the class-signed source theta and f_m = f (x/m)^{+1}.

usage: python3 -I theta_restricted_spikes.py B [Dmax] [Mfam] [threads]
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
Dmax = int(sys.argv[2]) if len(sys.argv) > 2 else 40
Mfam = int(sys.argv[3]) if len(sys.argv) > 3 else 300
nth = int(sys.argv[4]) if len(sys.argv) > 4 else 2
t0 = time.time()
Tb = tc.build_tables(B, L, verbose=False)
R, S = Tb.R, Tb.S
Ff = tu.free_namespace(Tb)
d_ = np.load(tu.scratch_path('gauss_B%d_L%d.npz' % (B, L)))
Gsrc, utw, nprime = d_['Gsrc'], d_['utw'], d_['nprime']
K = ck.Kernel(Tb.T, Tb.LOC, nthreads=nth)
SN = Tb.SN.astype(float)
parsign = np.where((utw[:, 3].real < 0) & (nprime % 2 == 1), -1.0, 1.0)
f = np.conj(Gsrc) * tu.lam3(Ff, 0, -1) * parsign * SN ** (-1.0 / 3)
uid = Tb.uid
order = np.argsort(SN, kind='stable')


def char_of(j):
    ids = tu.source_prime_ids(Ff, Tb.SA[j], Tb.SB[j], Tb.SN[j])
    pos = np.searchsorted(uid, ids)
    codes = np.zeros(S, np.int64); zero = np.zeros(S, bool)
    for p_ in pos:
        r = Tb.T[p_].astype(np.int64); zero |= (r & 0x40) != 0; codes += r & 7
    return np.where(zero, 0, np.exp(2j * np.pi * (codes % 6) / 6)), ids


fam = []
for j in order:
    if SN[j] > Mfam:
        break
    ch, _ = char_of(j)
    fam.append(f * ch)
Q, Rr = np.linalg.qr(np.stack(fam, axis=1))
Q = Q[:, np.abs(np.diag(Rr)) > 1e-8 * np.abs(np.diag(Rr)).max()]
src_ids = [set(int(i) for i in tu.source_prime_ids(Ff, a, b, n)) for a, b, n in zip(Tb.SA, Tb.SB, Tb.SN)]


def ratio(v):
    e = np.linalg.norm(K.forward(v[:, None], mode=0)[:, 0]) ** 2
    n = np.mean([np.linalg.norm(K.forward(v[:, None], mode=1, seed=s)[:, 0]) ** 2 for s in (3, 4)])
    return e / n


print('B = L = %d: R=%d S=%d; unrestricted family N(m) <= %d, dim %d   (%.0fs)'
      % (B, R, S, Mfam, Q.shape[1], time.time() - t0), flush=True)
print('  untwisted theta f: %.3f;  f off the family: %.3f' % (ratio(f), ratio(f - Q @ (Q.conj().T @ f))), flush=True)
twists = [int(j) for j in order if SN[j] <= 13]
for j in order:
    n = int(SN[j])
    if n > Dmax:
        break
    if n < 7 or int(Tb.spf[n]) != n:
        continue
    _, dids = char_of(j)
    did = int(dids[0])
    mult = np.array([did in s for s in src_ids], float)
    out = []
    for tj in twists:
        ch, _ = char_of(tj)
        v = f * ch * mult
        voff = v - Q @ (Q.conj().T @ v)
        out.append('m=%d: %.3f / off %.3f (kept %.2f)' % (int(SN[tj]), ratio(v), ratio(voff),
                                                         np.linalg.norm(voff) ** 2 / np.linalg.norm(v) ** 2))
    print('  d with N(d) = %3d (%4d multiples):  %s' % (n, int(mult.sum()), ';  '.join(out)), flush=True)
print('done in %.0fs' % (time.time() - t0))
