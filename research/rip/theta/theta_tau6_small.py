"""Is the source theta's row image the sextic theta function?  Small rows, long sources, and Broker-Hoffstein.

At rows of small norm and sources out to a large L, the residue L^{1/3} conj tau6(z) of the source sums should
dominate the noise row by row (journal, "The block outlier is a residue").  The script takes rows with
N(z) in [B, 2B] (B small, e.g. 100) and sources up to L, and for each of the 12 classes c of x mod 4 forms
  F_c(z) = sum_{x in class c} conj g6(x) lam3(x) eps(x) N(x)^{-1/3} (x/z)_6        (E applied to one class of the
                                                                                source theta, theta_util)
If every class carries the same residue vector, the 12 x R matrix [F_c(z)] is rank one up to noise: its singular
values, and the stability of the top right vector between sources up to L/3 and L, are printed.  The top right vector
is the estimate tau^(z) of conj tau6 on the rows (up to scale and conjugation).

Broker-Hoffstein (Math. Comp. 85 (2016), Conj. 5.7) predict, at prime pi, tau6(pi)^2 / tau6(1) =
zeta6^k(pi) g3~(pi) 3^l(pi) (norm-7 or norm-13 element)^(m, n), with k, l, m, n not described by a rule.  So:
  * the sixth power of tau^(pi)^2 g3~(pi)^(+-1) (one of the two conjugations) should have a constant phase;
  * |tau^(pi)|^2 should take a few discrete values, in ratios 3, 7, 13 and their products.
Both are printed for the split prime rows, with the cubic Gauss sum g3~(pi) computed as in theta_cfh.py.

usage: python3 -I theta_tau6_small.py B L
"""
import os, sys, math, time
sys.dont_write_bytecode = True
os.environ.setdefault('OMP_NUM_THREADS', '1')
import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import theta_core as tc          # noqa: E402
import theta_ckernel as ck       # noqa: E402
import theta_util as tu          # noqa: E402

B = int(sys.argv[1]); L = int(sys.argv[2])
t0 = time.time()
Tb = tc.build_tables(B, L)
R, S = Tb.R, Tb.S
ID, pc = Tb.ID, tc.pc
Ff = tu.free_namespace(Tb)
key = tu.scratch_path('srcgauss_L%d.npz' % L)
if os.path.exists(key):
    d = np.load(key)
    Gsrc, utw, nprime = d['Gsrc'], d['utw'], d['nprime']
else:
    sd = tu.source_data(Ff)
    Gsrc, utw, nprime = sd['Gsrc'], sd['utw'], sd['nprime']
    np.savez(key, Gsrc=Gsrc, utw=utw, nprime=nprime)
print('  source Gauss sums (%.0fs)' % (time.time() - t0), flush=True)
K = ck.Kernel(Tb.T, Tb.LOC, nthreads=2)
SN = Tb.SN.astype(float)
c4 = (Tb.SA % 4) * 4 + (Tb.SB % 4)
odd = utw[:, 3].real < 0
parsign = np.where(odd & (nprime % 2 == 1), -1.0, 1.0)
base = np.conj(Gsrc) * tu.lam3(Ff, 0, -1) * parsign * SN ** (-1.0 / 3)
classes = sorted(set(c4.tolist()))


def images(Lcut, mode=0, seed=0):
    cols = np.stack([base * ((c4 == c) & (SN <= Lcut)) for c in classes], axis=1)
    out = np.zeros((R, len(classes)), complex)
    for st in range(0, len(classes), 8):
        out[:, st:st + 8] = K.forward(cols[:, st:st + 8], mode=mode, seed=seed)
    return out.T                                       # classes x rows


res = {}
for Lc in (L // 3, L):
    M = images(Lc) / Lc ** (1.0 / 3)
    U, s, Vh = np.linalg.svd(M, full_matrices=False)
    res[Lc] = Vh[0]
    sn = np.mean([np.linalg.svd(images(Lc, 1, sd) / Lc ** (1.0 / 3), compute_uv=False) for sd in range(4)], axis=0)
    print('sources up to %d: singular values of the 12 x %d class-image matrix (/L^{1/3}): %s\n'
          '    masked null (mean of 4): %s' % (Lc, R, np.round(s, 3), np.round(sn, 3)), flush=True)
print('|<top right vector (L/3), top right vector (L)>|^2 = %.4f   (random level %.3f)'
      % (abs(np.vdot(res[L // 3], res[L])) ** 2, 1.0 / R), flush=True)
tau = res[L]
tau = tau / np.sqrt(np.mean(np.abs(tau) ** 2))

# split prime rows and their cubic Gauss sums (theta_cfh.g3_prime)
ZETA6 = np.exp(2j * np.pi * np.arange(6) / 6)
pids = Tb.rows['PID']
prime_rows, g3 = [], []
for zi in range(R):
    ids = [int(i) for i in pids[zi] if i >= 0]
    if len(ids) != 1 or ids[0] >= ID.ns:
        continue
    p, r = ID.split_pr(np.array([ids[0]]))
    p = int(p[0]); r = int(r[0])
    a, b = pc.primary_generator(p, r)
    x = np.arange(1, p, dtype=np.int64)
    code = pc.sym_codes(np.array([p]), np.array([r]), x, np.zeros_like(x))[0]
    G = np.sum(ZETA6[(2 * code.astype(np.int64)) % 6] * np.exp(-2j * np.pi * ((b * x) % p) / p)) / math.sqrt(p)
    prime_rows.append((zi, p)); g3.append(G)
g3 = np.array(g3)
zi = np.array([z for z, _ in prime_rows]); ps = np.array([p for _, p in prime_rows])
print('%d split prime rows (norms %s)' % (len(zi), sorted(set(ps.tolist()))), flush=True)
rng = np.random.default_rng(5)
for name, t in (('tau^', tau[zi]), ('conj tau^', np.conj(tau[zi]))):
    for sgn, gg in (('g3', g3), ('conj g3', np.conj(g3))):
        w = (t ** 2 * gg) ** 6
        R6 = abs(np.mean(w / np.abs(w)))
        print('  phase coherence |mean of unit (%s^2 %s)^6| = %.3f   (random phases: %.3f)'
              % (name, sgn, R6, abs(np.mean(np.exp(2j * np.pi * rng.random(len(w)))))), flush=True)
mag = np.abs(tau[zi]) ** 2
order = np.argsort(mag)
print('  |tau^(pi)|^2 on prime rows, sorted (mean 1 over all rows): %s' % np.round(mag[order], 2))
print('  ratios to the smallest: %s' % np.round(mag[order] / mag[order][0], 2))
print('done in %.0fs' % (time.time() - t0))
