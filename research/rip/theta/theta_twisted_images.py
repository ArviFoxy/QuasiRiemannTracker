"""Which row family contains the row images of the twisted source thetas?

For the matrix of order q (6: sextic E, 3: cubic E^2) and each twist m with N(m) <= M', the twisted source thetas
f_m^{+-}(x) = b(x) (x/m)^{+-1} (b = conj g(x) N(x)^{-(1/2-1/q)}, times the class phases for q = 6) have row images
Phi = E f.  The script prints the mean energy fraction of the normalized images in four row spans, each built from
the twists N(m) <= M with two profiles, against the random level dim/R:
  A  G conj chi_z(m), chi_z(m), conj chi_z(m) on the 6 unit classes          (theta_twosided_grow.py's V)
  B  A plus G chi_z(m) (the other conjugation)                                (THETA_ROWCONJ=1)
  C  the same three shapes on (z mod 9) x chi_z(-1)                            (THETA_TWCLS=9)
  D  B on (z mod 9) x chi_z(-1)                                               (C, D with THETA_IMG_MOD9=1)
  E  A plus conj G chi_z(m) and conj G conj chi_z(m) (the conjugate row theta, twisted)
plus the untwisted part (thetas and plain characters on classes mod 36) in every span.  Gauss sums come from the
cache that theta_twosided_grow.py writes.

usage: python3 -I theta_twisted_images.py B L M M' [order]
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

B = int(sys.argv[1]); L = int(sys.argv[2]); M = int(sys.argv[3]); Mp = int(sys.argv[4])
qord = int(sys.argv[5]) if len(sys.argv) > 5 else 6
kk = 6 // qord
modeE = 0 if qord == 6 else 2
t0 = time.time()
Tb = tc.build_tables(B, L, verbose=False)
R, S, rows = Tb.R, Tb.S, Tb.rows
Ff = tu.free_namespace(Tb)
key = tu.scratch_path('gauss_B%d_L%d.npz' % (B, L) if qord == 6 else 'gauss_B%d_L%d_q%d.npz' % (B, L, qord))
d = np.load(key)
Grow, gen, ut, Gsrc, utw, nprime = d['Grow'], d['gen'], d['ut'], d['Gsrc'], d['utw'], d['nprime']
K = ck.Kernel(Tb.T, Tb.LOC, nthreads=2)
SA, SB, SN = Tb.SA, Tb.SB, Tb.SN.astype(float)
c36 = ((gen[:, 0] % 4) * 4 + gen[:, 1] % 4) * 81 + (gen[:, 0] % 9) * 9 + gen[:, 1] % 9
unit6 = (np.rint(ut[:, 3].real) > 0) * 3 + np.rint(np.angle(ut[:, 1]) / (2 * np.pi / 3)).astype(int) % 3
cls9 = ((gen[:, 0] % 9) * 9 + gen[:, 1] % 9) * 2 + (np.rint(ut[:, 3].real) > 0)
prof = [(rows['N'].astype(float) / B) ** (-j / 2) for j in range(2)]
if qord == 6:
    parsign = np.where((utw[:, 3].real < 0) & (nprime % 2 == 1), -1.0, 1.0)
    bsig = np.conj(Gsrc) * tu.lam3(Ff, 0, -1) * parsign * SN ** (-1.0 / 3)
else:
    bsig = np.conj(Gsrc) * SN ** (-(0.5 - 1.0 / qord))
order = np.argsort(SN, kind='stable')
twists = [int(j) for j in order if SN[j] <= max(M, Mp)]
Ecol = np.zeros((R, len(twists)), complex)
for st in range(0, len(twists), 8):
    blk = twists[st:st + 8]
    V = np.zeros((S, len(blk)), complex)
    V[blk, np.arange(len(blk))] = 1
    Ecol[:, st:st + len(blk)] = K.forward(V, mode=modeE)
uid = Tb.uid
ID = Tb.ID


def src_char(j):
    ids = tu.source_prime_ids(Ff, SA[j], SB[j], SN[j])
    pos = np.searchsorted(uid, ids)
    codes = np.zeros(S, np.int64); zero = np.zeros(S, bool)
    for p_ in pos:
        row = Tb.T[p_].astype(np.int64)
        zero |= (row & 0x40) != 0
        codes += row & 7
    return np.where(zero, 0, np.exp(2j * np.pi * (kk * codes % 6) / 6))


def orth(X):
    Q, Rr = np.linalg.qr(X)
    dd = np.abs(np.diag(Rr))
    return Q[:, dd > 1e-8 * dd.max()]


def span(classes, conj_too, conjG=False):
    cols = [tu.class_span(c36, Grow * p) for p in prof] + [tu.class_span(c36, p.astype(complex)) for p in prof]
    for t, j in enumerate(twists):
        if SN[j] > M:
            break
        e = Ecol[:, t]
        for p in prof:
            cols += [tu.class_span(classes, Grow * np.conj(e) * p), tu.class_span(classes, e * p),
                     tu.class_span(classes, np.conj(e) * p)]
            if conj_too:
                cols.append(tu.class_span(classes, Grow * e * p))
            if conjG:
                cols += [tu.class_span(classes, np.conj(Grow) * e * p), tu.class_span(classes, np.conj(Grow * e) * p)]
    return orth(np.concatenate(cols, axis=1))


spans = {'A unit': span(unit6, False), 'B unit + conj': span(unit6, True),
         'E unit + conj G': span(unit6, False, True)}
if os.environ.get('THETA_IMG_MOD9') == '1':
    spans.update({'C mod 9': span(cls9, False), 'D mod 9 + conj': span(cls9, True)})
imgs = []
for t, j in enumerate(twists):
    if SN[j] > Mp:
        break
    ch = src_char(j)
    for sgn in (1, -1):
        v = bsig * (ch if sgn > 0 else np.conj(ch))
        u = K.forward(v[:, None], mode=modeE)[:, 0]
        imgs.append((int(SN[j]), sgn, u / np.linalg.norm(u)))
print('B=%d L=%d order %d: R=%d; row spans with twists N(m) <= %d; %d twisted source images (N(m) <= %d)   (%.0fs)'
      % (B, L, qord, R, M, len(imgs), Mp, time.time() - t0), flush=True)
for name, Q in spans.items():
    fr = np.array([float(np.linalg.norm(Q.conj().T @ u) ** 2) for _, _, u in imgs])
    plus = fr[[i for i, (_, s, _) in enumerate(imgs) if s > 0]].mean()
    minus = fr[[i for i, (_, s, _) in enumerate(imgs) if s < 0]].mean()
    print('  %-16s dim %5d (random %.3f): energy of the images (x/m)^+1 %.3f, (x/m)^-1 %.3f'
          % (name, Q.shape[1], Q.shape[1] / R, plus, minus), flush=True)
print('done in %.0fs' % (time.time() - t0))
