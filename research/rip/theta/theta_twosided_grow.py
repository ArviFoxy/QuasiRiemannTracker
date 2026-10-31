"""The two-sided test with families that grow: more row twists, twisted source thetas, several source profiles.

Row family V(M), as in theta_twosided_free.py: the row thetas G6(z) and the plain characters on classes mod 36 with
profiles (N z/B)^{-j/2}, j < J, and for every twist m (a source with N(m) <= M) the shapes G6 conj chi_z(m),
chi_z(m), conj chi_z(m) on the 6 unit classes, j < J.
Source family P(M', betas):
  base     conj g6(x) N(x)^{-beta} and g6(x) N(x)^{-beta} on cells (x mod 4, x mod 9, parity of omega(x)), each beta;
  twisted  for every twist m with N(m) <= M': b(x) (x/m)_6^{+-1} and conj b(x) (x/m)_6^{-+1} with the class-signed
           source theta b(x) = conj g6(x) lam3(x) eps(x) N(x)^{-1/3} (theta_util.class_signed_fit), and the plain
           characters (x/m)_6^{+-1}, each on the 12 classes of x mod 4.  The order of the symbol is (x/m): reciprocity
           moves the other order into the classes mod 4.
The operators are applied matrix-free through the compiled kernel, one forward and one adjoint pass per product:
  v -> P_P^perp E^H (1 - Q_V Q_V^H) E P_P^perp v,
so a family costs nothing to precompute.  Two controls:
  random spans  E off random row and source spans of the same dimensions;
  masked null   the masked random matrix (i.i.d. phases on E's zero pattern, kernel mode 1) off the SAME spans V, P.
The masked null is the right edge: E is zero where a row and a source share a prime, which puts its bulk edge about
4.5% below the Marchenko-Pastur formula (sqrt((R - dV)/S) + sqrt((S - dP)/S))^2, also printed.  Row and source Gauss
sums are cached in $SCRATCH (theta_util.scratch_path).

THETA_ROWCONJ=1 adds the twisted row thetas with the other conjugation, G chi_z(m), to V (the Lean statement removes
every power chi_z(m)^k).
Order 3 (last argument 3): the cubic matrix E^2 (kernel mode 2) with cubic Gauss sums of rows and sources (twisted
multiplicativity, as theta_pairs.py), source profile N^{-1/6}, twisted characters (x/m)_3 = (x/m)_6^2; the
class-signed source theta is replaced by conj g3(x) N(x)^{-1/6} on the classes mod 4.

usage: python3 -I theta_twosided_grow.py B L CONFIGS [J] [threads] [order]
  CONFIGS is a ';'-separated list of M,M'[,beta:beta:...], e.g. "30,0;100,0;300,0;300,30;300,100,0.3333333:0.2:0.5"
  (betas default to 1/2 - 1/order: 1/3 for the sextic matrix, 1/6 for the cubic one).
"""
import os, sys, math, time
sys.dont_write_bytecode = True
os.environ.setdefault('OMP_NUM_THREADS', '1')
os.environ.setdefault('OPENBLAS_NUM_THREADS', '2')
import numpy as np
from scipy.sparse.linalg import eigsh, LinearOperator

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import theta_core as tc          # noqa: E402
import theta_ckernel as ck       # noqa: E402
import theta_util as tu          # noqa: E402

B = int(sys.argv[1]); L = int(sys.argv[2])
J = int(sys.argv[4]) if len(sys.argv) > 4 else 2
nth = int(sys.argv[5]) if len(sys.argv) > 5 else 3
qord = int(sys.argv[6]) if len(sys.argv) > 6 else 6
assert qord in (6, 3)
kk = 6 // qord                       # character power: chi_z^kk
modeE = 0 if qord == 6 else 2        # kernel mode of the matrix itself
beta0 = 0.5 - 1.0 / qord
configs = []
for item in sys.argv[3].split(';'):
    f = item.split(',')
    betas = [float(t) for t in f[2].split(':')] if len(f) > 2 else [beta0]
    configs.append((int(f[0]), int(f[1]), betas))
t0 = time.time()
Tb = tc.build_tables(B, L)
R, S, ID, pc, zo, rows = Tb.R, Tb.S, Tb.ID, tc.pc, tc.zo, Tb.rows
Ff = tu.free_namespace(Tb)
sym = tc.sym


def row_generator(i, cache={}):
    """theta_core.build's generator: split primes through ppcore, inert primes by brute force over F_{q^2}."""
    if i in cache:
        return cache[i]
    if i < ID.ns:
        val = Ff.generator(i)
    else:
        q = int(ID.inert_q[i - ID.ns])
        pr = zo.Prime(q)
        tot = 0j
        for aa in range(q):
            for bb in range(q):
                k = pr.sym((aa, bb))
                if k is not None:
                    tot += np.exp(2j * np.pi * k / 6) * np.exp(2j * np.pi * bb / q)
        val = dict(a=q, b=0, G=tot / q, prime=pr)
    cache[i] = val
    return val


ZETA6 = np.exp(2j * np.pi * np.arange(6) / 6)


def prime_gauss(i, cache={}):
    """generator dict of prime ideal i with the Gauss sum of chi^kk (theta_pairs.genk); kk = 1 agrees with
    theta_core.build's generator."""
    if i in cache:
        return cache[i]
    if i < ID.ns:
        p, r = ID.split_pr(np.array([i]))
        p = int(p[0]); r = int(r[0])
        a, b = pc.primary_generator(p, r)
        x = np.arange(1, p, dtype=np.int64)
        code = pc.sym_codes(np.array([p]), np.array([r]), x, np.zeros_like(x))[0]
        G = np.sum(ZETA6[(kk * code.astype(np.int64)) % 6] * np.exp(-2j * np.pi * ((b * x) % p) / p)) / math.sqrt(p)
        val = dict(a=a, b=b, G=G, prime=zo.Prime(p, (a, b)))
    else:
        q = int(ID.inert_q[i - ID.ns])
        pr = zo.Prime(q)
        tot = 0j
        for aa in range(q):
            for bb in range(q):
                c = pr.sym((aa, bb))
                if c is not None:
                    tot += ZETA6[(kk * c) % 6] * np.exp(2j * np.pi * bb / q)
        val = dict(a=q, b=0, G=tot / q, prime=pr)
    cache[i] = val
    return val


def gauss_product(gens):
    g = 1 + 0j
    for gi in gens:
        g *= gi['G']
    for a_ in range(len(gens)):
        for b_ in range(a_ + 1, len(gens)):
            g *= (sym(gens[b_]['prime'], (gens[a_]['a'], gens[a_]['b'])) *
                  sym(gens[a_]['prime'], (gens[b_]['a'], gens[b_]['b']))) ** kk
    return g


key = tu.scratch_path('gauss_B%d_L%d.npz' % (B, L) if qord == 6 else 'gauss_B%d_L%d_q%d.npz' % (B, L, qord))
if qord != 6 and not os.path.exists(key):
    Gsrc = np.zeros(S, complex); utw = np.zeros((S, 6), complex); nprime = np.zeros(S, int)
    for j, (a, b, n) in enumerate(zip(Tb.SA, Tb.SB, Tb.SN)):
        gens = [prime_gauss(i) for i in tu.source_prime_ids(Ff, a, b, n)]
        Gsrc[j] = gauss_product(gens); nprime[j] = len(gens)
        for k, u in enumerate(pc.UNITS):
            v = 1 + 0j
            for gi in gens:
                v *= sym(gi['prime'], u)
            utw[j, k] = v
    print('  source Gauss sums of order %d (%.0fs)' % (qord, time.time() - t0), flush=True)
    Grow = np.zeros(R, complex); gen = np.zeros((R, 2), np.int64); ut = np.zeros((R, 6), complex)
    for zi in range(R):
        gens = [prime_gauss(int(i)) for i in rows['PID'][zi] if i >= 0]
        x = (1, 0)
        for gi in gens:
            x = zo.mul(x, (gi['a'], gi['b']))
        Grow[zi] = gauss_product(gens); gen[zi] = x
        for k, u in enumerate(pc.UNITS):
            v = 1 + 0j
            for gi in gens:
                v *= sym(gi['prime'], u)
            ut[zi, k] = v
    np.savez(key, Grow=Grow, gen=gen, ut=ut, Gsrc=Gsrc, utw=utw, nprime=nprime)
    print('  row Gauss sums of order %d (%.0fs); cached' % (qord, time.time() - t0), flush=True)
if os.path.exists(key):
    d = np.load(key)
    Grow, gen, ut, Gsrc, utw, nprime = d['Grow'], d['gen'], d['ut'], d['Gsrc'], d['utw'], d['nprime']
    print('  Gauss sums from the cache %s' % os.path.basename(key), flush=True)
else:
    sd = tu.source_data(Ff)
    Gsrc, utw, nprime = sd['Gsrc'], sd['utw'], sd['nprime']
    print('  source Gauss sums (%.0fs)' % (time.time() - t0), flush=True)
    Grow = np.zeros(R, complex); gen = np.zeros((R, 2), np.int64); ut = np.zeros((R, 6), complex)
    for zi in range(R):
        gens = [row_generator(int(i)) for i in rows['PID'][zi] if i >= 0]
        g = 1 + 0j; x = (1, 0)
        for gi in gens:
            g *= gi['G']; x = zo.mul(x, (gi['a'], gi['b']))
        for a_ in range(len(gens)):
            for b_ in range(a_ + 1, len(gens)):
                g *= (sym(gens[b_]['prime'], (gens[a_]['a'], gens[a_]['b'])) *
                      sym(gens[a_]['prime'], (gens[b_]['a'], gens[b_]['b'])))
        Grow[zi] = g; gen[zi] = x
        for k, u in enumerate(pc.UNITS):
            v = 1 + 0j
            for gi in gens:
                v *= sym(gi['prime'], u)
            ut[zi, k] = v
    np.savez(key, Grow=Grow, gen=gen, ut=ut, Gsrc=Gsrc, utw=utw, nprime=nprime)
    print('  row Gauss sums (%.0fs); cached' % (time.time() - t0), flush=True)
K = ck.Kernel(Tb.T, Tb.LOC, nthreads=nth)

# row classes
c36 = ((gen[:, 0] % 4) * 4 + gen[:, 1] % 4) * 81 + (gen[:, 0] % 9) * 9 + gen[:, 1] % 9
unit = (np.rint(ut[:, 3].real) > 0) * 3 + np.rint(np.angle(ut[:, 1]) / (2 * np.pi / 3)).astype(int) % 3
prof = [(rows['N'].astype(float) / B) ** (-j / 2) for j in range(J)]
# source classes and the class-signed source theta (theta_util.src_class_data, lam3)
SA, SB, SN = Tb.SA, Tb.SB, Tb.SN.astype(float)
cell = (((SA % 4) * 4 + SB % 4) * 81 + (SA % 9) * 9 + SB % 9) * 2 + nprime % 2
c4 = (SA % 4) * 4 + (SB % 4)
odd = utw[:, 3].real < 0
parsign = np.where(odd & (nprime % 2 == 1), -1.0, 1.0)
if qord == 6:
    bsig = np.conj(Gsrc) * tu.lam3(Ff, 0, -1) * parsign * SN ** (-1.0 / 3)
else:
    bsig = np.conj(Gsrc) * SN ** (-beta0)

order = np.argsort(SN, kind='stable')
Mmax = max(c[0] for c in configs); Mpmax = max(c[1] for c in configs)
twists = [int(j) for j in order if SN[j] <= max(Mmax, Mpmax)]
print('B=%d: R=%d S=%d; order %d; %d twists with N(m) <= %d   (%.0fs)' % (B, R, S, qord, len(twists),
                                                                          max(Mmax, Mpmax), time.time() - t0),
      flush=True)
# row side: columns E e_m = chi_z(m)
Ecol = np.zeros((R, len(twists)), complex)
for st in range(0, len(twists), 8):
    blk = twists[st:st + 8]
    V = np.zeros((S, len(blk)), complex)
    V[blk, np.arange(len(blk))] = 1
    Ecol[:, st:st + len(blk)] = K.forward(V, mode=modeE)
# source side: x -> (x/m)_6 from the symbol table rows of m's prime ideals
uid = Tb.uid
srcchar = np.zeros((len(twists), S), complex)
for t, j in enumerate(twists):
    ids = tu.source_prime_ids(Ff, SA[j], SB[j], SN[j])
    pos = np.searchsorted(uid, ids)
    assert np.all(pos < len(uid)) and np.all(uid[pos] == ids), 'twist prime not among the row primes'
    codes = np.zeros(S, np.int64); zero = np.zeros(S, bool)
    for p_ in pos:
        row = Tb.T[p_].astype(np.int64)
        zero |= (row & 0x40) != 0
        codes += row & 7
    srcchar[t] = np.where(zero, 0, np.exp(2j * np.pi * (kk * codes % 6) / 6))


def orth(X):
    """orthonormal basis of the column span.  QR by default; with THETA_LOWMEM=1 a symmetric orthogonalization through
    the Gram matrix (two passes), which needs about one copy of X less (for B = 2e5)."""
    if os.environ.get('THETA_LOWMEM') != '1':
        Q, Rr = np.linalg.qr(X)
        d = np.abs(np.diag(Rr))
        return Q[:, d > 1e-8 * d.max()]
    for _ in range(2):
        G = X.conj().T @ X
        w, V = np.linalg.eigh((G + G.conj().T) / 2)
        keep = w > 1e-14 * w.max()
        X = X @ (V[:, keep] / np.sqrt(w[keep]))
    return X


def row_family(M):
    cols = [tu.class_span(c36, Grow * p) for p in prof] + [tu.class_span(c36, p.astype(complex)) for p in prof]
    for t, j in enumerate(twists):
        if SN[j] > M:
            break
        e = Ecol[:, t]
        for p in prof:
            cols += [tu.class_span(unit, Grow * np.conj(e) * p), tu.class_span(unit, e * p),
                     tu.class_span(unit, np.conj(e) * p)]
            if os.environ.get('THETA_ROWCONJ') == '1':      # the other conjugation G chi_z(m) (the power k = q - 1)
                cols.append(tu.class_span(unit, Grow * e * p))
    return orth(np.concatenate(cols, axis=1))


def source_family(Mp, betas):
    cols = []
    for be in betas:
        cols += [tu.class_span(cell, np.conj(Gsrc) * SN ** (-be)), tu.class_span(cell, Gsrc * SN ** (-be))]
    for t, j in enumerate(twists):
        if SN[j] > Mp:
            break
        ch = srcchar[t]
        cols += [tu.class_span(c4, bsig * ch), tu.class_span(c4, bsig * np.conj(ch)),
                 tu.class_span(c4, np.conj(bsig) * ch), tu.class_span(c4, np.conj(bsig) * np.conj(ch)),
                 tu.class_span(c4, ch), tu.class_span(c4, np.conj(ch))]
    return orth(np.concatenate(cols, axis=1))


def top(QV=None, QP=None, k=4, mode=None):
    mode = modeE if mode is None else mode
    def mv(v):
        v = np.asarray(v).ravel().astype(complex)
        if QP is not None:
            v = v - QP @ (QP.conj().T @ v)
        y = K.forward(v[:, None], mode=mode, seed=7)[:, 0]
        if QV is not None:
            y = y - QV @ (QV.conj().T @ y)
        w = K.adjoint(y[:, None], mode=mode, seed=7)[:, 0]
        if QP is not None:
            w = w - QP @ (QP.conj().T @ w)
        return w
    op = LinearOperator((S, S), dtype=complex, matvec=mv)
    v0 = np.random.default_rng(12345).standard_normal(S) + 0j
    w = eigsh(op, k=k, which='LA', return_eigenvectors=False, tol=1e-5, v0=v0)
    return np.sort(w)[::-1] / S


def edge(dr, ds):
    return (math.sqrt((R - dr) / S) + math.sqrt((S - ds) / S)) ** 2


rng = np.random.default_rng(101)
print('full top %s   masked null %s   MP edge %.3f   (%.0fs)'
      % (np.round(top(), 3), np.round(top(mode=1), 3), edge(0, 0), time.time() - t0), flush=True)
for M, Mp, betas in configs:
    QV = row_family(M); QP = source_family(Mp, betas)
    dV, dP = QV.shape[1], QP.shape[1]
    tw = top(QV, QP)
    tnull = top(QV, QP, mode=1)
    del QV, QP
    QVr = orth(rng.standard_normal((R, dV)) + 1j * rng.standard_normal((R, dV)))
    QPr = orth(rng.standard_normal((S, dP)) + 1j * rng.standard_normal((S, dP)))
    trn = top(QVr, QPr)
    del QVr, QPr
    print('M=%d M\'=%d betas %s: dV %d (%.3f R), dP %d (%.3f S)\n    off both %s   masked null %s   random spans %s'
          '   MP edge %.3f   (%.0fs)'
          % (M, Mp, [round(b_, 3) for b_ in betas], dV, dV / R, dP, dP / S, np.round(tw, 3), np.round(tnull, 3),
             np.round(trn, 3), edge(dV, dP), time.time() - t0), flush=True)
print('done in %.0fs' % (time.time() - t0))
