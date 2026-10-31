"""Shared helpers for the mechanism probes (theta_mech_*.py): source Gauss sums, row/source class data, cached top
singular pairs, small-source column blocks.  Everything is built on theta_core.build; nothing here rebuilds E.

  source_data(F)      -> dict: Gsrc (source Gauss sums g~(x), unimodular), utw (S, 6) unit twists chi_x(u), nprime (number of
                         prime factors), mu ((-1)^omega), cls4 ((a mod 4, b mod 4) as an index 0..15), primes (list of prime
                         generator dicts per source)
  row_data(F)         -> dict: gen (R, 2) z_* = product of primary prime generators, cls4, par (parity of omega(z)), nprime,
                         chim1 (chi_z(-1) as +-1), chiw (chi_z(omega) exponent 0..2), isprime
  top_pairs(F, k)     -> (s, U, Vh) top-k singular triples of F.E, cached in $SCRATCH (set SCRATCH to a scratch directory)
  block_columns(F, M) -> indices of the sources with N(x) <= M sorted by norm

The cache is keyed by (B, L, k) only: delete the files when theta_core changes.
"""
import os, sys, math
import numpy as np
from scipy.sparse.linalg import svds

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
SCRATCH = os.environ.get('SCRATCH', os.path.join(HERE, '.scratch'))


def scratch_path(name):
    os.makedirs(SCRATCH, exist_ok=True)
    return os.path.join(SCRATCH, name)


def source_prime_ids(F, a, b, n):
    """prime-ideal ids of the (squarefree-norm) source a + b w of norm n."""
    ID, spf = F.ID, F.spf
    ids = []
    n = int(n)
    while n > 1:
        p = int(spf[n]); n //= p
        k = int(ID.pidx[p]); r0 = int(ID.split_r[k])
        r = r0 if (int(a) + int(b) * r0) % p == 0 else p - 1 - r0
        ids.append(ID.ideal_id(p, r))
    return ids


def source_data(F):
    """source Gauss sums by twisted multiplicativity over the prime factors (as theta_srcspike.py), unit twists, classes."""
    S = F.S
    sym = F.sym
    Gsrc = np.zeros(S, complex)
    utw = np.zeros((S, 6), complex)
    nprime = np.zeros(S, int)
    primes = []
    for j, (a, b, n) in enumerate(zip(F.SA, F.SB, F.SN)):
        ids = source_prime_ids(F, a, b, n)
        gens = [F.generator(i) for i in ids]
        g = 1 + 0j
        for gi in gens:
            g *= gi['G']
        for x_ in range(len(gens)):
            for y_ in range(x_ + 1, len(gens)):
                g *= sym(gens[y_]['prime'], (gens[x_]['a'], gens[x_]['b'])) * sym(gens[x_]['prime'], (gens[y_]['a'], gens[y_]['b']))
        Gsrc[j] = g
        for kk, u in enumerate(F.pc.UNITS):
            v = 1 + 0j
            for gi in gens:
                v *= sym(gi['prime'], u)
            utw[j, kk] = v
        nprime[j] = len(ids)
        primes.append(gens)
    cls4 = (np.asarray(F.SA) % 4) * 4 + (np.asarray(F.SB) % 4)
    return dict(Gsrc=Gsrc, utw=utw, nprime=nprime, mu=(-1.0) ** nprime, cls4=cls4, primes=primes)


def row_data(F):
    zo = F.zo
    R = F.R
    gen = np.zeros((R, 2), np.int64)
    nprime = np.zeros(R, int)
    for zi in range(R):
        x = (1, 0)
        for pid in F.rows['PID'][zi]:
            if pid >= 0:
                g = F.generator(int(pid)); x = zo.mul(x, (g['a'], g['b'])); nprime[zi] += 1
        gen[zi] = x
    cls4 = (gen[:, 0] % 4) * 4 + (gen[:, 1] % 4)
    ut = F.unit_tw
    chim1 = np.rint(ut[:, 3].real).astype(int)                       # chi_z(-1) = +-1
    chiw = np.rint(np.angle(ut[:, 1]) / (2 * np.pi / 3)).astype(int) % 3   # chi_z(omega) = omega^chiw
    return dict(gen=gen, cls4=cls4, nprime=nprime, par=nprime % 2, chim1=chim1, chiw=chiw, isprime=(nprime == 1))


def top_pairs(F, k=8, tag=''):
    """top-k singular triples (s, U, Vh) of F.E sorted by decreasing s, cached under $SCRATCH (tag e.g. 'B10000_L10000')."""
    key = scratch_path('top_%s_R%d_S%d_k%d.npz' % (tag, F.R, F.S, k))
    if os.path.exists(key):
        d = np.load(key)
        return d['s'], d['U'], d['Vh']
    U, s, Vh = svds(F.E, k=k, random_state=0)
    o = np.argsort(-s)
    s, U, Vh = s[o], U[:, o], Vh[o]
    np.savez(key, s=s, U=U, Vh=Vh)
    return s, U, Vh


def block_columns(F, M):
    """column indices of the sources with N(x) <= M, in norm order."""
    order = np.argsort(F.SN, kind='stable')
    return order[F.SN[order] <= M]


def orthonormal_cols(X):
    Q, _ = np.linalg.qr(X)
    return Q


def energy_in_span(Q, u):
    """||Q^* u||^2 / ||u||^2 for an orthonormal basis Q."""
    c = Q.conj().T @ u
    return float(np.vdot(c, c).real / np.vdot(u, u).real)


# ----------------------------------------------------------------------------------------------- class-signed source theta
def src_class_data(F, sd):
    """class data of the sources used by the class-signed theta model (all functions of x mod 36 and omega(x) mod 2):
       c4  = 4*(a mod 4) + (b mod 4)            the 12 occupied classes mod 4 of the primary generator
       t   = (b mod 9)/3 in {0,1,2}             cube-root class: lam3(x) = omega^(-t) is a cubic character mod 9
       odd = chi_x(-1) = -1                     (6 of the 12 classes mod 4)
       par = omega(x) mod 2 ; parsign = -1 on odd-class sources with an odd number of prime factors, else +1
       c36 = (class mod 4, class mod 9)."""
    SA, SB = F.SA, F.SB
    c4 = sd['cls4']
    t = ((SB % 9) // 3).astype(int)
    odd = (sd['utw'][:, 3].real < 0)
    par = sd['nprime'] % 2
    parsign = np.where(odd & (par == 1), -1.0, 1.0)
    c9 = (SA % 9) * 9 + (SB % 9)
    return dict(c4=c4, t=t, odd=odd, par=par, parsign=parsign, c9=c9, c36=c4 * 81 + c9)


def class_span(cl, base):
    """matrix whose columns are base restricted to each class of cl (one column per occupied class)."""
    keys = sorted(set(cl.tolist()))
    X = np.zeros((len(cl), len(keys)), dtype=complex)
    for i, k in enumerate(keys):
        m = cl == k
        X[m, i] = base[m]
    return X


def compressed(F, Q, side='src'):
    """Q^* H Q / (scale) for the source Gram H = E^* E (side='src', scale R) or the row Gram E E^* (side='row', scale S)."""
    E = F.E
    if side == 'src':
        EQ = E @ Q
        M = EQ.conj().T @ EQ / E.shape[0]
    else:
        EQ = E.conj().T @ Q
        M = EQ.conj().T @ EQ / E.shape[1]
    return (M + M.conj().T) / 2


def top_eig(M, k=3):
    w, V = np.linalg.eigh(M)
    o = np.argsort(-w)
    return w[o][:k], V[:, o[:k]]


def load_all(B, L, k=8):
    """build E (theta_core), source and row data, and the cached top-k singular triples."""
    import theta_core as tc
    from types import SimpleNamespace
    F = tc.build(B, L)
    sd = source_data(F)
    rd = row_data(F)
    s, U, Vh = top_pairs(F, k, 'B%d_L%d' % (B, L))
    return SimpleNamespace(F=F, sd=sd, rd=rd, s=s, U=U, Vh=Vh, B=B, L=L, R=F.R, S=F.S, sc=src_class_data(F, sd))


def lam3(F, j, k):
    """cubic character omega^(j*m + k*n) of the 3-adic class of a primary x = (3m - 1) + 3n*omega (arrays over the sources)."""
    m = ((F.SA + 1) // 3) % 3
    n = ((F.SB % 9) // 3)
    return np.exp(2j * np.pi * (j * m + k * n) / 3)


def class_signed_fit(A, alpha=1.0 / 3, conj=True, Esub=None, mask=None, k=12):
    """12-dim class-signed source theta: base = conj g~ N^-alpha lam3(0,-1) parsign on the 12 classes mod 4 (restricted to
    mask if given); returns (top eigenvalues of Q^*(E^*E)Q/R, f = best vector in the span, basis Xn).  Esub = the matrix to use
    in place of A.F.E (a row/column submatrix: then mask is applied inside it)."""
    F, sd, sc = A.F, A.sd, A.sc
    SN = F.SN.astype(float)
    g = np.conj(sd['Gsrc']) if conj else sd['Gsrc']
    base = g * SN ** (-alpha) * lam3(F, 0, -1) * sc['parsign']
    if mask is not None:
        base = base * mask
    X = class_span(sc['c4'], base)
    X = X[:, np.linalg.norm(X, axis=0) > 1e-12]
    Xn = X / np.linalg.norm(X, axis=0, keepdims=True)
    return base, Xn
