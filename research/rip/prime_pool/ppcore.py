"""ppcore.py -- core routines for the prime-pool (twisted fourth moment) numerics.  See README.md.

Everything here works over Z[w], w = e^{2 pi i/3}, elements a + b w as integer pairs.
 * primary element: a = 2 mod 3, b = 0 mod 3 (one per ideal coprime to 3; the unit ideal is represented by -1).
 * sextic symbol (x/pi)_6 = zeta6^k, k = sym code in Z/6 (same identification as research/rip/zomega.py:
   w = zeta6^2, the six roots of unity +-w^j are matched with their images mod pi).
 * rows: squarefree ideals z (products of distinct prime ideals), N(z) in [B, 2B], coprime to 6.
 * chi_z(n) = prod_{pi | z} (n/pi)_6 for the primary element n.   A product of THREE primary elements is again primary
   (2*2*2 = 2 mod 3), so X1 X2 Q = sum_m c_m chi_z(m) is a Dirichlet series over ideals with no unit twists.
The bulk symbol computation is vectorised (numpy modular exponentiation) and validated against zomega.Prime.sym
(ppsanity.py).  Run scripts with `python3 -I` (the script directory is added to sys.path explicitly).
"""
import os, sys, math
sys.dont_write_bytecode = True
import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..'))          # research/rip  (python3 -I does not put the script dir on sys.path)
import zomega as zo                                    # reused: Prime, norm, mul, conj, split_generator

I64 = np.int64
ZETA6 = np.exp(2j * np.pi * np.arange(6) / 6)
ZCODE = 100                                            # table code meaning "pi divides n": symbol is 0
UNITS = [(1, 0), (0, 1), (-1, -1), (-1, 0), (0, -1), (1, 1)]


# ----------------------------------------------------------------------------------------------- arithmetic helpers
def powmod(base, exp, mod):
    """Vectorised modular exponentiation (int64; mod < 3e9)."""
    base = np.asarray(base, I64); exp = np.asarray(exp, I64); mod = np.asarray(mod, I64)
    shape = np.broadcast(base, exp, mod).shape
    b = np.broadcast_to(base, shape) % mod
    e = np.broadcast_to(exp, shape)
    res = np.ones(shape, I64)
    nb = int(e.max()).bit_length() if e.size else 0
    for k in range(nb - 1, -1, -1):
        res = res * res % mod
        bit = ((e >> k) & 1).astype(bool)
        res = np.where(bit, res * b % mod, res)
    return res


def spf_sieve(n):
    spf = np.arange(n + 1, dtype=np.int32)
    for i in range(2, math.isqrt(n) + 1):
        if spf[i] == i:
            seg = spf[i * i::i]
            np.minimum(seg, i, out=seg)
    return spf


def cube_root_unity_mod(ps):
    """smaller primitive cube root of unity mod p, for primes p = 1 mod 3 (the two roots r, p-1-r are the images of w)."""
    ps = np.asarray(ps, I64)
    r = np.zeros_like(ps)
    todo = np.arange(len(ps))
    g = 2
    while todo.size:
        p = ps[todo]
        t = powmod(np.full(p.shape, g, I64), (p - 1) // 3, p)
        good = t != 1
        r[todo[good]] = t[good]
        todo = todo[~good]
        g += 1
    return np.minimum(r, ps - 1 - r)


def prim_assoc(a, b):
    """the associate of a + b w that is primary (== 2 mod 3)."""
    for u in UNITS:
        y = zo.mul(u, (a, b))
        if y[0] % 3 == 2 and y[1] % 3 == 0:
            return y
    raise ValueError('not coprime to 3: %s' % ((a, b),))


def primary_generator(p, r):
    """primary generator (a, b) of the prime ideal pi of norm p with w -> r mod pi (a + b r = 0 mod p).
    Gauss reduction of the lattice {x : x = 0 mod pi} = <p, -r + w> w.r.t. the norm form."""
    N = lambda v: v[0] * v[0] - v[0] * v[1] + v[1] * v[1]
    Bf = lambda v, w: 2 * v[0] * w[0] - (v[0] * w[1] + v[1] * w[0]) + 2 * v[1] * w[1]
    v1, v2 = (p, 0), (-int(r), 1)
    if N(v1) < N(v2): v1, v2 = v2, v1
    while True:
        # make v2 the shorter
        mu = round(Bf(v1, v2) / (2 * N(v2)))
        v1 = (v1[0] - mu * v2[0], v1[1] - mu * v2[1])
        if N(v1) >= N(v2): break
        v1, v2 = v2, v1
    g = v2 if N(v2) <= N(v1) else v1
    assert N(g) == p, (p, r, g)
    g = prim_assoc(*g)
    assert (g[0] + g[1] * int(r)) % p == 0
    return g


# ----------------------------------------------------------------------------------------------- prime ideal table
class Ideals:
    """prime ideals of Z[w] coprime to 6 with norm <= maxnorm.
    split ideal id = 2*k + w  (k = index of the rational prime p = split_p[k], w = 0/1: image of w is split_r[k] or p-1-split_r[k]);
    inert ideal id = 2*K + j  (K = number of split primes, q = inert_q[j], norm q^2)."""
    def __init__(self, maxnorm):
        self.maxnorm = maxnorm
        spf = spf_sieve(maxnorm)
        self.spf = spf
        allp = (np.nonzero(spf[2:] == np.arange(2, maxnorm + 1))[0] + 2).astype(I64)
        self.split_p = allp[allp % 3 == 1]
        self.split_r = cube_root_unity_mod(self.split_p)
        self.pidx = np.full(maxnorm + 1, -1, np.int32)
        self.pidx[self.split_p] = np.arange(len(self.split_p), dtype=np.int32)
        self.inert_q = allp[(allp % 3 == 2) & (allp != 2) & (allp * allp <= maxnorm)]
        self.qidx = {int(q): j for j, q in enumerate(self.inert_q)}
        self.ns = 2 * len(self.split_p)

    def split_pr(self, ids):
        k = ids // 2; w = ids % 2
        p = self.split_p[k]
        r = np.where(w == 0, self.split_r[k], p - 1 - self.split_r[k])
        return p, r

    def ideal_id(self, p, r):
        k = int(self.pidx[p]); assert k >= 0
        return 2 * k + (0 if int(r) == int(self.split_r[k]) else 1)


# ----------------------------------------------------------------------------------------------- sextic symbols
def sym_codes(p, r, SA, SB):
    """codes k in Z/6 (or ZCODE) with (a + b w / pi)_6 = zeta6^k, for the split ideals (p[i], r[i]) and elements (SA[j], SB[j]).
    Returns int8 array (len(p), len(SA)).  Same identification as zomega.Prime.sym."""
    p = np.asarray(p, I64)[:, None]; r = np.asarray(r, I64)[:, None]
    SA = np.asarray(SA, I64)[None, :]; SB = np.asarray(SB, I64)[None, :]
    v = (SA + SB * r) % p
    z = v == 0
    v = np.where(z, 1, v)
    t = powmod(v, (p - 1) // 6, p)
    r2 = (r * r) % p
    code = np.full(t.shape, -1, np.int8)
    code[t == 1] = 0
    code[t == r] = 2
    code[t == r2] = 4
    code[t == p - 1] = 3
    code[t == p - r] = 5
    code[t == p - r2] = 1
    assert (code[~z] >= 0).all(), 'symbol not a sixth root of unity?'
    code[z] = ZCODE
    return code


def symbol_table(ID, uniq_ids, SA, SB, verbose=False):
    """T[i, j] = sym code of source j against prime ideal uniq_ids[i]."""
    SA = np.asarray(SA, I64); SB = np.asarray(SB, I64)
    S = len(SA); nu = len(uniq_ids)
    T = np.empty((nu, S), np.int8)
    split = uniq_ids < ID.ns
    sidx = np.nonzero(split)[0]
    if len(sidx):
        p, r = ID.split_pr(uniq_ids[sidx])
        CH = max(1, 1_500_000 // S)
        for i in range(0, len(sidx), CH):
            T[sidx[i:i + CH]] = sym_codes(p[i:i + CH], r[i:i + CH], SA, SB)
    for ui in np.nonzero(~split)[0]:
        q = int(ID.inert_q[uniq_ids[ui] - ID.ns])
        pr = zo.Prime(q)
        T[ui] = [ZCODE if (c := pr.sym((int(a), int(b)))) is None else c for a, b in zip(SA, SB)]
    return T


# ----------------------------------------------------------------------------------------------- rows
def enumerate_rows(B, ID):
    """squarefree ideals z coprime to 6 with N(z) in [B, 2B].  Returns dict with
    A, Bc (primary generator), N, and PID (R, J) int array of prime ideal ids (-1 padded)."""
    M = math.isqrt((8 * B) // 3) + 4
    ap = np.arange(-(M // 3) - 2, M // 3 + 3, dtype=I64)
    A2 = (3 * ap + 2)[:, None]; B2 = (3 * ap)[None, :]
    Nn = A2 * A2 - A2 * B2 + B2 * B2
    sel = (Nn >= B) & (Nn <= 2 * B) & (Nn % 2 == 1)
    ia, ib = np.nonzero(sel)
    A = (3 * ap[ia] + 2); Bc = (3 * ap[ib]); N = Nn[ia, ib]
    del Nn, sel
    n = N.size
    rem = N.copy()
    sq = np.ones(n, bool)
    rows_l, ids_l = [], []
    act = np.arange(n)
    while act.size:
        rm = rem[act]
        nz = rm > 1
        act = act[nz]; rm = rm[nz]
        if not act.size: break
        p = ID.spf[rm].astype(I64)
        e = np.zeros(act.size, I64)
        t = rm.copy()
        while True:
            d = (t % p) == 0
            if not d.any(): break
            t = np.where(d, t // p, t)
            e += d
        rem[act] = t
        a = A[act]; b = Bc[act]
        inert = (p % 3 == 2)
        ii = np.nonzero(inert)[0]
        if ii.size:
            bad = e[ii] != 2
            sq[act[ii[bad]]] = False
            gi = ii[~bad]
            if gi.size:
                rows_l.append(act[gi])
                ids_l.append(ID.ns + np.array([ID.qidx[int(q)] for q in p[gi]], I64))
        ss = np.nonzero(~inert)[0]
        if ss.size:
            ps = p[ss]; k = ID.pidx[ps].astype(I64); r1 = ID.split_r[k]; r2 = ps - 1 - r1
            t1 = ((a[ss] + b[ss] * r1) % ps) == 0
            t2 = ((a[ss] + b[ss] * r2) % ps) == 0
            ee = e[ss]
            one = ee == 1
            two = ee == 2
            bad = (ee >= 3) | (two & ~(t1 & t2)) | (one & ~(t1 | t2))
            sq[act[ss[bad]]] = False
            g1 = one & ~bad
            if g1.any():
                rows_l.append(act[ss[g1]]); ids_l.append(2 * k[g1] + np.where(t1[g1], 0, 1))
            g2 = two & ~bad
            if g2.any():
                rows_l.append(act[ss[g2]]); ids_l.append(2 * k[g2])
                rows_l.append(act[ss[g2]]); ids_l.append(2 * k[g2] + 1)
    prow = np.concatenate(rows_l); pid = np.concatenate(ids_l)
    keep = sq[prow]
    prow = prow[keep]; pid = pid[keep]
    rowmap = np.cumsum(sq) - 1                      # candidate index -> row index
    R = int(sq.sum())
    order = np.argsort(prow, kind='stable')
    prow = rowmap[prow[order]]; pid = pid[order]
    first = np.searchsorted(prow, np.arange(R))
    rank = np.arange(len(prow)) - first[prow]
    J = int(rank.max()) + 1
    PID = np.full((R, J), -1, I64)
    PID[prow, rank] = pid
    return dict(A=A[sq], Bc=Bc[sq], N=N[sq], PID=PID, R=R, J=J)


def local_index(PID, uid):
    """map prime-ideal ids in PID to positions in the sorted unique list uid (-1 stays -1)."""
    return np.where(PID >= 0, np.searchsorted(uid, np.where(PID >= 0, PID, 0)), -1)


def chi_chunk(LOC, T, r0, r1):
    """complex matrix chi_z(source_j) for rows r0..r1 (0 where a prime of z divides the source)."""
    n = r1 - r0; S = T.shape[1]
    acc = np.zeros((n, S), np.int16)
    for j in range(LOC.shape[1]):
        li = LOC[r0:r1, j]; sel = li >= 0
        if sel.any():
            acc[sel] += T[li[sel]]
    chi = ZETA6[acc % 6]
    chi[acc >= ZCODE] = 0
    return chi


# ----------------------------------------------------------------------------------------------- sources
def primary_elements(Nmax):
    """all primary elements (a, b) (a = 2 mod 3, b = 0 mod 3) with 1 <= N <= Nmax, sorted by norm."""
    M = math.isqrt((4 * int(Nmax)) // 3) + 3
    ap = np.arange(-(M // 3) - 2, M // 3 + 3, dtype=I64)
    A2 = (3 * ap + 2)[:, None]; B2 = (3 * ap)[None, :]
    Nn = A2 * A2 - A2 * B2 + B2 * B2
    ia, ib = np.nonzero(Nn <= Nmax)
    A = 3 * ap[ia] + 2; Bc = 3 * ap[ib]; N = Nn[ia, ib]
    o = np.lexsort((Bc, A, N))
    return A[o], Bc[o], N[o]


def split_prime_sources(ID, lo, hi):
    """split prime ideals with lo < N <= hi (both conjugates), as dicts with primary generator, sorted by (norm, id)."""
    ks = np.nonzero((ID.split_p > lo) & (ID.split_p <= hi))[0]
    out = []
    for k in ks:
        p = int(ID.split_p[k])
        for w in (0, 1):
            r = int(ID.split_r[k]) if w == 0 else p - 1 - int(ID.split_r[k])
            a, b = primary_generator(p, r)
            out.append(dict(p=p, r=r, a=a, b=b, id=2 * int(k) + w))
    return out


def gauss_sums(P):
    """Normalised sextic Gauss sums of a split prime P (dict from split_prime_sources), x = rational integers mod p.
    simple:  g~ = p^{-1/2} sum_x (x/P)_6 e(x/p)                      (additive character e(x/p): the task's normalisation)
    canon :  g~ = p^{-1/2} sum_x (x/P)_6 e(-b x/p),  P = a + b w primary generator
             (= e(Tr(x/(sqrt(-3) P))), the Kubota/Patterson character; same convention as round7/signal-processing/zw.py)."""
    p = P['p']; r = P['r']; b = P['b']
    x = np.arange(1, p, dtype=I64)
    code = sym_codes(np.array([p]), np.array([r]), x, np.zeros_like(x))[0]
    chi = ZETA6[code]
    gs = np.sum(chi * np.exp(2j * np.pi * x / p)) / math.sqrt(p)
    gc = np.sum(chi * np.exp(-2j * np.pi * ((b * x) % p) / p)) / math.sqrt(p)
    return gs, gc


# ----------------------------------------------------------------------------------------------- Dirichlet-series (diagonal) side
def encode(a, b, off=1 << 20):
    return (np.asarray(a, I64) + off) * (1 << 22) + (np.asarray(b, I64) + off)


def zmul(a1, b1, a2, b2):
    """(a1 + b1 w)(a2 + b2 w) with w^2 = -1 - w."""
    return a1 * a2 - b1 * b2, a1 * b2 + b1 * a2 - b1 * b2


def self_convolution(SA, SB, w):
    """d = w * w as a Dirichlet polynomial over ELEMENT products n1*n2 (== 1 mod 3: unique per ideal).
    Returns (ka, kb, d, rep_i, rep_j)."""
    nz = np.nonzero(w > 0)[0]
    i, j = np.meshgrid(nz, nz, indexing='ij')
    i = i.ravel(); j = j.ravel()
    pa, pb = zmul(SA[i], SB[i], SA[j], SB[j])
    key = encode(pa, pb)
    uk, first, inv = np.unique(key, return_index=True, return_inverse=True)
    d = np.bincount(inv, weights=w[i] * w[j])
    return pa[first], pb[first], d


def conv_matrix(ka, kb, d, TA, TB):
    """sparse matrix Amat (nsrc x ncols): Amat[s, col(m)] = d_k, m = k * t_s (primary element), t_s = (TA[s], TB[s]).
    Returns (Amat csr, cols_a, cols_b)."""
    import scipy.sparse as sp
    ns = len(TA); nk = len(ka)
    a, b = zmul(ka[None, :], kb[None, :], np.asarray(TA, I64)[:, None], np.asarray(TB, I64)[:, None])
    assert (a % 3 == 2).all() and (b % 3 == 0).all(), 'triple products must be primary'
    key = encode(a, b).ravel()
    uk, first, inv = np.unique(key, return_index=True, return_inverse=True)
    rows = np.repeat(np.arange(ns), nk)
    vals = np.broadcast_to(d[None, :], (ns, nk)).ravel()
    M = sp.csr_matrix((vals, (rows, inv)), shape=(ns, len(uk)))
    return M, a.ravel()[first], b.ravel()[first]


def rho_elements(ID, a, b, pmax):
    """prod over prime ideals pi | m (norm <= pmax) of N(pi)/(N(pi)+1): fraction of squarefree z coprime to m, heuristically.
    (Exact prime-ideal support of each element m = a + b w; used for the coprimality-corrected diagonal D_cop.)"""
    a = np.asarray(a, I64); b = np.asarray(b, I64)
    N = a * a - a * b + b * b
    rho = np.ones(a.shape, np.float64)
    for p in ID.split_p[ID.split_p <= pmax]:
        p = int(p)
        div = (N % p) == 0
        if not div.any(): continue
        k = int(ID.pidx[p]); r1 = int(ID.split_r[k]); r2 = p - 1 - r1
        t1 = div & (((a + b * r1) % p) == 0)
        t2 = div & (((a + b * r2) % p) == 0)
        f = p / (p + 1.0)
        rho[t1] *= f; rho[t2] *= f
    for q in ID.inert_q[ID.inert_q <= math.isqrt(pmax)]:
        q = int(q)
        div = (a % q == 0) & (b % q == 0)
        rho[div] *= q * q / (q * q + 1.0)
    return rho


# ----------------------------------------------------------------------------------------------- weights
def norm_arr(A, B):
    A = np.asarray(A, I64); B = np.asarray(B, I64)
    return A * A - A * B + B * B


def weight_vector(Nsrc, L, kind):
    """plain: 1_{N <= L};  smooth: (1 - N/L)_+."""
    Nsrc = np.asarray(Nsrc, float)
    if kind == 'plain':
        return (Nsrc <= L).astype(float)
    return np.maximum(0.0, 1.0 - Nsrc / L)
