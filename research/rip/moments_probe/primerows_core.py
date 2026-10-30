"""Shared machinery for the prime-row / composite-row study (PRIMEROWS.md).

Same objects as probeC.py (rows, sources, weights, surrogate), built on the probeB.py helpers (imported, not modified),
plus per-row metadata used by the experiments:
  normu   N(u);   kres = ((N(u) - 1)/6) mod 6, which fixes the 3-part of the conductor of the ideal character
          n -> chi_u(primary generator of n):  k = 0 -> conductor u (sum imprimitive at 1 - w), k = 3 -> (1 - w) u,
          k in {1,2,4,5} -> 3u   [derived, PRIMEROWS.md section 2]
  nf, minnorm (smallest factor norm), has_inert, conj (index of the conjugate row u-bar, |S_ubar| = |S_u|), maskkey
  (the factors of u with norm <= the largest source norm: the only thing the surrogate of u depends on).
Actual sums are complex S_u (R x nm).  Surrogate: K replicas per row of a random completely multiplicative f_u with
i.i.d. uniform mu_6 values at prime ideals and the same coprimality mask; we keep per-row sums of |S|^2, |S|^4, |S|^6.
"""
import sys, os, math, time
sys.dont_write_bytecode = True
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import numpy as np
import scipy.sparse as sps
import probeB as PB

SIG = 0.3
Z6 = PB.ZETA6.astype(np.complex64)


def weight(t, kind):
    if kind == 'sharp':
        return ((t >= 1.0) & (t < 2.0)).astype(np.float64)
    w = np.exp(-np.log(np.maximum(t, 1e-300)) ** 2 / (2 * SIG ** 2))
    w[(t < math.exp(-1)) | (t >= math.e)] = 0.0
    return w


def support(kind):
    return (1.0, 2.0) if kind == 'sharp' else (math.exp(-1), math.e)


def subPI(PI, idx):
    return {k: v[idx] for k, v in PI.items()}


class Setup:
    """rows, metadata, sources, weights and the factor matrix of the sources."""

    def __init__(self, B, ms, kind='smooth', rough=0, lens=None, verbose=True):
        t0 = time.time()
        self.B, self.ms, self.kind = B, list(ms), kind
        self.lens = [B ** m for m in ms] if lens is None else list(lens)    # window centres N
        ar = PB.Arith(2 * B + 10)
        PI = PB.prime_ideals(ar, 2 * B)
        self.PI = PI
        rows = PB.build_rows(PI['norm'], B, 2 * B)
        self.rows = rows
        R = self.R = len(rows)
        nP = len(PI['norm'])
        self.nf = np.array([len(r) for r in rows])
        self.normu = np.array([int(np.prod([int(PI['norm'][j]) for j in r])) for r in rows], dtype=np.int64)
        self.kres = ((self.normu - 1) // 6) % 6
        self.minnorm = np.array([int(PI['norm'][r[0]]) for r in rows], dtype=np.int64)
        self.minidx = np.array([r[0] for r in rows], dtype=np.int64)
        self.has_inert = np.array([any(PI['kind'][j] == 1 for j in r) for r in rows])
        # conjugate ideal of each prime ideal
        cj = np.arange(nP)
        byp = {}
        for i in range(nP):
            if PI['kind'][i] == 0:
                byp.setdefault(int(PI['p'][i]), []).append(i)
        for p, l in byp.items():
            assert len(l) == 2
            cj[l[0]], cj[l[1]] = l[1], l[0]
        self.cjP = cj
        pos = {r: i for i, r in enumerate(rows)}
        self.conj = np.array([pos[tuple(sorted(int(cj[j]) for j in r))] for r in rows], dtype=np.int64)
        self.selfconj = self.conj == np.arange(R)
        self.has_pair = np.array([any(int(cj[j]) in r and int(cj[j]) != j for j in r) for r in rows])
        # sources
        lo_f, hi_f = support(kind)
        lo = int(math.floor(min(self.lens) * lo_f)); hi = int(math.ceil(max(self.lens) * hi_f)) + 1
        SA, SB, SN = PB.primary_window(max(lo, 1), hi)
        Ex, _ = PB.small_prime_ideal_factors(SA, SB, SN, hi + 5)          # nS x (nI+1), last column = (2)
        nI = Ex.shape[1] - 1
        PIs = PB.prime_ideals(PB.Arith(hi + 15), hi + 5)
        assert np.array_equal(PIs['norm'], PI['norm'][:nI]) and np.array_equal(PIs['p'], PI['p'][:nI]) \
            and np.array_equal(PIs['a'], PI['a'][:nI]) and np.array_equal(PIs['b'], PI['b'][:nI]), 'prime list mismatch'
        self.srcnorm_I = np.append(PI['norm'][:nI], 4)
        if rough:
            # keep only sources coprime to every prime ideal of norm <= rough (incl. (2) if 4 <= rough)
            small = np.flatnonzero(self.srcnorm_I <= rough)
            keep = Ex[:, small].sum(1) == 0
            SA, SB, SN, Ex = SA[keep], SB[keep], SN[keep], Ex[keep]
        self.rough = rough
        self.SA, self.SB, self.SN = SA, SB, SN
        self.nS = len(SA)
        self.Ex = Ex
        self.ExS = sps.csr_matrix(Ex)
        self.nI = nI
        self.maxsrc = int(SN.max())
        self.W = np.stack([weight(SN / N, kind) for N in self.lens], axis=1).astype(np.float32)   # nS x nm
        self.mass = (self.W.astype(np.float64) ** 2).sum(0)
        # mask key: factors of u that can divide a source
        self.maskkey = [tuple(j for j in r if PI['norm'][j] <= self.maxsrc) for r in rows]
        self.Inc = None
        if verbose:
            print(f'[setup] B={B} R={R} nS={self.nS} nI={nI} maxsrc={self.maxsrc} rough={rough} ({time.time()-t0:.1f}s)', flush=True)

    def classes(self):
        nf, mn = self.nf, self.minnorm
        return dict(all=np.ones(self.R, bool), prime=nf == 1, composite=nf >= 2,
                    comp_small=(nf >= 2) & (mn <= 200), comp_large=(nf >= 2) & (mn > 200))

    # ------------------------------------------------------------------ actual sums
    def actual(self, CH=2000, verbose=True):
        """complex S_u (R x nm); composite rows through a symbol table of the primes of norm <= 2B/7, prime rows directly."""
        t0 = time.time()
        PI, R, rows = self.PI, self.R, self.rows
        S = np.zeros((R, len(self.lens)), dtype=np.complex128)
        Wc = self.W.astype(np.complex64)
        comp = np.flatnonzero(self.nf >= 2)
        prim = np.flatnonzero(self.nf == 1)
        if len(comp):
            jmax = max(max(rows[i]) for i in comp) + 1
            E, Z = PB.sextic_table(subPI(PI, np.arange(jmax)), self.SA, self.SB)
            E32 = E.astype(np.float32); Z32 = Z.astype(np.float32)
            del E, Z
            nfc = self.nf[comp]
            indptr = np.zeros(len(comp) + 1, dtype=np.int64); indptr[1:] = np.cumsum(nfc)
            indices = np.fromiter((j for i in comp for j in rows[i]), dtype=np.int64, count=int(indptr[-1]))
            Inc = sps.csr_matrix((np.ones(len(indices), dtype=np.float32), indices, indptr), shape=(len(comp), jmax))
            for i0 in range(0, len(comp), CH):
                inc = Inc[i0:i0 + CH]
                Ech = np.rint(inc @ E32).astype(np.int64) % 6
                msk = (inc @ Z32) < 0.5
                ph = Z6[Ech] * msk
                S[comp[i0:i0 + CH]] = ph @ Wc
            del E32, Z32
        for i0 in range(0, len(prim), CH):
            idx = prim[i0:i0 + CH]
            pj = np.array([rows[i][0] for i in idx])
            E, Z = PB.sextic_table(subPI(PI, pj), self.SA, self.SB)
            ph = Z6[E.astype(np.int64)] * (~Z)
            S[idx] = ph @ Wc
        if verbose:
            print(f'[actual] done ({time.time()-t0:.1f}s)', flush=True)
        return S

    def masks(self, CH=None):
        """sparse boolean structure: for each row the sources killed by the mask (row factor divides source)."""
        # source j is killed by row u iff some factor of u (norm <= maxsrc) divides it: use Ex columns of the factors
        nI = self.nI
        exb = (self.Ex[:, :nI] > 0)
        return exb

    # ------------------------------------------------------------------ surrogate
    def surrogate(self, K, rng, CH=1500, keep=0, groups=1, verbose=True, rows_idx=None, pair=False):
        """K replicas per row; returns sums over replicas of |S|^2,|S|^4,|S|^6 per row (R x nm x 3) split in `groups`
        groups of replicas (R x nm x 3 x groups), and the first `keep` replicas' |S|^2 (keep x R x nm, float32).
        pair=True draws f_ubar(n) = conj f_u(conj n) for the conjugate row (so |S_ubar| = |S_u| as in the actual)."""
        t0 = time.time()
        R = self.R if rows_idx is None else len(rows_idx)
        ridx = np.arange(self.R) if rows_idx is None else np.asarray(rows_idx)
        nm = len(self.lens)
        acc = np.zeros((R, nm, 3, groups))
        kept = np.zeros((keep, R, nm), dtype=np.float32) if keep else None
        exb = (self.Ex[:, :self.nI] > 0).astype(np.float32)          # nS x nI
        Wc = self.W.astype(np.complex64)
        # mask matrix rows x nI (factors of u among the source primes)
        rr, cc = [], []
        for t, i in enumerate(ridx):
            for j in self.maskkey[i]:
                rr.append(t); cc.append(j)
        Mk = sps.csr_matrix((np.ones(len(rr), dtype=np.float32), (rr, cc)), shape=(R, self.nI))
        nIx = self.Ex.shape[1]
        W2 = (self.W.astype(np.float64) ** 2) / self.mass                # nS x nm
        self.diag = np.zeros((R, nm))                                     # exact E|S_u|^2 / mass (the masked diagonal)
        for i0 in range(0, R, CH):
            i1 = min(R, i0 + CH)
            killed = np.asarray((Mk[i0:i1] @ exb.T)) > 0.5               # chunk x nS
            live = ~killed
            self.diag[i0:i1] = live.astype(np.float64) @ W2
            for r in range(K):
                J = rng.integers(0, 6, size=(nIx, i1 - i0)).astype(np.float32)
                Er = np.rint(np.asarray(self.ExS @ J)).astype(np.int64).T % 6
                ph = Z6[Er] * live
                a2 = np.abs(ph @ Wc).astype(np.float64) ** 2 / self.mass
                g = r % groups
                acc[i0:i1, :, 0, g] += a2
                acc[i0:i1, :, 1, g] += a2 ** 2
                acc[i0:i1, :, 2, g] += a2 ** 3
                if r < keep:
                    kept[r, i0:i1] = a2
        if verbose:
            print(f'[surrogate] K={K} rows={R} ({time.time()-t0:.1f}s)', flush=True)
        return acc, kept


def pair_clusters(conj):
    """cluster id per row: rows u and conj(u) share a cluster."""
    R = len(conj)
    cid = np.minimum(np.arange(R), conj)
    _, inv = np.unique(cid, return_inverse=True)
    return inv


def boot_ratio(a6, s6, cl, nb=2000, rng=None, sel=None):
    """bootstrap over conjugate-pair clusters of mean(a6)/mean(s6) (rows in sel)."""
    rng = rng or np.random.default_rng(0)
    if sel is not None:
        a6, s6, cl = a6[sel], s6[sel], cl[sel]
    _, cl = np.unique(cl, return_inverse=True)
    nc = cl.max() + 1
    A = np.bincount(cl, weights=a6, minlength=nc); S = np.bincount(cl, weights=s6, minlength=nc)
    n = np.bincount(cl, minlength=nc).astype(float)
    out = np.empty(nb)
    for b in range(nb):
        w = np.bincount(rng.integers(0, nc, nc), minlength=nc).astype(float)
        out[b] = (w @ A) / (w @ S)
    return float(np.mean(a6) / np.mean(s6)), float(np.std(out)), out
