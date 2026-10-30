"""PROBE B (directions.md D4): sixth (and fourth) moments of short plain sums in the thin sextic family.

Rows u : squarefree products of distinct prime ideals of Z[w], norm in [B, 2B], coprime to 6 (rip/zfamily.py);
         chi_u = (./u)_6 = prod_{pi | u} (./pi)_6   (rip/zomega.py conventions: x^((N pi-1)/6) mod pi).
Sums   : S_u = sum_{n primary, N <= N(n) < 2N} chi_u(n),   N = B^m   (primary = one generator per ideal prime to 3).
Moments: M4 = sum_u |S_u|^4 /(R N^2),  M6 = sum_u |S_u|^6 /(R N^3),   R = #rows.

Comparators computed at the same R, N and with the same coprimality zeros (chi_u(n) = 0 iff gcd(n,u) != 1):
  mult : S_u^mult  = sum_n f_u(n), f_u completely multiplicative on ideals with i.i.d. uniform mu_6 values at the prime
         ideals ("Lindelof on average" surrogate; E|S|^6 = #{n1n2n3 = n4n5n6} for the units-free count)
  iid  : S_u^iid   = sum_n exp(2 pi i theta_{u,n}), i.i.d. uniform phases per (u,n)  (no multiplicative structure)
  diag : exact counts T4 = #{n1 n2 = n3 n4}, T6 = #{n1 n2 n3 = n4 n5 n6} of ideals in the window (no coprimality mask)
  full : the full family of Dirichlet characters mod a prime q ~ R on the integers [N, 2N): the exact count
         #{n1n2n3 = m1m2m3 mod q}/N^3 (this has the 'N-term' ~ N^3/q: a positive control of the diagnostic).

usage: python3 -I probeB.py --B 3000 6000 12000 --m 0.3 0.35 0.43 0.5 [--nrep 3] [--sources all|zfamily] [--out FILE.json]
"""
import sys, os, math, time, argparse, json
sys.dont_write_bytecode = True
HERE = os.path.dirname(os.path.abspath(__file__))
SP_DIR = os.path.normpath(os.path.join(HERE, '..', '..', 'round7', 'signal-processing'))
RIP_DIR = os.path.normpath(os.path.join(HERE, '..'))
for _d in (SP_DIR, RIP_DIR):
    if _d not in sys.path:
        sys.path.insert(0, _d)
import numpy as np
import scipy.sparse as sps
import zomega                                  # Prime (sextic symbols, used for inert primes and validation)
from zw import Arith, powmod                   # primary prime elements, vectorised modular power

ZETA6 = np.exp(2j * np.pi * np.arange(6) / 6)
T0 = time.time()


def log(*a):
    print(f'[{time.time()-T0:7.1f}s]', *a, flush=True)


# ------------------------------------------------------------------------- arithmetic
def primary_window(lo, hi):
    """all primary a + b w (a = 2 mod 3, b = 0 mod 3) with lo <= N(a + b w) < hi, sorted by (N, a, b)."""
    T = int(2 * math.sqrt(hi / 3.0)) + 3
    a = np.arange(-T, T + 1); a = a[a % 3 == 2]
    b = np.arange(-T, T + 1); b = b[b % 3 == 0]
    A, B = np.meshgrid(a, b, indexing='ij')
    A = A.ravel(); B = B.ravel()
    N = A * A - A * B + B * B
    m = (N >= lo) & (N < hi)
    A, B, N = A[m], B[m], N[m]
    o = np.lexsort((B, A, N))
    return A[o], B[o], N[o]


def prime_ideals(ar, maxnorm):
    """prime ideals prime to 6 with norm <= maxnorm: split (two per p = 1 mod 3) and inert (q = 2 mod 3, q >= 5, q^2 <= maxnorm)
    returned as arrays sorted by norm: norm, kind (0 split / 1 inert), p (the rational prime), r (image of w, split only), a, b."""
    el = ar.elems(1, maxnorm, primes_only=True)           # primary prime elements of prime norm p = 1 mod 3
    recs = [(e['N'], 0, e['ps'][0], e['rs'][0], e['a'], e['b']) for e in el]
    q = 5
    while q * q <= maxnorm:
        if ar.isp[q] and q % 3 == 2:
            recs.append((q * q, 1, q, -1, 0, 0))
        q += 1
    recs.sort()
    arr = np.array(recs, dtype=np.int64)
    return dict(norm=arr[:, 0], kind=arr[:, 1], p=arr[:, 2], r=arr[:, 3], a=arr[:, 4], b=arr[:, 5])


def sextic_table(PI, SA, SB):
    """E[i, j] in 0..5 with (source j / prime ideal i)_6 = zeta6^E (E = 0 where pi | source: see Z), Z[i, j] = (pi | source)."""
    nP, nS = len(PI['norm']), len(SA)
    E = np.zeros((nP, nS), dtype=np.int8)
    Z = np.zeros((nP, nS), dtype=bool)
    SA64 = SA.astype(np.int64); SB64 = SB.astype(np.int64)
    inert_cache = {}
    for i in range(nP):
        p = int(PI['p'][i])
        if PI['kind'][i] == 0:
            r = int(PI['r'][i])
            v = (SA64 + SB64 * r) % p
            z = v == 0
            t = powmod(v, (p - 1) // 6, p)
            base = (-r * r) % p                         # image of zeta6 = -w^2
            k = np.zeros(nS, dtype=np.int8)
            ok = z.copy()
            x = 1
            for kk in range(6):
                if kk:
                    x = (x * base) % p
                msk = (t == x) & ~z
                k[msk] = kk
                ok |= msk
            assert ok.all(), f'prime {p}: non-sixth-root values'
            E[i] = k; Z[i] = z
        else:
            pr = inert_cache.setdefault(p, zomega.Prime(p))
            for j in range(nS):
                s = pr.sym((int(SA[j]), int(SB[j])))
                if s is None:
                    Z[i, j] = True
                else:
                    E[i, j] = s
    return E, Z


def build_rows(norms, lo, hi):
    """squarefree products of distinct prime ideals (indices into the norm-sorted list) with norm in [lo, hi]."""
    n = len(norms)
    rows = []
    sys.setrecursionlimit(100000)
    nl = norms.tolist()

    def rec(start, N, facs):
        if lo <= N <= hi:
            rows.append(tuple(facs))
        for j in range(start, n):
            Nj = nl[j]
            if N * Nj > hi:
                break
            facs.append(j)
            rec(j + 1, N * Nj, facs)
            facs.pop()
    rec(0, 1, [])
    return rows


# ------------------------------------------------------------- exact diagonal counts T4, T6
def ideal_mul(a1, b1, a2, b2):
    return a1 * a2 - b1 * b2, a1 * b2 + a2 * b1 - b1 * b2


def key_of(a, b):
    return (a + (1 << 30)) * (1 << 31) + (b + (1 << 30))


def diag_counts(A, B, want6=True, cap6=420):
    """T4 = #{(n1..n4): n1 n2 = n3 n4}, T6 = #{(n1..n6): n1 n2 n3 = n4 n5 n6} over the window elements (ideals)."""
    C = len(A)
    A = A.astype(np.int64); B = B.astype(np.int64)
    pa, pb = ideal_mul(A[:, None], B[:, None], A[None, :], B[None, :])
    keys2 = key_of(pa.ravel(), pb.ravel())
    u2, c2 = np.unique(keys2, return_counts=True)
    T4 = int(np.sum(c2.astype(np.int64) ** 2))
    T6 = None
    if want6 and C <= cap6:
        # distinct pair products (a2, b2) with multiplicity c2, then times each n
        ua = (u2 // (1 << 31)) - (1 << 30)
        ub = (u2 % (1 << 31)) - (1 << 30)
        allk = []
        allw = []
        for j in range(C):
            ta, tb = ideal_mul(ua, ub, A[j], B[j])
            allk.append(key_of(ta, tb)); allw.append(c2)
        allk = np.concatenate(allk); allw = np.concatenate(allw)
        o = np.argsort(allk, kind='stable')
        allk = allk[o]; allw = allw[o]
        brk = np.flatnonzero(np.diff(allk)) + 1
        tot = np.add.reduceat(allw, np.concatenate(([0], brk)))
        T6 = int(np.sum(tot.astype(np.int64) ** 2))
    return T4, T6


def full_family_counts(N, qmin):
    """exact #{n1n2 = m1m2 mod q}, #{n1n2n3 = m1m2m3 mod q} over integers in [N, 2N), q the next prime > max(qmin, 2N)."""
    q = max(int(qmin), 2 * int(math.ceil(N))) + 1
    while any(q % d == 0 for d in range(2, int(q ** 0.5) + 1)):
        q += 1
    n = np.arange(int(math.ceil(N)), int(math.ceil(2 * N)), dtype=np.int64)
    p2 = (n[:, None] * n[None, :] % q).ravel()
    c2 = np.bincount(p2, minlength=q)
    F4 = int(np.sum(c2.astype(np.int64) ** 2))
    c3 = np.zeros(q, dtype=np.int64)
    for x in n:
        c3 += np.bincount(p2 * x % q, minlength=q)
    F6 = int(np.sum(c3 ** 2))
    # integer diagonal (q -> infinity): counts of true equalities
    pr2 = (n[:, None] * n[None, :]).ravel()
    _, cc2 = np.unique(pr2, return_counts=True)
    I4 = int(np.sum(cc2.astype(np.int64) ** 2))
    return q, F4, F6, I4, len(n)


# ------------------------------------------------------------------------------ main
def small_prime_ideal_factors(SA, SB, SN, N_hi):
    """exponent matrix Ex[j, i] of the prime ideal i (all ideals of norm < N_hi, incl. (2)) in the ideal (source j)."""
    ar = Arith(int(N_hi) + 10)
    PI = prime_ideals(ar, int(N_hi))
    nI = len(PI['norm'])
    kind = np.append(PI['kind'], 1); pp = np.append(PI['p'], 2); rr = np.append(PI['r'], -1)
    ga = np.append(PI['a'], 0); gb = np.append(PI['b'], 0)
    inorm = np.append(PI['norm'], 4).astype(object)
    split = kind == 0
    Ex = np.zeros((len(SA), nI + 1), dtype=np.float32)
    for j in range(len(SA)):
        a0, b0 = int(SA[j]), int(SB[j])
        cand = np.flatnonzero(np.where(split, (a0 + b0 * np.where(split, rr, 0)) % pp == 0, (a0 % pp == 0) & (b0 % pp == 0)))
        tot = 1
        for i in cand:
            p = int(pp[i])
            e = 0
            if split[i]:
                ca, cb = a0, b0                      # divide by the prime element (ga, gb): z * conj(pi) / p
                cga, cgb = int(ga[i]) - int(gb[i]), -int(gb[i])
                while True:
                    za, zb = ideal_mul(ca, cb, cga, cgb)
                    if za % p or zb % p:
                        break
                    ca, cb = za // p, zb // p
                    e += 1
            else:
                ca, cb = a0, b0
                while ca % p == 0 and cb % p == 0:
                    ca //= p; cb //= p; e += 1
            Ex[j, i] = e
            tot *= int(inorm[i]) ** e
        assert tot == int(SN[j]), (a0, b0, tot, SN[j])
    return Ex, None


CAPFULL = 900


def run(B, ms, nrep, sources, rng, CH=8000):
    t1 = time.time()
    ar = Arith(2 * B + 10)
    PI = prime_ideals(ar, 2 * B)
    log(f'B={B}: {len(PI["norm"])} prime ideals (norm <= {2*B})')
    rows = build_rows(PI['norm'], B, 2 * B)
    R = len(rows)
    log(f'B={B}: {R} rows (squarefree, N(u) in [B,2B], prime to 6)   [{R/B:.3f} B]   ({time.time()-t1:.1f}s)')
    indptr = np.zeros(R + 1, dtype=np.int64)
    indptr[1:] = np.cumsum([len(r) for r in rows])
    indices = np.fromiter((j for r in rows for j in r), dtype=np.int64, count=int(indptr[-1]))
    Inc = sps.csr_matrix((np.ones(len(indices), dtype=np.float32), indices, indptr), shape=(R, len(PI['norm'])))
    # windows
    wins = []
    for m in ms:
        N = B ** m
        wins.append(dict(m=m, N=N, lo=N, hi=2 * N))
    lo_all = min(w['lo'] for w in wins); hi_all = max(w['hi'] for w in wins)
    SA, SB, SN = primary_window(lo_all, hi_all)
    if sources != 'all':
        # source filters: zfamily = odd squarefree norm prime to 3 (zfamily.py: split-squarefree sources);
        #                 odd = odd norm; nosq = ideal (n) squarefree (inert primes and 2 allowed); nosqodd = both
        def sqfree(n):
            d = 2
            while d * d <= n:
                if n % (d * d) == 0:
                    return False
                d += 1
            return True

        def ideal_sqfree(a, b, n):
            # (n) is divisible by the square of a prime ideal iff p^2 | N(n) for a split p with pi^2 | n (checked via valuations), or q | n for inert q
            for p in range(2, int(math.isqrt(n)) + 1):
                if n % (p * p) == 0:
                    if p % 3 == 2:
                        if a % p == 0 and b % p == 0 and n % (p ** 4) == 0:
                            return False
                    else:
                        # p = 1 mod 3 (or p = 3): square of a split prime ideal divides n iff p^2 | n as ideals: test pi^2 | n for pi, pibar
                        # n = pi^2 m  <=>  p^2 | N(n) and the p-part of the ideal is pi^2 or pibar^2 (not pi*pibar = (p))
                        if a % p == 0 and b % p == 0:
                            continue            # p | n as an element: ideal part (p) = pi pibar (or higher), squarefree test below
                        return False
            return True
        if sources == 'zfamily':
            keep = np.array([(n % 2 == 1) and (n % 3 != 0) and sqfree(int(n)) for n in SN])
        elif sources == 'odd':
            keep = np.array([n % 2 == 1 for n in SN])
        elif sources in ('nosq', 'nosqodd'):
            keep = np.array([ideal_sqfree(int(a), int(b), int(n)) and (sources == 'nosq' or n % 2 == 1) for a, b, n in zip(SA, SB, SN)])
        else:
            raise ValueError(sources)
        SA, SB, SN = SA[keep], SB[keep], SN[keep]
    for w in wins:
        w['c0'] = int(np.searchsorted(SN, w['lo'], side='left'))
        w['c1'] = int(np.searchsorted(SN, w['hi'], side='left'))
        w['C'] = w['c1'] - w['c0']
    log(f'B={B}: {len(SA)} source elements in union of windows; ' + ', '.join(f"m={w['m']}: N={w['N']:.1f} C={w['C']}" for w in wins))
    E, Z = sextic_table(PI, SA, SB)
    E32 = E.astype(np.float32); Z32 = Z.astype(np.float32)
    log(f'B={B}: symbol table {E.shape} ({time.time()-t1:.1f}s)')
    # exact diagonals and prime-factor data for the multiplicative surrogate
    for w in wins:
        a_, b_ = SA[w['c0']:w['c1']], SB[w['c0']:w['c1']]
        w['T4'], w['T6'] = diag_counts(a_, b_)
        w['Ex'], _ = small_prime_ideal_factors(a_, b_, SN[w['c0']:w['c1']], w['hi'] + 5)
        w['full'] = full_family_counts(w['N'], R) if w['N'] <= CAPFULL else (0, float('nan'), float('nan'), float('nan'), 0)
    log(f'B={B}: diagonals done ({time.time()-t1:.1f}s)')
    nW = len(wins)
    NSUB = 4
    # accumulators [which][window][subset][moment 2,4,6]
    which = ['actual'] + [f'mult{r}' for r in range(nrep)] + [f'iid{r}' for r in range(nrep)]
    acc = {k: np.zeros((nW, NSUB, 3)) for k in which}
    smax = {k: np.zeros(nW) for k in which}
    top = [[] for _ in range(nW)]
    Sall = [dict() for _ in range(nW)]
    for iw in range(nW):
        for k in which:
            Sall[iw][k] = np.zeros(R)
    nzero = np.zeros(nW)
    Ex_f = [w['Ex'].astype(np.float32) for w in wins]
    for i0 in range(0, R, CH):
        i1 = min(R, i0 + CH)
        inc = Inc[i0:i1]
        Ech = np.rint(inc @ E32).astype(np.int32) % 6
        Zch = (inc @ Z32) > 0.5
        sub = (np.arange(i0, i1) % NSUB)
        for iw, w in enumerate(wins):
            c0, c1 = w['c0'], w['c1']
            msk = ~Zch[:, c0:c1]
            nzero[iw] += np.sum(~msk)
            Ssum = {}
            ph = ZETA6[Ech[:, c0:c1]]
            ph *= msk
            Ssum['actual'] = ph.sum(1)
            for r in range(nrep):
                J = rng.integers(0, 6, size=(i1 - i0, Ex_f[iw].shape[1])).astype(np.float32)
                Er = np.rint(J @ Ex_f[iw].T).astype(np.int64) % 6
                ph = ZETA6[Er]; ph *= msk
                Ssum[f'mult{r}'] = ph.sum(1)
                th = np.exp(2j * np.pi * rng.random((i1 - i0, c1 - c0))); th *= msk
                Ssum[f'iid{r}'] = th.sum(1)
            for k, S in Ssum.items():
                a2 = np.abs(S) ** 2
                Sall[iw][k][i0:i1] = a2
                for s in range(NSUB):
                    q = a2[sub == s]
                    acc[k][iw, s] += [q.sum(), (q ** 2).sum(), (q ** 3).sum()]
                smax[k][iw] = max(smax[k][iw], a2.max())
    results = []
    for iw, w in enumerate(wins):
        N = w['N']
        rec = dict(B=B, m=w['m'], N=N, R=R, C=w['C'], T4=w['T4'], T6=w['T6'],
                   T4N2=w['T4'] / N ** 2, T6N3=(w['T6'] / N ** 3 if w['T6'] is not None else None),
                   zero_frac=float(nzero[iw] / (R * w['C'])))
        q, F4, F6, I4, ni = w['full']
        rec.update(q=q, full_M4=F4 / N ** 2, full_M6=F6 / N ** 3, int_M4=I4 / N ** 2, nint=ni)
        for k in which:
            tot = acc[k][iw].sum(0)
            M2, M4, M6 = tot[0] / (R * N), tot[1] / (R * N ** 2), tot[2] / (R * N ** 3)
            subM6 = acc[k][iw][:, 2] / ((R / NSUB) * N ** 3)
            subM4 = acc[k][iw][:, 1] / ((R / NSUB) * N ** 2)
            s2k = Sall[iw][k]
            rec[k] = dict(M2=M2, M4=M4, M6=M6, se4=float(np.std(s2k ** 2, ddof=1) / math.sqrt(R) / N ** 2),
                          se6=float(np.std(s2k ** 3, ddof=1) / math.sqrt(R) / N ** 3), maxS2=float(smax[k][iw] / N))
        # top rows of the actual family, and the trimmed sixth moment
        s2 = np.sort(Sall[iw]['actual'])[::-1]
        rec['top_S2_over_N'] = (s2[:5] / N).tolist()
        rec['actual_M6_without_top1pct'] = float(np.sum(np.sort(Sall[iw]['actual'] ** 3)[:int(0.99 * R)]) / (R * N ** 3))
        results.append(rec)
    log(f'B={B}: done ({time.time()-t1:.1f}s)')
    return results


def summarize(rec, nrep):
    """surrogate means/sds and z-scores of the actual moments against the multiplicative surrogate."""
    def ms(prefix, key):
        v = np.array([rec[f'{prefix}{r}'][key] for r in range(nrep)])
        return v.mean(), (v.std(ddof=1) if len(v) > 1 else float('nan'))
    a = rec['actual']
    out = {}
    for mom in ('M4', 'M6'):
        mm, ms_ = ms('mult', mom); im, is_ = ms('iid', mom)
        se_pred = math.sqrt(a['se' + mom[1]] ** 2 + (ms_ ** 2 / nrep if nrep > 1 else 0.0))
        out[mom] = dict(mult=mm, mult_sd=ms_, iid=im, iid_sd=is_, ratio=a[mom] / mm, z=(a[mom] - mm) / se_pred, se_pred=se_pred)
    return out


def print_table(results, nrep):
    for mom, ex, tkey, fkey in (('M4', 2, 'T4N2', 'full_M4'), ('M6', 3, 'T6N3', 'full_M6')):
        print(f'\n--- {mom} = sum_u |S_u|^{mom[1]} / (R N^{ex});  actual vs multiplicative surrogate (mean of {nrep}), iid-phase surrogate, '
              f'exact diagonal T/N^{ex} (no coprimality mask), full Dirichlet family mod q ~ R')
        print(f'      B     m       N     C      R  N^{ex}/R |  actual (se)     |  mult  (sd/rep) |   iid  | T/N^{ex}  |  full  | actual/mult |   z   | excess*R/N^{ex}')
        for rec in results:
            s = summarize(rec, nrep)[mom]; a = rec['actual']; N = rec['N']; R = rec['R']
            t = rec[tkey]
            print(f"{rec['B']:7d} {rec['m']:5.2f} {N:7.1f} {rec['C']:5d} {R:6d} {N**ex/R:8.2f} | {a[mom]:8.4f} ({a['se'+mom[1]]:.4f}) | "
                  f"{s['mult']:8.4f} ({s['mult_sd']:.4f}) | {s['iid']:7.4f} | {(t if t is not None else float('nan')):8.4f} | "
                  f"{rec[fkey]:8.2f} | {s['ratio']:9.3f} | {s['z']:+5.2f} | {(a[mom]-s['mult'])*R/N**ex:+.2e}")


if __name__ == '__main__':
    ap = argparse.ArgumentParser()
    ap.add_argument('--B', type=int, nargs='+', required=True)
    ap.add_argument('--m', type=float, nargs='+', default=[0.3, 0.35, 0.43, 0.5])
    ap.add_argument('--nrep', type=int, default=3)
    ap.add_argument('--sources', default='all')
    ap.add_argument('--seed', type=int, default=1)
    ap.add_argument('--out', default=None)
    args = ap.parse_args()
    rng = np.random.default_rng(args.seed)
    allres = []
    for B in args.B:
        res = run(B, args.m, args.nrep, args.sources, rng)
        allres.extend(res)
        print_table(res, args.nrep)
        if args.out:
            json.dump(dict(args=vars(args), results=allres), open(args.out, 'w'), indent=1, default=lambda o: o.tolist() if hasattr(o, 'tolist') else str(o))
    print('\n=== all ===')
    print_table(allres, args.nrep)
