"""Tail of the plain eighth moment in the thin sextic family (sanity check for STRATEGIES.md, Prop. 0).

The target sum_z|A|^4 << Z^{1+eps} N^2 forces max_z |A(z)|^2 <= Z^{1/2+eps} * mean|A|^2 for EVERY row.
Here: max|A|^2/mean|A|^2 (against Z^{1/2}), and the share of sum|A|^4 carried by the top rows, for the actual
family and one multiplicative surrogate.  Same family, weights and code path as eighth_probe.py.
usage: python3 -I strat_tail.py --B 30000 100000 --mu 0.6 0.8 0.93 1.0
"""
import sys, os, math, time, argparse
sys.dont_write_bytecode = True
HERE = os.path.dirname(os.path.abspath(__file__))
MP = os.path.normpath(os.path.join(HERE, '..', 'moments_probe'))
sys.path.insert(0, MP)
import numpy as np
import scipy.sparse as sps
import probeB as PB
from probeC import weight, support


def per_row(B, mus, rng, CH=1500):
    ar = PB.Arith(2 * B + 10)
    PI = PB.prime_ideals(ar, 2 * B)
    rows = PB.build_rows(PI['norm'], B, 2 * B)
    R = len(rows)
    nf = np.array([len(r) for r in rows])
    indptr = np.zeros(R + 1, dtype=np.int64); indptr[1:] = np.cumsum(nf)
    indices = np.fromiter((j for r in rows for j in r), dtype=np.int64, count=int(indptr[-1]))
    Inc = sps.csr_matrix((np.ones(len(indices), dtype=np.float32), indices, indptr), shape=(R, len(PI['norm'])))
    lo_f, hi_f = support('smooth')
    ms = sorted(set(m / 2 for m in mus))
    lo_all = min(B ** m for m in ms) * lo_f; hi_all = max(B ** m for m in ms) * hi_f
    SA, SB, SN = PB.primary_window(int(math.floor(lo_all)), int(math.ceil(hi_all)) + 1)
    Wm = np.stack([weight(SN / B ** m, 'smooth') for m in ms], axis=1).astype(np.float32)
    E, Zt = PB.sextic_table(PI, SA, SB)
    E32 = E.astype(np.float32); Z32 = Zt.astype(np.float32)
    Ex, _ = PB.small_prime_ideal_factors(SA, SB, SN, int(math.ceil(hi_all)) + 5)
    ExS = sps.csr_matrix(Ex); nI = Ex.shape[1]
    X = {k: np.zeros((R, len(ms)), dtype=np.complex128) for k in ('act', 'mul')}
    Z6 = PB.ZETA6.astype(np.complex64)
    for i0 in range(0, R, CH):
        i1 = min(R, i0 + CH)
        inc = Inc[i0:i1]
        Ech = np.rint(inc @ E32).astype(np.int64) % 6
        msk = ((inc @ Z32) < 0.5).astype(np.float32)
        X['act'][i0:i1] = (Z6[Ech] * msk) @ Wm
        J = rng.integers(0, 6, size=(nI, i1 - i0)).astype(np.float32)
        Er = np.rint(np.asarray(ExS @ J)).astype(np.int64).T % 6
        X['mul'][i0:i1] = (Z6[Er] * msk) @ Wm
    return R, ms, X


def stats(A2):
    """A2 = |A|^2 per row. Returns kappa8, max/mean, shares of sum|A|^4 in the top 0.1%, 1%, 10% rows."""
    m = A2.mean()
    A4 = np.sort(A2 ** 2)[::-1]
    tot = A4.sum()
    R = len(A2)
    sh = [A4[:max(1, int(round(f * R)))].sum() / tot for f in (0.001, 0.01, 0.1)]
    return dict(k8=float((A2 ** 2).mean() / m ** 2), mx=float(A2.max() / m), sh=sh)


if __name__ == '__main__':
    ap = argparse.ArgumentParser()
    ap.add_argument('--B', type=int, nargs='+', required=True)
    ap.add_argument('--mu', type=float, nargs='+', required=True)
    args = ap.parse_args()
    rng = np.random.default_rng(5)
    print(f"{'B':>7} {'R':>6} {'mu':>5} {'Z^1/2':>7} | {'kappa8':>7} {'max/mean':>9} {'top.1%':>7} {'top1%':>7} {'top10%':>7}"
          f" | {'k8 mult':>7} {'max/mean':>9} {'top1%':>7}")
    for B in args.B:
        t0 = time.time()
        R, ms, X = per_row(B, args.mu, rng)
        for mu in args.mu:
            j = ms.index(mu / 2)
            a = stats(np.abs(X['act'][:, j]) ** 4)       # |A|^2 = |X|^4 (X1 = X2)
            s = stats(np.abs(X['mul'][:, j]) ** 4)
            print(f"{B:7d} {R:6d} {mu:5.2f} {math.sqrt(B):7.1f} | {a['k8']:7.2f} {a['mx']:9.2f} "
                  f"{a['sh'][0]:7.3f} {a['sh'][1]:7.3f} {a['sh'][2]:7.3f} | {s['k8']:7.2f} {s['mx']:9.2f} {s['sh'][1]:7.3f}",
                  flush=True)
        print(f"   ({time.time()-t0:.1f}s)", flush=True)
