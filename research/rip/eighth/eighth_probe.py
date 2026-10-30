"""Plain eighth moment of the thin sextic family (input of the D1 dispersion route):
  kappa8 = mean_u |A(u)|^4 / (mean_u |A(u)|^2)^2,  A = X1 X2,  X_i = sum_n w(N(n)/N_i) chi_u(n),  N_i = B^{m_i}.
Lindelof on average <=> kappa8 = B^{o(1)}; an N-term would make kappa8 grow like (N1 N2)^2 / R past the row count.
Compared with the multiplicative surrogate (i.i.d. mu_6 at prime ideals, same coprimality mask).
usage: python3 -I eighth_probe.py --B 30000 100000 --mu 0.6 0.8 0.93 1.0 [--nrep 3]
"""
import sys, os, math, time, argparse, json
sys.dont_write_bytecode = True
HERE = os.path.dirname(os.path.abspath(__file__))
MP = os.path.normpath(os.path.join(HERE, '..', 'moments_probe'))
sys.path.insert(0, MP)
import numpy as np
import scipy.sparse as sps
import probeB as PB
from probeC import weight, support


def run(B, mus, nrep, rng, CH=1500):
    t0 = time.time()
    ar = PB.Arith(2 * B + 10)
    PI = PB.prime_ideals(ar, 2 * B)
    rows = PB.build_rows(PI['norm'], B, 2 * B)
    R = len(rows)
    nf = np.array([len(r) for r in rows])
    indptr = np.zeros(R + 1, dtype=np.int64); indptr[1:] = np.cumsum(nf)
    indices = np.fromiter((j for r in rows for j in r), dtype=np.int64, count=int(indptr[-1]))
    Inc = sps.csr_matrix((np.ones(len(indices), dtype=np.float32), indices, indptr), shape=(R, len(PI['norm'])))
    lo_f, hi_f = support('smooth')
    ms = sorted(set(m / 2 for m in mus))                       # balanced split m1 = m2 = mu/2
    lo_all = min(B ** m for m in ms) * lo_f; hi_all = max(B ** m for m in ms) * hi_f
    SA, SB, SN = PB.primary_window(int(math.floor(lo_all)), int(math.ceil(hi_all)) + 1)
    Wm = np.stack([weight(SN / B ** m, 'smooth') for m in ms], axis=1).astype(np.float32)
    E, Z = PB.sextic_table(PI, SA, SB)
    E32 = E.astype(np.float32); Z32 = Z.astype(np.float32)
    Ex, _ = PB.small_prime_ideal_factors(SA, SB, SN, int(math.ceil(hi_all)) + 5)
    ExS = sps.csr_matrix(Ex); nI = Ex.shape[1]
    keys = ['act'] + [f'mul{r}' for r in range(nrep)]
    X = {k: np.zeros((R, len(ms)), dtype=np.complex128) for k in keys}
    Z6 = PB.ZETA6.astype(np.complex64)
    for i0 in range(0, R, CH):
        i1 = min(R, i0 + CH)
        inc = Inc[i0:i1]
        Ech = np.rint(inc @ E32).astype(np.int64) % 6
        msk = ((inc @ Z32) < 0.5).astype(np.float32)
        X['act'][i0:i1] = (Z6[Ech] * msk) @ Wm
        for r in range(nrep):
            J = rng.integers(0, 6, size=(nI, i1 - i0)).astype(np.float32)
            Er = np.rint(np.asarray(ExS @ J)).astype(np.int64).T % 6
            X[f'mul{r}'][i0:i1] = (Z6[Er] * msk) @ Wm
    out = []
    for mu in mus:
        j = ms.index(mu / 2)
        rec = dict(B=B, mu=mu, R=R, NN=float(B ** mu), NN2_over_R=float(B ** (2 * mu) / R))
        for k in keys:
            A2 = np.abs(X[k][:, j]) ** 4                         # |A|^2 = |X1 X2|^2 with X1 = X2
            rec[k] = dict(m2=float(A2.mean()), kappa8=float((A2 ** 2).mean() / A2.mean() ** 2),
                          kappa6=float((A2 ** 1.5).mean() / A2.mean() ** 1.5))
        out.append(rec)
    print(f'B={B} R={R} sources={len(SA)} ({time.time()-t0:.1f}s)', flush=True)
    return out


if __name__ == '__main__':
    ap = argparse.ArgumentParser()
    ap.add_argument('--B', type=int, nargs='+', required=True)
    ap.add_argument('--mu', type=float, nargs='+', required=True)
    ap.add_argument('--nrep', type=int, default=3)
    ap.add_argument('--out', default=None)
    args = ap.parse_args()
    rng = np.random.default_rng(11)
    allres = []
    for B in args.B:
        res = run(B, args.mu, args.nrep, rng)
        for r in res:
            mk = [r[f'mul{i}']['kappa8'] for i in range(args.nrep)]
            print(f"  B={r['B']} mu={r['mu']:.2f}  (N1N2)^2/R={r['NN2_over_R']:.1f}  kappa8 act={r['act']['kappa8']:.3f}  "
                  f"mult={np.mean(mk):.3f}±{np.std(mk):.3f}  ratio={r['act']['kappa8']/np.mean(mk):.3f}", flush=True)
        allres.extend(res)
        if args.out:
            json.dump(dict(args=vars(args), results=allres), open(args.out, 'w'), indent=1)
