"""PROBE C (follow-up to probe B, D4): why does the thin sextic family's sixth moment sit *below* the random
multiplicative model?  Hypotheses tested:
  H_dual  the functional equation: for m > 1/2 the sum is a dual sum of length B/N, so M6_actual(m) ~ M6_mult(1 - m);
  H_cut   the sharp annulus [N, 2N) dualizes to oscillatory weights; with a smooth weight the deficit at m = 1/2 vanishes;
  H_row   row structure: prime vs composite rows, rows with an inert prime factor ((rational/q)_6 = 1 for inert q);
  H_2     the inert prime 2 among the sources (supplementary law): drop sources with 2 | n.
Weighted sums S_u = sum_n w(N(n)/N) chi_u(n) over primary n (ideals prime to 3), rows as in probe B (squarefree,
N(u) in [B, 2B], prime to 6).  Weights: sharp = 1_[1,2); smooth = exp(-(log t)^2 / (2 * 0.3^2)) on t in [e^-1, e].
The multiplicative surrogate uses i.i.d. uniform mu_6 values at prime ideals and the same coprimality mask.
Moments are normalized by the weight mass: M_k = sum_u |S_u|^k / (R * (sum_n w_n^2)^(k/2)).
usage: python3 -I probeC.py --B 30000 --m 0.3 0.4 0.5 0.6 0.7 0.8 --weight smooth [--src odd] [--nrep 4]
"""
import sys, os, math, time, argparse, json
sys.dont_write_bytecode = True
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import numpy as np
import scipy.sparse as sps
import probeB as PB

SIG = 0.3


def weight(t, kind):
    if kind == 'sharp':
        return ((t >= 1.0) & (t < 2.0)).astype(np.float64)
    w = np.exp(-np.log(np.maximum(t, 1e-300)) ** 2 / (2 * SIG ** 2))
    w[(t < math.exp(-1)) | (t >= math.e)] = 0.0
    return w


def support(kind):
    return (1.0, 2.0) if kind == 'sharp' else (math.exp(-1), math.e)


def run(B, ms, kind, nrep, src, rng, CH=1500):
    t0 = time.time()
    ar = PB.Arith(2 * B + 10)
    PI = PB.prime_ideals(ar, 2 * B)
    rows = PB.build_rows(PI['norm'], B, 2 * B)
    R = len(rows)
    nf = np.array([len(r) for r in rows])
    has_inert = np.array([any(PI['kind'][j] == 1 for j in r) for r in rows])
    minnorm = np.array([min(int(PI['norm'][j]) for j in r) for r in rows])
    classes = dict(all=np.ones(R, bool), prime=(nf == 1), composite=(nf >= 2), inert=has_inert, noinert=~has_inert,
                   comp_small=(nf >= 2) & (minnorm <= 200), comp_large=(nf >= 2) & (minnorm > 200),
                   prime_split=(nf == 1) & ~has_inert, prime_inert=(nf == 1) & has_inert)
    indptr = np.zeros(R + 1, dtype=np.int64); indptr[1:] = np.cumsum(nf)
    indices = np.fromiter((j for r in rows for j in r), dtype=np.int64, count=int(indptr[-1]))
    Inc = sps.csr_matrix((np.ones(len(indices), dtype=np.float32), indices, indptr), shape=(R, len(PI['norm'])))
    lo_f, hi_f = support(kind)
    lo_all = min(B ** m for m in ms) * lo_f; hi_all = max(B ** m for m in ms) * hi_f
    SA, SB, SN = PB.primary_window(int(math.floor(lo_all)), int(math.ceil(hi_all)) + 1)
    if src == 'odd':
        keep = SN % 2 == 1
        SA, SB, SN = SA[keep], SB[keep], SN[keep]
    nS = len(SA)
    W = np.stack([weight(SN / B ** m, kind) for m in ms], axis=1).astype(np.float32)      # nS x nm
    mass = (W.astype(np.float64) ** 2).sum(0)
    E, Z = PB.sextic_table(PI, SA, SB)
    E32 = E.astype(np.float32); Z32 = Z.astype(np.float32)
    Ex, _ = PB.small_prime_ideal_factors(SA, SB, SN, int(math.ceil(hi_all)) + 5)
    ExS = sps.csr_matrix(Ex)                                                                  # nS x nI
    nI = Ex.shape[1]
    print(f'B={B} R={R} sources={nS} primes(src)={nI} kind={kind} src={src} ({time.time()-t0:.1f}s)', flush=True)
    keys = ['act'] + [f'mul{r}' for r in range(nrep)]
    S2 = {k: np.zeros((R, len(ms))) for k in keys}
    Z6 = PB.ZETA6.astype(np.complex64)
    for i0 in range(0, R, CH):
        i1 = min(R, i0 + CH)
        inc = Inc[i0:i1]
        Ech = np.rint(inc @ E32).astype(np.int64) % 6
        msk = ((inc @ Z32) < 0.5).astype(np.float32)
        ph = Z6[Ech] * msk
        S2['act'][i0:i1] = np.abs(ph @ W) ** 2
        for r in range(nrep):
            J = rng.integers(0, 6, size=(nI, i1 - i0)).astype(np.float32)
            Er = np.rint(np.asarray(ExS @ J)).astype(np.int64).T % 6
            ph = Z6[Er] * msk
            S2[f'mul{r}'][i0:i1] = np.abs(ph @ W) ** 2
    out = []
    for im, m in enumerate(ms):
        rec = dict(B=B, m=m, kind=kind, src=src, R=R, mass=float(mass[im]))
        for cname, cm in classes.items():
            if cm.sum() < 50:
                continue
            a = S2['act'][cm, im] / mass[im]
            mm = [S2[f'mul{r}'][cm, im] / mass[im] for r in range(nrep)]
            M = lambda x, k: float(np.mean(x ** (k // 2)))
            mu6 = [M(x, 6) for x in mm]; mu4 = [M(x, 4) for x in mm]
            rec[cname] = dict(n=int(cm.sum()), M2=M(a, 2), M4=M(a, 4), M6=M(a, 6), mul_M2=float(np.mean([M(x, 2) for x in mm])),
                              mul_M4=float(np.mean(mu4)), mul_M6=float(np.mean(mu6)), mul_M6_sd=float(np.std(mu6, ddof=1) if nrep > 1 else 0),
                              max_act=float(a.max()), max_mul=float(np.mean([x.max() for x in mm])),
                              q999_act=float(np.quantile(a, 0.999)), q999_mul=float(np.mean([np.quantile(x, 0.999) for x in mm])))
        out.append(rec)
    print(f'B={B} done ({time.time()-t0:.1f}s)', flush=True)
    return out


def show(res):
    for rec in res:
        print(f"\nB={rec['B']} m={rec['m']} {rec['kind']} src={rec['src']} R={rec['R']}")
        print('  class        n     M2    M4(act/mul)      M6 act / mul (sd)      ratio   q999 act/mul   max act/mul')
        for c in ('all', 'prime', 'prime_split', 'prime_inert', 'composite', 'comp_small', 'comp_large', 'inert', 'noinert'):
            if c not in rec:
                continue
            d = rec[c]
            print(f"  {c:10s} {d['n']:6d} {d['M2']:.3f}  {d['M4']:.3f}/{d['mul_M4']:.3f}   {d['M6']:.3f} / {d['mul_M6']:.3f} ({d['mul_M6_sd']:.3f})"
                  f"   {d['M6']/d['mul_M6']:.3f}   {d['q999_act']:.2f}/{d['q999_mul']:.2f}   {d['max_act']:.2f}/{d['max_mul']:.2f}")


if __name__ == '__main__':
    ap = argparse.ArgumentParser()
    ap.add_argument('--B', type=int, nargs='+', required=True)
    ap.add_argument('--m', type=float, nargs='+', required=True)
    ap.add_argument('--weight', default='smooth')
    ap.add_argument('--src', default='all')
    ap.add_argument('--nrep', type=int, default=4)
    ap.add_argument('--seed', type=int, default=7)
    ap.add_argument('--out', default=None)
    args = ap.parse_args()
    rng = np.random.default_rng(args.seed)
    allres = []
    for B in args.B:
        res = run(B, args.m, args.weight, args.nrep, args.src, rng)
        show(res); allres.extend(res)
        if args.out:
            json.dump(dict(args=vars(args), results=allres), open(args.out, 'w'), indent=1)
