"""Random multiplicative model applied to the DUAL representation (primerows_dual.py) of each row's sum.

For a sample of rows (stratified by class and by the 3-part c of the conductor), with D_u the dual sum
  c >= 1: D_u = 2N/sqrt(3 Nf) sum_n conj chi_u(n) Gh(2 sqrt(N N(n)/(3 Nf))),                Nf = 3^c N(u)
  c  = 0: D_u = 2N/(3 sqrt(3 N(u))) sum_n conj chi_u(n) [2 sum_j lam^-j g_j(n) - lam g_{-1}(n)],   lam = chi_u(1 - w),
(|D_u| = |S_u| exactly), we replace conj chi_u(n) by a random completely multiplicative f (i.i.d. uniform mu_6 at prime
ideals; f(n) = 0 when gcd(n, u) != 1) and compute E|D_u(f)|^6 / mass^3 ("dual surrogate", dsur), next to the ordinary
surrogate of the original sum (osur) for the same rows.  Prediction of the dual picture: actual/osur ~ dsur/osur when
the dual is the shorter side.
usage: python3 -I primerows_dualsurr.py --B 100000 --m 0.5 0.6 0.7 --nrow 600 --K 128 [--run logsP/run_1e5.npz]
"""
import sys, os, math, time, argparse
sys.dont_write_bytecode = True
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import numpy as np
import scipy.sparse as sps
import probeB as PB
import primerows_core as PC
import primerows_dual as PD

Z6 = PC.Z6


def factor_matrix(A, Bb, NN, Nmax):
    Ex, _ = PB.small_prime_ideal_factors(A, Bb, NN, Nmax + 5)
    return Ex


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--B', type=int, required=True)
    ap.add_argument('--m', type=float, nargs='+', required=True)
    ap.add_argument('--nrow', type=int, default=600, help='rows per (class, c) stratum')
    ap.add_argument('--K', type=int, default=128)
    ap.add_argument('--batch', type=int, default=8, help='rows sharing one set of K draws')
    ap.add_argument('--rhomax', type=float, default=3.5)
    ap.add_argument('--seed', type=int, default=5)
    ap.add_argument('--run', default=None, help='primerows_run.py npz with the same B (for all-row actual / osur)')
    ap.add_argument('--out', default=None)
    a = ap.parse_args()
    t0 = time.time()
    rng = np.random.default_rng(a.seed)
    gh = PD.Ghat('smooth', rmax=a.rhomax + 0.5, drho=0.001, ns=8001)
    B = a.B
    st = PC.Setup(B, a.m, 'smooth')
    PI = st.PI
    cexp = np.where(st.kres == 0, 0, np.where(st.kres == 3, 1, 2))
    strata = {}
    for cname, sel in (('prime', st.nf == 1), ('comp7', (st.nf >= 2) & (st.minnorm == 7)), ('compother', (st.nf >= 2) & (st.minnorm > 7))):
        for c in (0, 1, 2):
            idx = np.flatnonzero(sel & (cexp == c))
            strata[(cname, c)] = rng.choice(idx, size=min(a.nrow, len(idx)), replace=False)
    run = np.load(a.run) if a.run else None
    if run is not None:
        assert np.array_equal(run['normu'], st.normu) and np.array_equal(run['nf'], st.nf), 'run npz rows differ'
    results = []
    for m in a.m:
        im_run = None
        if run is not None:
            im_run = int(np.argmin(np.abs(run['ms'] - m))); assert abs(run['ms'][im_run] - m) < 1e-9
        N = B ** m
        mass = st.mass[st.ms.index(m)]
        # dual terms: all primary n up to the largest reach
        Xmax = a.rhomax ** 2 * 9 * 3 * 2 * B / (4 * N) * 1.02
        A, Bb, NN = PB.primary_window(1, int(Xmax) + 2)
        T = len(NN)
        Ex = factor_matrix(A, Bb, NN, int(Xmax) + 2)
        ExS = sps.csr_matrix(Ex)
        nIx = Ex.shape[1]
        exb = (Ex[:, :-1] > 0)
        PId = PB.prime_ideals(PB.Arith(int(Xmax) + 15), int(Xmax) + 7)
        nchk = min(len(PId['norm']), len(PI['norm']))
        assert np.array_equal(PId['norm'][:nchk], PI['norm'][:nchk]) and np.array_equal(PId['a'][:nchk], PI['a'][:nchk])
        print(f'[m={m}] N={N:.1f} dual terms T={T} primes={nIx} ({time.time()-t0:.1f}s)', flush=True)
        # original sources (for osur on the same rows)
        Wm = st.W[:, st.ms.index(m)].astype(np.float64)
        sel_src = Wm > 0
        oEx = st.ExS[sel_src]; oW = Wm[sel_src]; oexb = (st.Ex[sel_src][:, :st.nI] > 0)
        for (cname, c), rows_idx in strata.items():
            acc_d = []; acc_o = []; act = []
            for b0 in range(0, len(rows_idx), a.batch):
                bidx = rows_idx[b0:b0 + a.batch]
                H = np.zeros((T, len(bidx)), dtype=np.complex64)
                Ho = np.zeros((len(oW), len(bidx)), dtype=np.complex64)
                for t, i in enumerate(bidx):
                    fac = list(st.rows[i]); Nu = int(st.normu[i]); k = int(st.kres[i])
                    live = np.ones(T, bool)
                    for j in fac:
                        if PI['norm'][j] <= Xmax:
                            live &= ~exb[:, j]
                    if k != 0:
                        Nf = Nu * (3 if k == 3 else 9)
                        h = gh(2 * np.sqrt(N * NN / (3.0 * Nf))) * (2 * N / math.sqrt(3 * Nf))
                    else:
                        lam = PD.chi_val(PI, fac, np.array([1]), np.array([-1]))[0]
                        h = -lam * gh(2 * np.sqrt(N * NN / (9.0 * Nu))).astype(np.complex128)
                        j = 0
                        while True:
                            arg = 2 * np.sqrt(N * (3.0 ** j) * NN / (3.0 * Nu))
                            if arg.min() > gh.rmax:
                                break
                            h += 2 * np.conj(lam) ** j * gh(arg)
                            j += 1
                        h *= 2 * N / (3 * math.sqrt(3 * Nu))
                    H[:, t] = h * live / math.sqrt(mass)
                    olive = np.ones(len(oW), bool)
                    for jj in st.maskkey[i]:
                        olive &= ~oexb[:, jj]
                    Ho[:, t] = oW * olive / math.sqrt(mass)
                    if run is None:
                        act.append(np.nan)
                    else:
                        act.append(abs(run['S'][i, im_run]) ** 2 / run['mass'][im_run])
                J = rng.integers(0, 6, size=(nIx, a.K)).astype(np.float32)
                F = Z6[np.rint(np.asarray(ExS @ J)).astype(np.int64) % 6]                    # T x K
                acc_d.append((np.abs(F.T @ H).astype(np.float64) ** 2))                      # K x rows
                Jo = rng.integers(0, 6, size=(st.ExS.shape[1], a.K)).astype(np.float32)
                Fo = Z6[np.rint(np.asarray(oEx @ Jo)).astype(np.int64) % 6]
                acc_o.append((np.abs(Fo.T @ Ho).astype(np.float64) ** 2))
            d2 = np.concatenate(acc_d, axis=1); o2 = np.concatenate(acc_o, axis=1)
            rec = dict(m=m, cls=cname, c=c, n=len(rows_idx), dM2=d2.mean(), oM2=o2.mean(), dM6=(d2 ** 3).mean(), oM6=(o2 ** 3).mean(),
                       dM4=(d2 ** 2).mean(), oM4=(o2 ** 2).mean())
            if run is not None:
                acta = np.array(act)
                rec['aM6_sample'] = float((acta ** 3).mean()); rec['aM2_sample'] = float(acta.mean())
                # all rows of this stratum in the run
                sel = {'prime': st.nf == 1, 'comp7': (st.nf >= 2) & (st.minnorm == 7), 'compother': (st.nf >= 2) & (st.minnorm > 7)}[cname] & (cexp == c)
                a2 = np.abs(run['S'][sel, im_run]) ** 2 / run['mass'][im_run]
                s6 = run['acc'][sel, im_run, 2, :].sum(-1) / int(run['K'])
                rec['aM6_all'] = float((a2 ** 3).mean()); rec['oM6_all'] = float(s6.mean()); rec['n_all'] = int(sel.sum())
            results.append(rec)
            msg = (f"  m={m} {cname:9s} c={c} n={rec['n']:4d}  M2 dual/orig {rec['dM2']:.3f}/{rec['oM2']:.3f}   M6 dsur {rec['dM6']:7.3f}  osur {rec['oM6']:7.3f}"
                   f"  dsur/osur {rec['dM6']/rec['oM6']:.3f}")
            if run is not None:
                msg += f"  | all rows: actual {rec['aM6_all']:.3f} osur {rec['oM6_all']:.3f} act/osur {rec['aM6_all']/rec['oM6_all']:.3f}"
            print(msg + f'  ({time.time()-t0:.0f}s)', flush=True)
    if a.out:
        import json
        json.dump(dict(args=vars(a), results=results), open(a.out, 'w'), indent=1)


if __name__ == '__main__':
    main()
