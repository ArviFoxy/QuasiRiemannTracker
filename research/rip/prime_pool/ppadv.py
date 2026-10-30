"""ppadv.py -- worst-case pool weights and the extended-s window (s up to ~0.95, m from 0).

    python3 -I ppadv.py B [--ms 0,0.25,0.4] [--ss 0.5,0.6,0.7,0.8,0.9] [--kinds smooth,plain] [--out results/adv_B.json]

For X = X1 = X2 (length B^m) the quadratic form in the pool weights a is
    F(a)    = sum_z |X(z)|^4 |sum_P a_P chi_z(P)|^2 = a^H M a,      M = E_Q^H diag(|X|^4) E_Q   (n x n),
    Dcop(a) = a^H Delta a,                                           Delta = R * A diag(rho) A^H
(A = sparse convolution matrix of d = w*w with the pool; rho = coprimality factor).  Reported per (m, s):
  * F/Dcop for the standard variants (ones, rand, t5, t20, gauss_simple, gauss_canon);
  * SUP_L2   = lambda_max(M, Delta): the sup over ALL complex weight vectors -- an upper bound for every weight class;
  * SUP_UNI  = best unimodular a found by the unimodular power iteration a <- phase(M a) (8 random starts + start at the
               phases of the top eigenvector): a lower bound for the sup over unimodular weights;
  * Reff     = (sum |X|^4)^2 / sum |X|^8  (participation ratio of the row weights) and the random-matrix guess (1 + sqrt(n/Reff))^2.
"""
import os, sys, time, json, math, argparse
import numpy as np
import scipy.linalg as sla
sys.dont_write_bytecode = True
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from ppcore import *


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('B', type=int)
    ap.add_argument('--ms', default='0,0.25,0.4')
    ap.add_argument('--ss', default='0.5,0.6,0.7,0.8,0.9')
    ap.add_argument('--kinds', default='smooth')
    ap.add_argument('--seeds', type=int, default=4)
    ap.add_argument('--maxn', type=int, default=3000)
    ap.add_argument('--out', default=None)
    args = ap.parse_args()
    B = args.B
    ms = [float(x) for x in args.ms.split(',')]
    ss = [float(x) for x in args.ss.split(',')]
    kinds = args.kinds.split(',')
    t0 = time.time()
    tick = lambda msg: print('[%6.1fs] %s' % (time.time() - t0, msg), flush=True)
    ID = Ideals(2 * B)
    rows = enumerate_rows(B, ID); R = rows['R']
    PID = rows['PID']; uid = np.unique(PID[PID >= 0]); LOC = local_index(PID, uid)
    tick('B=%d R=%d' % (B, R))
    # X(z) for each (kind, m)
    PA, PB, PN = primary_elements(B ** max(max(ms), 0.05))
    Tp = symbol_table(ID, uid, PA, PB)
    chip = np.zeros((R, len(PA)), complex)
    CH = max(200, 2_000_000 // max(1, len(PA)))
    for r0 in range(0, R, CH):
        chip[r0:r0 + CH] = chi_chunk(LOC, Tp, r0, min(R, r0 + CH))
    combos = []
    for m in ms:
        if m == 0: combos.append(('plain', 0.0))              # X = chi_z(-1): |X| = 1 (smooth weight would vanish)
        else: combos += [(k, m) for k in kinds]
    Wc = np.stack([weight_vector(PN, B ** m, k) for k, m in combos], axis=1)
    X = chip @ Wc
    w4 = np.abs(X) ** 4
    Reff = w4.sum(0) ** 2 / (w4 ** 2).sum(0)
    base = {}
    pmax_plain = float(B ** max(ms))
    res = dict(B=B, R=R, combos=[list(c) for c in combos], Reff=Reff.tolist(), entries=[], time=None)
    selfc = {}
    for ci, (k, m) in enumerate(combos):
        ka, kb, d = self_convolution(PA, PB, Wc[:, ci])
        selfc[ci] = (ka, kb, d)
    for s in ss:
        pool = split_prime_sources(ID, B ** s, 2 * B ** s)
        n = len(pool)
        if n < 2 or n > args.maxn:
            tick('s=%.2f: pool size %d skipped' % (s, n)); continue
        TA = np.array([P['a'] for P in pool], I64); TB = np.array([P['b'] for P in pool], I64)
        Tq = symbol_table(ID, uid, TA, TB)
        gs = np.zeros(n, complex); gc = np.zeros(n, complex)
        for i, P in enumerate(pool): gs[i], gc[i] = gauss_sums(P)
        lnN = np.log(np.array([P['p'] for P in pool], float))
        rng = np.random.default_rng([B, int(round(1000 * s))])
        var = {'ones': np.ones(n, complex), 't5': np.exp(-5j * lnN), 't20': np.exp(-20j * lnN),
               'gauss_simple': np.conj(gs), 'gauss_canon': np.conj(gc)}
        for i in range(args.seeds): var['rand%d' % i] = np.exp(2j * np.pi * rng.random(n))
        vnames = list(var); Avar = np.stack([var[k] for k in vnames], axis=1)
        M = np.zeros((len(combos), n, n), complex)
        Fv = np.zeros((len(combos), len(vnames))); F2v = np.zeros_like(Fv)
        CHR = max(100, 1_500_000 // n)
        for r0 in range(0, R, CHR):
            r1 = min(R, r0 + CHR)
            E = chi_chunk(LOC, Tq, r0, r1)
            Ec = E.conj().T
            q2 = np.abs(E @ Avar) ** 2
            for ci in range(len(combos)):
                M[ci] += (Ec * w4[r0:r1, ci][None, :]) @ E
                f = w4[r0:r1, ci][:, None] * q2
                Fv[ci] += f.sum(0); F2v[ci] += (f ** 2).sum(0)
        pmax = int(max(pmax_plain, 2 * B ** s + 1))
        for ci, (k, m) in enumerate(combos):
            ka, kb, d = selfc[ci]
            Am, ca, cb = conv_matrix(ka, kb, d, TA, TB)
            rho = rho_elements(ID, ca, cb, pmax)
            Dl = (R * (Am.multiply(rho[None, :]) @ Am.conj().T)).toarray()
            Dl = (Dl + Dl.conj().T) / 2
            Mi = M[ci]; Mi = (Mi + Mi.conj().T) / 2
            out = dict(kind=k, m=m, s=s, n=n, T=2 * m + s, Reff=float(Reff[ci]))
            ratios = {}; ses = {}
            for vi, name in enumerate(vnames):
                a = var[name]
                dd = float((a.conj() @ Dl @ a).real)
                ratios[name] = float((a.conj() @ Mi @ a).real / dd)
                ses[name] = math.sqrt(max(0.0, F2v[ci, vi] - Fv[ci, vi] ** 2 / R)) / dd
            out['var'] = ratios; out['var_se'] = ses
            # sup over all complex a: generalized top eigenvalue
            try:
                ev = sla.eigh(Mi, Dl, eigvals_only=True, subset_by_index=[n - 1, n - 1])
                out['sup_l2'] = float(ev[0])
                w_, V_ = sla.eigh(Mi, Dl, subset_by_index=[n - 1, n - 1])
                top = V_[:, 0]
            except Exception as e:                       # Delta not positive definite (rare): ridge
                Dr = Dl + 1e-9 * np.trace(Dl).real / n * np.eye(n)
                w_, V_ = sla.eigh(Mi, Dr, subset_by_index=[n - 1, n - 1])
                out['sup_l2'] = float(w_[0]); top = V_[:, 0]
            # unimodular power iteration
            best = 0.0
            starts = [np.exp(1j * np.angle(top))] + [np.exp(2j * np.pi * rng.random(n)) for _ in range(8)]
            for a in starts:
                for _ in range(200):
                    b = Mi @ a
                    an = np.exp(1j * np.angle(b))
                    if np.allclose(an, a, atol=1e-12): a = an; break
                    a = an
                best = max(best, float((a.conj() @ Mi @ a).real / (a.conj() @ Dl @ a).real))
            out['sup_uni'] = best
            out['mp_guess'] = float((1 + math.sqrt(n / Reff[ci])) ** 2)
            res['entries'].append(out)
            tick('kind=%-6s m=%.2f s=%.2f n=%4d T=%.2f | ones %.3f canon %.3f rand0 %.3f | sup_uni %.3f sup_l2 %.3f | MP guess %.3f (Reff=%.0f, R=%d)' % (
                k, m, s, n, 2 * m + s, ratios['ones'], ratios['gauss_canon'], ratios['rand0'], best, out['sup_l2'], out['mp_guess'], Reff[ci], R))
    res['time'] = time.time() - t0
    outp = args.out or os.path.join(os.path.dirname(os.path.abspath(__file__)), 'results', 'adv_%d.json' % B)
    os.makedirs(os.path.dirname(outp), exist_ok=True)
    with open(outp, 'w') as f: json.dump(res, f)
    tick('wrote %s' % outp)


if __name__ == '__main__':
    main()
