"""ppgrid.py -- measure F/D on the (m, s) grid for ONE value of B.

    python3 -I ppgrid.py B [--out results/grid_B.json] [--seeds 8] [--ms 0.25,0.3,0.35,0.4] [--ss 0.05,...,0.45]

F(m, W, s, variant) = sum_z |X(z)|^4 |Q(z)|^2   with  X = X1 = X2 = sum_{n primary, N(n) <= B^m} W(N(n)/B^m) chi_z(n),
                                                       Q = sum_{P split primary prime, P0 < N(P) <= 2 P0} a_P chi_z(P),  P0 = B^s.
D = R * sum_m |c_m|^2  (c = coefficient vector of X1 X2 Q over ideals).   Dcop = same with the coprimality factor
(fraction of rows z coprime to m, prod_{pi | m} N(pi)/(N(pi)+1)); it is the exact expectation of F under independent
sextic characters (random-sign model), so F/Dcop isolates arithmetic structure.  SE: row-sampling standard error of F.
Control: Q replaced by a plain sum X3 = sum_{N(n) <= P0} W chi_z(n) (same kind of weight W).
Rows are streamed in chunks; symbol tables are cached per prime ideal.
"""
import os, sys, time, json, math, argparse
import numpy as np
sys.dont_write_bytecode = True
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from ppcore import *


def parse():
    ap = argparse.ArgumentParser()
    ap.add_argument('B', type=int)
    ap.add_argument('--out', default=None)
    ap.add_argument('--seeds', type=int, default=8)
    ap.add_argument('--ms', default='0.25,0.3,0.35,0.4')
    ap.add_argument('--ss', default='0.05,0.1,0.15,0.2,0.25,0.3,0.35,0.4,0.45')
    ap.add_argument('--ts', default='5,20')
    ap.add_argument('--minpool', type=int, default=2)
    return ap.parse_args()


def main():
    args = parse()
    B = args.B
    ms = [float(x) for x in args.ms.split(',')]
    ss = [float(x) for x in args.ss.split(',')]
    ts = [float(x) for x in args.ts.split(',')]
    WK = ['plain', 'smooth']
    t0 = time.time()
    tick = lambda msg: print('[%6.1fs] %s' % (time.time() - t0, msg), flush=True)

    ID = Ideals(2 * B)
    rows = enumerate_rows(B, ID)
    R, J = rows['R'], rows['J']
    tick('B=%d  rows R=%d (R/B=%.4f, log_B R=%.4f)  max #prime factors J=%d' % (B, R, R / B, math.log(R) / math.log(B), J))

    # ---------------- sources: plain primary elements up to B^max(m,s); pools for each s
    Lplain = B ** max(max(ms), max(ss))
    PA, PB, PN = primary_elements(Lplain)
    Sp = len(PA)
    pools = {}
    for s in ss:
        P0 = B ** s
        pl = split_prime_sources(ID, P0, 2 * P0)
        if len(pl) >= args.minpool:
            pools[s] = pl
    colmap = {int(k): i for i, k in enumerate(encode(PA, PB))}
    SA = list(PA); SB = list(PB)
    for s, pl in pools.items():
        for P in pl:
            kk = int(encode(P['a'], P['b']))
            if kk not in colmap:
                colmap[kk] = len(SA); SA.append(P['a']); SB.append(P['b'])
    SA = np.array(SA, I64); SB = np.array(SB, I64)
    S = len(SA)
    for s, pl in pools.items():
        for P in pl:
            P['col'] = colmap[int(encode(P['a'], P['b']))]
    tick('sources: %d plain (N<=%.0f), %d total columns; pools: %s' % (Sp, Lplain, S, {s: len(p) for s, p in pools.items()}))

    # ---------------- symbol table for the prime ideals dividing rows
    PID = rows['PID']
    uid = np.unique(PID[PID >= 0])
    LOC = local_index(PID, uid)
    T = symbol_table(ID, uid, SA, SB)
    tick('symbol table %s' % (T.shape,))

    # ---------------- weights
    Wcols = []     # (kind, m)
    for kind in WK:
        for m in ms:
            Wcols.append((kind, m))
    nMW = len(Wcols)
    Wall = np.zeros((Sp, nMW + len(pools) * len(WK)))
    for i, (kind, m) in enumerate(Wcols):
        Wall[:, i] = weight_vector(PN, B ** m, kind)
    ctrl_cols = {}
    for si, s in enumerate(sorted(pools)):
        for ki, kind in enumerate(WK):
            c = nMW + si * len(WK) + ki
            Wall[:, c] = weight_vector(PN, B ** s, kind)       # plain control of length N3 = P0 = B^s
            ctrl_cols[(s, kind)] = c

    # ---------------- pool weight variants
    varnames = ['ones'] + ['rand%d' % i for i in range(args.seeds)] + ['t%g' % t for t in ts] + ['gauss_simple', 'gauss_canon']
    Amats = {}
    for s, pl in pools.items():
        n = len(pl)
        Am = np.zeros((n, len(varnames)), complex)
        lnN = np.log(np.array([P['p'] for P in pl], float))
        gs = np.zeros(n, complex); gc = np.zeros(n, complex)
        for i, P in enumerate(pl):
            gs[i], gc[i] = gauss_sums(P)
        for vi, v in enumerate(varnames):
            if v == 'ones': Am[:, vi] = 1
            elif v.startswith('rand'):
                rng = np.random.default_rng([int(v[4:]), B, int(round(s * 1000))])
                Am[:, vi] = np.exp(2j * np.pi * rng.random(n))
            elif v.startswith('t'):
                Am[:, vi] = np.exp(-1j * float(v[1:]) * lnN)
            elif v == 'gauss_simple': Am[:, vi] = np.conj(gs)
            elif v == 'gauss_canon': Am[:, vi] = np.conj(gc)
        Amats[s] = Am
        for P, g1, g2 in zip(pl, gs, gc):
            assert abs(abs(g1) - 1) < 1e-8 and abs(abs(g2) - 1) < 1e-8
    nv = len(varnames)

    # ---------------- F accumulation (streaming over rows)
    sl = sorted(pools)
    F = np.zeros((nMW, len(sl), nv)); F2 = np.zeros_like(F)
    Fc = np.zeros((nMW, len(sl))); Fc2 = np.zeros_like(Fc)
    F0 = np.zeros(nMW); F02 = np.zeros(nMW)
    Mmom = np.zeros(nMW)     # sum |X|^2
    chunk = max(200, min(R, 2_500_000 // S))
    for r0 in range(0, R, chunk):
        r1 = min(R, r0 + chunk); n = r1 - r0
        chi = chi_chunk(LOC, T, r0, r1)
        Xall = chi[:, :Sp] @ Wall
        X2 = np.abs(Xall[:, :nMW]) ** 2
        X4 = X2 ** 2; X8 = X4 ** 2
        F0 += X4.sum(0); F02 += X8.sum(0); Mmom += X2.sum(0)
        Y2 = np.abs(Xall[:, nMW:]) ** 2
        for si, s in enumerate(sl):
            cols = [P['col'] for P in pools[s]]
            Q = chi[:, cols] @ Amats[s]
            q2 = np.abs(Q) ** 2; q4 = q2 ** 2
            F[:, si, :] += X4.T @ q2
            F2[:, si, :] += X8.T @ q4
            for ki, kind in enumerate(WK):
                mi = [i for i, (kk, m) in enumerate(Wcols) if kk == kind]
                y2 = Y2[:, ctrl_cols[(s, kind)] - nMW]
                Fc[mi, si] += X4[:, mi].T @ y2
                Fc2[mi, si] += X8[:, mi].T @ (y2 ** 2)
    tick('F accumulated')

    # ---------------- D (diagonal) side
    pmax = int(max(Lplain, 2 * max([B ** s for s in sl]) + 1))
    res = dict(B=B, R=R, J=J, logB_R=math.log(R) / math.log(B), Sp=Sp, S=S, varnames=varnames, ms=ms, ss=sl, WK=WK,
               pools={str(s): len(pools[s]) for s in sl}, entries=[], seeds=args.seeds, ts=ts, time_rows=time.time() - t0)
    for i, (kind, m) in enumerate(Wcols):
        w = Wall[:, i]
        ka, kb, d = self_convolution(PA, PB, w)
        rho_k = rho_elements(ID, ka, kb, pmax)
        D0 = R * float(np.sum(d ** 2)); D0cop = R * float(np.sum(rho_k * d ** 2))
        base = dict(kind=kind, m=m, nX=int((w > 0).sum()), nk=len(ka), D0=D0, D0cop=D0cop, F0=F0[i], SE0=math.sqrt(max(0, F02[i] - F0[i] ** 2 / R)),
                    X2mean=Mmom[i] / R, sumd=float(d.sum()))
        res['entries'].append(dict(base, s=None))
        for si, s in enumerate(sl):
            pl = pools[s]
            TA = np.array([P['a'] for P in pl], I64); TB = np.array([P['b'] for P in pl], I64)
            Am, ca, cb = conv_matrix(ka, kb, d, TA, TB)
            rho = rho_elements(ID, ca, cb, pmax)
            C = Am.T @ Amats[s]                       # (ncols, nv)
            C2 = np.abs(C) ** 2
            D = R * C2.sum(0); Dcop = R * (rho[:, None] * C2).sum(0)
            SE = np.sqrt(np.maximum(0, F2[i, si] - F[i, si] ** 2 / R))
            # control: plain third factor
            w3 = Wall[:, ctrl_cols[(s, kind)]]
            n3 = np.nonzero(w3 > 0)[0]
            Ac, cac, cbc = conv_matrix(ka, kb, d, PA[n3], PB[n3])
            rhoc = rho_elements(ID, cac, cbc, pmax)
            cc = Ac.T @ w3[n3]
            Dc = R * float(np.sum(cc ** 2)); Dcc = R * float(np.sum(rhoc * cc ** 2))
            SEc = math.sqrt(max(0, Fc2[i, si] - Fc[i, si] ** 2 / R))
            res['entries'].append(dict(kind=kind, m=m, s=s, npool=len(pl), ncols=int(Am.shape[1]), T=2 * m + s,
                                       F=F[i, si].tolist(), D=D.tolist(), Dcop=Dcop.tolist(), SE=SE.tolist(),
                                       Fc=float(Fc[i, si]), Dc=Dc, Dccop=Dcc, SEc=SEc, nctrl=int(len(n3)), ncolsc=int(Ac.shape[1]),
                                       D0=D0, D0cop=D0cop, F0=float(F0[i])))
    tick('D computed; total %.1fs' % (time.time() - t0))
    res['time'] = time.time() - t0
    out = args.out or os.path.join(os.path.dirname(os.path.abspath(__file__)), 'results', 'grid_%d.json' % B)
    os.makedirs(os.path.dirname(out), exist_ok=True)
    with open(out, 'w') as f:
        json.dump(res, f)
    tick('wrote %s' % out)


if __name__ == '__main__':
    main()
