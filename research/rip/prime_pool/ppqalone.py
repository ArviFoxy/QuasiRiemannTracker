"""ppqalone.py -- the prime pool ALONE (X = 1): F/(R n) = sum_z |Q(z)|^2 / (R n) as a function of s, for many weight vectors.

    python3 -I ppqalone.py B s1,s2,...     [--out results/qalone_B.json]

This isolates the pool's own behaviour (the case m = 0 of the face).  For |a_P| = 1 and no collisions the diagonal is R n
(Dcop = R * sum_P N(P)/(N(P)+1), reported separately).  Variants:
  ones, rand0..3, t5, t20                  (the task's variants (i)-(iii))
  gsimple, gcanon                          conj of the normalised Gauss sum, additive characters e(x/p), e(-b x/p)   (iv)
  gsimple_c, gcanon_c                      the NON-conjugated sums (orientation test: are we aligned or merely correlated?)
  ang1, ang-1, ang3, ang-3                 angular Hecke characters (P/|P|)^k of the primary generator
  gc_sign                                  gcanon restricted to a single sign class (p = 1 mod 12 only), others weight 0
SE: row-sampling standard error of F/(R n), SE = std(|Q|^2)/(mean * sqrt(R)).
"""
import os, sys, math, json, argparse
import numpy as np
sys.dont_write_bytecode = True
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from ppcore import *


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('B', type=int); ap.add_argument('ss'); ap.add_argument('--out', default=None)
    args = ap.parse_args()
    B = args.B; ss = [float(x) for x in args.ss.split(',')]
    ID = Ideals(2 * B); rows = enumerate_rows(B, ID); R = rows['R']
    PID = rows['PID']; uid = np.unique(PID[PID >= 0]); LOC = local_index(PID, uid)
    print('B=%d R=%d' % (B, R), flush=True)
    out = dict(B=B, R=R, entries=[])
    for s in ss:
        pl = split_prime_sources(ID, B ** s, 2 * B ** s); n = len(pl)
        if n < 2: continue
        TA = np.array([P['a'] for P in pl], I64); TB = np.array([P['b'] for P in pl], I64)
        T = symbol_table(ID, uid, TA, TB)
        CH = max(100, 2_000_000 // n)
        gs = np.zeros(n, complex); gc = np.zeros(n, complex)
        for i, P in enumerate(pl): gs[i], gc[i] = gauss_sums(P)
        pp = np.array([P['p'] for P in pl], float)
        gen = TA + TB * np.exp(2j * np.pi / 3)
        ang = gen / np.abs(gen)
        rng = np.random.default_rng([B, int(1000 * s)])
        V = {'ones': np.ones(n, complex)}
        for i in range(4): V['rand%d' % i] = np.exp(2j * np.pi * rng.random(n))
        V['t5'] = np.exp(-5j * np.log(pp)); V['t20'] = np.exp(-20j * np.log(pp))
        V['gsimple'] = np.conj(gs); V['gcanon'] = np.conj(gc); V['gsimple_c'] = gs; V['gcanon_c'] = gc
        for k in (1, -1, 3, -3): V['ang%d' % k] = ang ** k
        V['gc_sign'] = np.where(pp % 12 == 1, np.conj(gc), 0)
        names = list(V); A = np.stack([V[k] for k in names], axis=1)
        Fs = np.zeros(len(names)); F2 = np.zeros(len(names))
        for r0 in range(0, R, CH):
            E = chi_chunk(LOC, T, r0, min(R, r0 + CH))
            q2 = np.abs(E @ A) ** 2
            Fs += q2.sum(0); F2 += (q2 ** 2).sum(0)
        norm_ = (np.abs(A) ** 2).sum(0) * R
        ratio = Fs / norm_
        se = np.sqrt(np.maximum(0, F2 / R - (Fs / R) ** 2)) / math.sqrt(R) * R / norm_
        print('s=%.2f P0=%8.1f n=%4d P0^2/B=%7.2f | ' % (s, B ** s, n, B ** (2 * s - 1)) + ' '.join('%s %.3f' % (k, r) for k, r in zip(names, ratio)) + ' | SE~%.3f' % np.median(se), flush=True)
        out['entries'].append(dict(s=s, n=n, P2B=B ** (2 * s - 1), names=names, ratio=ratio.tolist(), se=se.tolist()))
    outp = args.out or os.path.join(os.path.dirname(os.path.abspath(__file__)), 'results', 'qalone_%d.json' % B)
    os.makedirs(os.path.dirname(outp), exist_ok=True)
    json.dump(out, open(outp, 'w'))


if __name__ == '__main__':
    main()
