#!/usr/bin/env python3
"""
P1 (column branch) through a Gram / frame decomposition along the largest prime factor.

Model over Z[omega] (as in round7/signal-processing): rows k (quadratic symbols, N(k) <= K),
columns n (primary split-squarefree, N/2 < N(n) <= N), c(n) = g~(n) * A(n) with the prime slot
polynomial A(n) = sum_{P ~ Lslot} N(P)^{-1/2} conj((n/P)_3).

Split the columns by the norm of their largest prime factor pi = P^+(n):
  smooth part  : N(pi) <= K   (cofactor m = n/pi has N(m) >= N/(2K))
  hard core    : N(pi) >  K   (cofactor N(m) < N/K)
Inside each part the blocks are B_pi = {n : P^+(n) = pi}.  Twisted multiplicativity gives
  c(pi m) = g~(pi) * e_pi(m),   e_pi(m) = g~(m) conj((m/pi)_3) A(pi m),
so the block phase g~(pi) is a common unimodular factor of the block.  With w_pi = Phi(c|B_pi) and
W = [w_pi] (K' x #blocks):
  CB(part) = ||sum_pi w_pi||^2 <= #blocks * ||W||_op^2           (Cauchy-Schwarz, phase-free)
and ||W||_op is unchanged by any change of the block phases.  So if ||W||_op^2 is at its generic
(Marchenko-Pastur) size, the part's column branch is diagonal for EVERY choice of block phases.

Printed per part:
  diag    = sum_k sum_{n in part} |c(n)|^2 1[(n,k)=1]            (exact diagonal)
  CB/diag = actual column branch (true Gauss sums)
  blk/diag= sum_pi ||w_pi||^2 / diag   (block-diagonal part = what random block phases give)
  op/MP   = ||W||_op^2 / (generic iid prediction (Frob/(K' m)) (sqrt K' + sqrt m)^2)
  adv/diag= max over unimodular block phases found by a phase power iteration (lower bound)
  ub/diag = #blocks * ||W||_op^2 / diag (upper bound for any block phases)
  LS/diag = (K' + N'_part) ||c_part||^2 / diag   (large-sieve allowance)
usage: python3 block_gram.py K N Lslot
"""
import sys, os, math, time
import numpy as np
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', '..', 'round7', 'signal-processing'))
from zw import Arith, col_arrays, quad_row, cubic_exp, GaussTable, cubic_sym_elem

W3 = np.exp(2j * np.pi / 3)


def build(K, N, Ls):
    t0 = time.time()
    ar = Arith(max(N, 2 * Ls, K) + 10)
    rows = ar.elems(1, K)
    cols = ar.elems(N // 2, N)
    marks = ar.elems(Ls, 2 * Ls, primes_only=True)
    pel = {}
    for e in ar.elems(1, N, primes_only=True):
        pel[(e['ps'][0], e['rs'][0])] = e
    keys = sorted({(p, r) for c in cols for p, r in zip(c['ps'], c['rs'])})
    gtab = GaussTable(ar, [pel[k] for k in keys])
    gt = np.array([gtab.gt(c) for c in cols])
    A, B = col_arrays(cols)
    Phi = np.array([quad_row(ar, A, B, k) for k in rows], dtype=float)
    X = np.zeros((len(cols), len(marks)), complex)
    for j, P in enumerate(marks):
        e = cubic_exp(ar, A, B, P)
        X[:, j] = np.where(e < 0, 0, np.conj(W3 ** np.where(e < 0, 0, e)))      # conj((n/P)_3)
    Aslot = (X / np.sqrt(np.array([P['N'] for P in marks]))[None, :]).sum(1)
    big = [max(zip(c['ps'], c['rs'])) for c in cols]                            # largest prime (by norm)
    print(f'built K={K} N={N} Lslot={Ls}: rows {len(rows)}, cols {len(cols)}, marks {len(marks)} '
          f'({time.time()-t0:.1f}s)', flush=True)
    return dict(ar=ar, rows=rows, cols=cols, Phi=Phi, gt=gt, A=Aslot, big=big, pel=pel, gtab=gtab)


def part_stats(Phi, c, mask, big, name, rng):
    idx = np.nonzero(mask)[0]
    Kp = Phi.shape[0]
    if len(idx) == 0:
        print(f'  {name}: empty'); return
    blocks = {}
    for j in idx:
        blocks.setdefault(big[j], []).append(j)
    bl = list(blocks.values())
    m = len(bl)
    Wm = np.zeros((Kp, m), complex)
    for i, js in enumerate(bl):
        Wm[:, i] = Phi[:, js] @ c[js]
    cp = np.zeros_like(c); cp[idx] = c[idx]
    diag = np.sum((Phi ** 2) @ np.abs(cp) ** 2)
    CB = np.sum(np.abs(Phi @ cp) ** 2)
    blk = np.sum(np.abs(Wm) ** 2)
    sv = np.linalg.svd(Wm, compute_uv=False)
    op = sv[0] ** 2
    mp = (blk / (Kp * m)) * (math.sqrt(Kp) + math.sqrt(m)) ** 2
    # adversarial block phases: phase power iteration on W^* W, several starts
    G = Wm.conj().T @ Wm
    best = 0.0
    starts = [np.linalg.svd(Wm, full_matrices=False)[2][0].conj()] + \
             [np.exp(2j * np.pi * rng.random(m)) for _ in range(4)]
    for x in starts:
        x = np.exp(1j * np.angle(x))
        for _ in range(60):
            y = G @ x
            x = np.exp(1j * np.angle(y))
        best = max(best, np.real(np.vdot(x, G @ x)))
    sizes = np.array([len(b) for b in bl])
    ls = (Kp + len(idx)) * np.sum(np.abs(cp) ** 2) / diag
    nrm = np.linalg.norm(Wm, axis=0); nrm[nrm == 0] = 1
    fr = np.linalg.svd(Wm / nrm, compute_uv=False)[0] ** 2      # frame bound of normalized block profiles
    wub = blk * fr / diag                                           # weighted Cauchy-Schwarz bound, any block phases
    print(f'  {name:11s}: cols {len(idx):5d} ({len(idx)/len(c):5.1%})  blocks {m:5d} (mean size {sizes.mean():5.2f}) '
          f'CB/diag={CB/diag:6.3f}  blk/diag={blk/diag:6.3f}  op/MP={op/mp:6.3f}  '
          f'adv/diag={best/diag:7.3f}  wub/diag={wub:7.2f} (frame {fr:6.2f}, (1+sqrt(m/K))^2={(1+math.sqrt(m/Kp))**2:5.2f})  LS/diag={ls:6.1f}', flush=True)
    return dict(CB=CB, diag=diag, blk=blk, op=op, mp=mp, adv=best, m=m, fr=fr, ls=ls)


def main():
    K, N, Ls = map(int, sys.argv[1:4])
    rng = np.random.default_rng(1)
    d = build(K, N, Ls)
    Phi, gt, A, big = d['Phi'], d['gt'], d['A'], d['big']
    bignorm = np.array([b[0] for b in big])
    Kp, Np = Phi.shape
    print(f"K'={Kp} N'={Np}  N'/K'={Np/Kp:.1f}   log N/log K = {math.log(N)/math.log(K):.3f}")
    for label, beta in [('g~ * A (true)', gt * A),
                        ('random phase * A', np.exp(2j * np.pi * rng.random(Np)) * A),
                        ('g~ (no slots)', gt)]:
        print(f' column vector: {label}')
        allmask = np.ones(Np, bool)
        part_stats(Phi, beta, allmask, big, 'all', rng)
        part_stats(Phi, beta, bignorm <= K, big, 'smooth', rng)
        part_stats(Phi, beta, bignorm > K, big, 'hard core', rng)
        # smooth part split further by the size of the block prime
        for lo, hi in [(1, int(K ** 0.5)), (int(K ** 0.5), K)]:
            part_stats(Phi, beta, (bignorm > lo) & (bignorm <= hi), big, f'P+ in({lo},{hi}]', rng)


if __name__ == '__main__':
    main()
