#!/usr/bin/env python3
"""Scan N at fixed K: does the block-phase adversary stay bounded on the K-smooth part while it
tracks the large-sieve allowance on the hard core (columns with a prime factor of norm > K)?
usage: python3 block_scan.py K Lslot N1 N2 ..."""
import sys, numpy as np
from block_gram import build, part_stats
K, Ls = int(sys.argv[1]), int(sys.argv[2])
rng = np.random.default_rng(3)
print(f'K={K} Lslot={Ls}')
for N in map(int, sys.argv[3:]):
    d = build(K, N, Ls)
    Phi, gt, A, big = d['Phi'], d['gt'], d['A'], d['big']
    bn = np.array([b[0] for b in big])
    c = gt * A
    print(f" N={N}: N'/K'={Phi.shape[1]/Phi.shape[0]:.1f}")
    s = part_stats(Phi, c, bn <= K, big, 'smooth', rng)
    h = part_stats(Phi, c, bn > K, big, 'hard core', rng)
