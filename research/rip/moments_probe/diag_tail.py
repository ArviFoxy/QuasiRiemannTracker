"""Tail diagnostic for probe B: distribution of |S_u|^2/N for the actual family vs one multiplicative-surrogate draw,
share of sum |S|^6 per bin, split by number of prime factors and by the smallest prime of u.

usage: python3 -I diag_tail.py B m      (e.g. 192000 0.5)
"""
import sys, math, time
sys.dont_write_bytecode = True
import os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import numpy as np
import scipy.sparse as sps
import probeB as pb
B = int(sys.argv[1]); m = float(sys.argv[2])
from zw import Arith
rng = np.random.default_rng(7)
ar = Arith(2*B+10)
PI = pb.prime_ideals(ar, 2*B)
rows = pb.build_rows(PI['norm'], B, 2*B)
R = len(rows)
N = B**m
SA, SB, SN = pb.primary_window(N, 2*N)
C = len(SA)
E, Z = pb.sextic_table(PI, SA, SB)
indptr = np.zeros(R+1, dtype=np.int64); indptr[1:] = np.cumsum([len(r) for r in rows])
indices = np.fromiter((j for r in rows for j in r), dtype=np.int64, count=int(indptr[-1]))
Inc = sps.csr_matrix((np.ones(len(indices), dtype=np.float32), indices, indptr), shape=(R, len(PI['norm'])))
Ech = np.rint(Inc @ E.astype(np.float32)).astype(np.int32) % 6
Zch = (Inc @ Z.astype(np.float32)) > 0.5
V = pb.ZETA6[Ech] * (~Zch)
S = V.sum(1)
Ex, _ = pb.small_prime_ideal_factors(SA, SB, SN, 2*N + 5)
J = rng.integers(0, 6, size=(R, Ex.shape[1])).astype(np.float32)
Er = np.rint(J @ Ex.T).astype(np.int64) % 6
Sm = (pb.ZETA6[Er] * (~Zch)).sum(1)
print('R', R, 'C', C, 'N', round(N,1))
a2 = np.abs(S)**2/N; m2 = np.abs(Sm)**2/N
print('mean |S|^2/N: actual %.4f mult %.4f' % (a2.mean(), m2.mean()))
print('M4: actual %.4f mult %.4f ; M6: actual %.4f mult %.4f' % ((a2**2).mean(), (m2**2).mean(), (a2**3).mean(), (m2**3).mean()))
edges = [0, 0.25, 0.5, 1, 1.5, 2, 3, 4, 6, 8, 12, 20, 1e9]
print('bin of |S|^2/N        frac actual  frac mult  | share of sum|S|^6: actual  mult')
t_a = (a2**3).sum(); t_m = (m2**3).sum()
for lo, hi in zip(edges[:-1], edges[1:]):
    ma = (a2 >= lo) & (a2 < hi); mm = (m2 >= lo) & (m2 < hi)
    print('[%5.2f,%5.2f)      %.4f      %.4f     |  %.4f   %.4f' % (lo, hi, ma.mean(), mm.mean(), (a2[ma]**3).sum()/t_a, (m2[mm]**3).sum()/t_m))
print('max |S|^2/N: actual %.2f  mult %.2f' % (a2.max(), m2.max()))
# split rows by number of prime ideal factors and by the smallest prime
nf = np.array([len(r) for r in rows]); small = np.array([PI['norm'][r[0]] for r in rows])
print('by number of prime factors (M6 actual / mult):')
for k in range(1, 8):
    mk = nf == k
    if mk.sum() > 200:
        print('  k=%d rows %6d  M6 actual %.4f mult %.4f ratio %.3f | M2 actual %.4f mult %.4f' % (k, mk.sum(), (a2[mk]**3).mean(), (m2[mk]**3).mean(), (a2[mk]**3).mean()/(m2[mk]**3).mean(), a2[mk].mean(), m2[mk].mean()))
print('by smallest prime norm:')
for lo, hi in [(1,10),(10,30),(30,100),(100,1000),(1000,1e9)]:
    mk = (small >= lo) & (small < hi)
    if mk.sum() > 200:
        print('  smallest N in [%d,%d) rows %6d  M6 actual %.4f mult %.4f ratio %.3f' % (lo, hi, mk.sum(), (a2[mk]**3).mean(), (m2[mk]**3).mean(), (a2[mk]**3).mean()/(m2[mk]**3).mean()))
# real-valued rows (u = conj u): all prime factors inert -> S real
allinert = np.array([all(PI['kind'][j] == 1 for j in r) for r in rows])
print('rows with only inert primes (S real):', allinert.sum())
