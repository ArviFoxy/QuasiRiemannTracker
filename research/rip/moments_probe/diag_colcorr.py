"""Column-correlation diagnostic for probe B: Gam[n,m] = (1/R) sum_u chi_u(n) conj chi_u(m) for the sources n,m of one window.

usage: python3 -I diag_colcorr.py B m      (e.g. 48000 0.5)
Prints M2 against its diagonal-only value, the rms off-diagonal entry against R^-1/2 and the largest off-diagonal pairs.
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
V = pb.ZETA6[Ech] * (~Zch)           # R x C
Gam = (V.conj().T @ V) / R           # C x C column correlation
S = V.sum(1)
print('R', R, 'C', C, 'N', N)
print('M2 actual', np.mean(np.abs(S)**2)/N, ' diag-only prediction', np.trace(Gam).real/N)
off = Gam - np.diag(np.diag(Gam))
print('sum offdiag / N =', off.sum().real/N, ' (relative to diag %.4f)' % (off.sum().real/np.trace(Gam).real))
print('rms offdiag |Gam| = %.4f ; 1/sqrt(R) = %.4f' % (np.sqrt(np.mean(np.abs(off[~np.eye(C, dtype=bool)])**2)), 1/math.sqrt(R)))
# top pairs
iu = np.triu_indices(C, 1)
vals = Gam[iu]
o = np.argsort(-np.abs(vals))[:15]
def fmt(i): return f'({SA[i]},{SB[i]})N={SN[i]}'
for k in o:
    i, j = iu[0][k], iu[1][k]
    print(fmt(i), fmt(j), 'Gam=%.4f%+.4fj |Gam|*sqrtR=%.2f' % (vals[k].real, vals[k].imag, abs(vals[k])*math.sqrt(R)))
# mean of real part of offdiag
print('mean Re off-diag (upper) = %.5f, sd = %.5f (expected sd %.5f)' % (vals.real.mean(), vals.real.std(), 1/math.sqrt(2*R)))
