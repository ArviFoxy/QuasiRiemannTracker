"""Q1 (frontier/README.md, queued directions): dual-frame metrics built from products of short pieces.

The dual-frame bound (lean/arvi_kwall/DualFrame.lean): for Q positive definite on the rows,
  sum_{z in W} |(Ea)_z|^2 <= c_W(Q) * lambda_max(E^H Q E) * |a|^2,   c_W(Q) = sup_{v on W, |v|=1} <v, Q^{-1} v>.
Amplification is the diagonal case Q = diag(|T(z)|^2)/A, with T the slot polynomial and A its threshold on W:
Q >= 1 on W (c_W <= 1) and <Ea, Q Ea> = sum_z |T D|^2 / A is the amplified polynomial's energy.  A family of short
pieces at several prime scales gives Q = sum_k w_k diag(|P_k|^2)/A_k: a multiresolution metric.

The script prints c_W(Q) * lambda_max(E^H Q E) / S for slot-selected W (top rho R rows by |T|, T = sum of chi_z(p) over
split primes p with N p in [P0, 2 P0]) and for:
  Q = I (trivial);  single amplifier |T|^2/A;  its square |T|^4/A^2;  families over several slot ranges;  the oracle
  P_W + 0.1 I;  and the truth |E_W|^2/S.

usage: python3 -I theta_ampframe.py B L [rho] [P0,P0,...]
"""
import os, sys, math
sys.dont_write_bytecode = True
import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import theta_core as tc      # noqa: E402

B = int(sys.argv[1]); L = int(sys.argv[2])
rho = float(sys.argv[3]) if len(sys.argv) > 3 else 0.1
P0s = [int(t) for t in sys.argv[4].split(',')] if len(sys.argv) > 4 else [40, 100, 250]
F = tc.build(B, L)
E, R, S, SN, spf = F.E, F.R, F.S, F.SN, F.spf


def slot_sum(P0):
    sl = np.nonzero((SN >= P0) & (SN <= 2 * P0) & np.array([int(spf[int(n)]) == int(n) for n in SN]))[0]
    return E[:, sl].sum(1), len(sl)


T0, n0 = slot_sum(P0s[0])
n = max(2, int(rho * R))
W = np.argsort(-np.abs(T0))[:n]
inW = np.zeros(R, bool); inW[W] = True
print('B=%d: slot P0=%d (%d primes), |W| = %d (rho %.2f)' % (B, P0s[0], n0, n, rho), flush=True)


def lam_max_EQE(qdiag):
    """top eigenvalue of E^H diag(q) E / S by Lanczos (matrix-free)."""
    from scipy.sparse.linalg import eigsh, LinearOperator
    op = LinearOperator((S, S), dtype=complex, matvec=lambda v: E.conj().T @ (qdiag * (E @ v)))
    return float(eigsh(op, k=1, which='LA', return_eigenvectors=False, tol=1e-6)[0]) / S


def bound_diag(qdiag, name):
    cW = 1.0 / qdiag[W].min()                    # diagonal Q: c_W = 1 / min_W Q
    lam = lam_max_EQE(qdiag)
    print('  %-46s c_W %.3f  lambda %.3f  bound %.3f' % (name, cW, lam, cW * lam), flush=True)
    return cW * lam


truth = lam_max_EQE(inW.astype(float))
triv = lam_max_EQE(np.ones(R))
print('  truth |E_W|^2/S %.3f ; trivial (Q = I) %.3f' % (truth, triv))
Pw = inW.astype(float) + 0.1
print('  oracle P_W + 0.1 I (c_W = 1/1.1): bound %.3f' % ((1 / 1.1) * lam_max_EQE(Pw)))
a0 = np.abs(T0) ** 2
A0 = a0[W].min()
bound_diag(a0 / A0, 'single amplifier |T|^2/A (P0=%d)' % P0s[0])
bound_diag((a0 / A0) ** 2, 'squared amplifier |T|^4/A^2')
bound_diag(0.5 * (a0 / A0) + 0.5, 'half amplifier + half identity')
# multiresolution families: the slot sum at other scales, each normalized by its own mean on W
fam = [a0 / A0]
for P0 in P0s[1:]:
    Tk, nk = slot_sum(P0)
    ak = np.abs(Tk) ** 2
    fam.append(ak / max(ak[W].mean(), 1e-12))
    print('  slot P0=%d: %d primes; corr(|T_0|^2, |T_k|^2) on W %.3f' % (P0, nk, np.corrcoef(a0[W], ak[W])[0, 1]),
          flush=True)
Qf = sum(fam) / len(fam)
bound_diag(Qf / Qf[W].min() * 1.0, 'family mean over scales (normalized)')
Qprod = np.prod(fam, axis=0) ** (1.0 / len(fam))
bound_diag(Qprod / Qprod[W].min(), 'family geometric mean (product of pieces)')
print('done')
