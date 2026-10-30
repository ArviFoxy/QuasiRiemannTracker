"""Where does the arithmetic excess at the top of the sextic spectrum live?

Removes candidate subspaces and recomputes the top singular values s^2/S of the projected matrix:
  * rows: the block span {chi_z(m) chi_z(u)} of small-modulus row characters (N(m) <= M, six units u), and the
    twisted-theta span {conj G(z) chi_z(m) chi_z(u)} with the same twists;
  * sources: the columns with N(x) <= X (small sources), or with N(x) > X (large sources).
The random models (theta_models.py) sit at s^2/S ~ 3.95 (B = 10^4) and ~ 3.99 (B = 3*10^4).

usage: python3 -I theta_locate.py B L
"""
import os, sys, math
sys.dont_write_bytecode = True
import numpy as np
from scipy.sparse.linalg import svds, LinearOperator

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import theta_core as tc      # noqa: E402

B = int(sys.argv[1]); L = int(sys.argv[2])
F = tc.build(B, L)
E, R, S, rows, SA, SB, SN, Grow, unit_tw = F.E, F.R, F.S, F.rows, F.SA, F.SB, F.SN, F.Grow, F.unit_tw


def top(M, k=4):
    s = svds(M, k=k, random_state=0, return_singular_vectors=False)
    return np.sort(s)[::-1] ** 2 / S


def top_off_rows(Q, k=4):
    op = LinearOperator((R, S), dtype=complex,
                        matvec=lambda v: (E @ v) - Q @ (Q.conj().T @ (E @ v)),
                        rmatvec=lambda u: E.conj().T @ (u - Q @ (Q.conj().T @ u)))
    s = svds(op, k=k, random_state=0, return_singular_vectors=False)
    return np.sort(s)[::-1] ** 2 / S


print('full: %s' % np.round(top(E), 3), flush=True)
order = np.argsort(SN)
for M in (30, 100, 300, 1000):
    idx = order[(SN[order] <= M)]                     # twists m = small sources (chi_z(m) is column m of E)
    blocks = (E[:, idx][:, :, None] * unit_tw[:, None, :]).reshape(R, -1)
    Qb, _ = np.linalg.qr(blocks)
    thetas = np.conj(Grow)[:, None] * blocks
    Qt, _ = np.linalg.qr(thetas)
    Qbt, _ = np.linalg.qr(np.concatenate([blocks, thetas], axis=1))
    print('N(m) <= %4d: block span dim %d -> %s ; theta span -> %s ; both (dim %d) -> %s' %
          (M, Qb.shape[1], np.round(top_off_rows(Qb), 3), np.round(top_off_rows(Qt), 3), Qbt.shape[1],
           np.round(top_off_rows(Qbt), 3)), flush=True)
    del blocks, thetas, Qb, Qt, Qbt
for X in (30, 100, 300, 1000, 3000):
    keep = SN > X
    print('sources N(x) > %4d (%d of %d): %s ;  N(x) <= %4d only: %s' %
          (X, keep.sum(), S, np.round(top(E[:, keep]), 3), X, np.round(top(E[:, ~keep], k=3), 3) if (~keep).sum() > 4 else '-'),
          flush=True)
