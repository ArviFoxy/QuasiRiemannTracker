"""Large sieve off the spike span, in the convention of the Lean statement (lean/arvi_kwall/SexticSpikeFree.lean).

The Lean form is the row Gram's quadratic form b* E E^H b = |E^H b|^2.  Poisson writes the off-diagonal row Gram
through f_h f_h^H with f_h(z) = G(z) conj chi_z(h), so in this convention the theta spikes are G conj(chi(m) chi(u)).
Most earlier scripts measure |E^T c|^2 instead; there the spikes are the conjugates conj G chi(m) chi(u).
Projecting those out of E E^H (theta_span, theta_locate, theta_topspan) removes the other conjugation.

Twists m = 1 and the sources with N(m) <= M, times the six units u; radial profiles (N z / B)^{-j/2}, j < J.  The
script prints
  * r_H(b) = |E^H b|^2 / (S |b|^2) for b = G conj chi(u) prof and for its conjugate, against random phases;
  * the top eigenvalues of P E E^H P / S, P = projection off the span, for the theta span in each conjugation, the
    block span (chi(m) chi(u) prof_j in both conjugations), all of them, and a random subspace of the same dimension
    as "all";
  * the Marchenko-Pastur edge (1 + sqrt(R/S))^2.

usage: python3 -I theta_offspan.py B L [M,M,...] [J]
"""
import os, sys, math
sys.dont_write_bytecode = True
import numpy as np
from scipy.sparse.linalg import svds, LinearOperator

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import theta_core as tc      # noqa: E402

B = int(sys.argv[1]); L = int(sys.argv[2])
Ms = [int(t) for t in sys.argv[3].split(',')] if len(sys.argv) > 3 else [30, 100]
J = int(sys.argv[4]) if len(sys.argv) > 4 else 2
F = tc.build(B, L)
E, R, S, rows, SN, Grow, unit_tw = F.E, F.R, F.S, F.rows, F.SN, F.Grow, F.unit_tw
rng = np.random.default_rng(23)
Nz = rows['N'].astype(float)
profs = [(Nz / B) ** (-j / 2) for j in range(J)]
mp = (1 + math.sqrt(R / S)) ** 2


def rH(b):
    v = E.conj().T @ b
    return float(np.vdot(v, v).real / (S * np.vdot(b, b).real))


prof = profs[min(1, J - 1)]
rb = [rH(np.exp(2j * np.pi * rng.random(R)) * prof) for _ in range(12)]
print('r_H, random phases: %.3f +- %.3f' % (np.mean(rb), np.std(rb)))
print('r_H, G conj chi(u) prof (Lean convention):  %s' % np.round([rH(Grow * np.conj(unit_tw[:, k]) * prof) for k in range(6)], 3))
print('r_H, conj G chi(u) prof (other conjugation): %s' % np.round([rH(np.conj(Grow) * unit_tw[:, k] * prof) for k in range(6)], 3),
      flush=True)


def top_off(Q, k=4):
    if Q is None:
        s = svds(E, k=k, random_state=0, return_singular_vectors=False)
    else:
        op = LinearOperator((R, S), dtype=complex,
                            matvec=lambda v: (lambda w: w - Q @ (Q.conj().T @ w))(E @ v),
                            rmatvec=lambda u: E.conj().T @ (u - Q @ (Q.conj().T @ u)))
        s = svds(op, k=k, random_state=0, return_singular_vectors=False)
    return np.sort(s)[::-1] ** 2 / S


def orth(vecs):
    Q, Rr = np.linalg.qr(np.array(vecs).T)
    keep = np.abs(np.diag(Rr)) > 1e-8 * np.abs(np.diag(Rr)).max()
    return Q[:, keep]


print('full: %s   MP edge %.3f' % (np.round(top_off(None), 3), mp), flush=True)
order = np.argsort(SN)
for M in Ms:
    idx = order[SN[order] <= M]
    tw = np.concatenate([np.ones((R, 1), complex), E[:, idx]], axis=1)        # m = 1 and the sources with N(m) <= M
    base = (tw[:, :, None] * unit_tw[:, None, :]).reshape(R, -1)            # chi(m) chi(u)
    th_ok, th_ot, bl = [], [], []
    for p in profs:
        for c in base.T:
            th_ok.append(Grow * np.conj(c) * p)
            th_ot.append(np.conj(Grow) * c * p)
            bl.append(c * p)
            bl.append(np.conj(c) * p)
    Qok, Qot, Qbl = orth(th_ok), orth(th_ot), orth(bl)
    Qall = orth(th_ok + th_ot + bl)
    d = Qall.shape[1]
    Qr = np.linalg.qr(rng.standard_normal((R, d)) + 1j * rng.standard_normal((R, d)))[0]
    print('N(m) <= %d (%d twists, J = %d):' % (M, tw.shape[1], J))
    print('  theta, Lean conjugation  (dim %4d): %s' % (Qok.shape[1], np.round(top_off(Qok), 3)), flush=True)
    print('  theta, other conjugation (dim %4d): %s' % (Qot.shape[1], np.round(top_off(Qot), 3)), flush=True)
    print('  block, both conjugations (dim %4d): %s' % (Qbl.shape[1], np.round(top_off(Qbl), 3)), flush=True)
    print('  all                      (dim %4d): %s' % (d, np.round(top_off(Qall), 3)), flush=True)
    print('  random subspace          (dim %4d): %s' % (d, np.round(top_off(Qr), 3)), flush=True)
