"""Is the block outlier inside the spike family of the Lean conjecture?  (row side)

The top left singular vectors u0..u3 of E carry the block outlier, whose source side is the class-signed conjugate
source theta (theta_mech_*.py).  SexticSpikeFree.lean removes the row spans of its spike shapes (Lean convention:
kind 0 = g~(z) conj chi_z(m), kind 1 = chi_z(m), kind 2 = conj chi_z(m), times the profiles (B/N z)^{j/2}) for twists m
of norm <= C B^{1-6 eps}, every associate included.  Here every shape is multiplied by the class functions of the row
generator (z_* mod 4, z_* mod 9), which contain every supplementary twist (lambda/z), (2/z), (omega/z), (-1/z) and the
unit twists.  For each span the script prints the energy of u0..u3 and of the row image E f of the fitted source theta f
in it, the energy of a random vector (dim / R), and the top eigenvalue s^2/S of the row Gram compressed to the span
against the top singular value.

usage: python3 -I theta_blockcover.py B L [M] [J]      (twists m: the sources with N(m) <= M; profiles j < J)
"""
import os, sys, time
sys.dont_write_bytecode = True
import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import theta_util as tu      # noqa: E402

B = int(sys.argv[1]); L = int(sys.argv[2])
M = int(sys.argv[3]) if len(sys.argv) > 3 else 30
J = int(sys.argv[4]) if len(sys.argv) > 4 else 2
A = tu.load_all(B, L, 8)
F, R, S, rd, U, s = A.F, A.R, A.S, A.rd, A.U, A.s
E, t0 = F.E, F.t0
gen = rd['gen']
c36 = ((gen[:, 0] % 4) * 4 + gen[:, 1] % 4) * 81 + (gen[:, 0] % 9) * 9 + gen[:, 1] % 9
ncls = len(set(c36.tolist()))
prof = [(F.rows['N'].astype(float) / B) ** (-j / 2) for j in range(J)]
print('B=%d L=%d  R=%d S=%d  top s^2/S %s   %d row classes mod 36   (%.0fs)'
      % (B, L, R, S, np.round(s[:4] ** 2 / S, 3), ncls, time.time() - t0), flush=True)

# the fitted source theta (12 class phases, alpha = 1/3) and its row image
base, Xn = tu.class_signed_fit(A)
w, V = tu.top_eig(tu.compressed(F, Xn, 'src'), 1)
f = Xn @ V[:, 0]
Ef = E @ f
print('  source theta: compressed top %.3f (s^2/R); |<f, v0>| %.3f' % (w[0], abs(np.vdot(f / np.linalg.norm(f), A.Vh[0].conj()))),
      flush=True)
tests = [('u0', U[:, 0]), ('u1', U[:, 1]), ('u2', U[:, 2]), ('u3', U[:, 3]), ('E f', Ef)]


def basis(cols):
    X = np.concatenate(cols, axis=1)
    Q, Rr = np.linalg.qr(X)
    d = np.abs(np.diag(Rr))
    return Q[:, d > 1e-8 * d.max()]


def report(name, Q):
    d = Q.shape[1]
    en = [tu.energy_in_span(Q, v) for _, v in tests]
    lam = tu.top_eig(tu.compressed(F, Q, 'row'), 1)[0][0]
    print('  %-44s dim %5d  random %.3f | %s | span top %.3f' % (name, d, d / R, ' '.join('%s %.3f' % (n, e) for (n, _), e
                                                                                     in zip(tests, en)), lam), flush=True)


G = F.Grow
twist_idx = tu.block_columns(F, M)
print('  twists m: %d sources with N(m) <= %d' % (len(twist_idx), M), flush=True)
k0 = [tu.class_span(c36, G * p) for p in prof]                 # kind 0, m = 1, all supplementary twists
k1 = [tu.class_span(c36, p.astype(complex)) for p in prof]     # kinds 1/2, m = 1 (class functions are conj-closed)
report('kind 0 (theta), m = 1, classes mod 36', basis(k0))
report('kinds 1/2 (plain), m = 1, classes mod 36', basis(k1))
report('kinds 0-2, m = 1, classes mod 36', basis(k0 + k1))
# twisted shapes with the 6 unit classes only (the dimension of the full class span times the twists exceeds R)
unit = (rd['chim1'] > 0) * 3 + rd['chiw']
tw0 = [tu.class_span(unit, G * np.conj(E[:, j]) * p) for j in twist_idx for p in prof]
tw1 = [tu.class_span(unit, E[:, j] * p) for j in twist_idx for p in prof]
tw2 = [tu.class_span(unit, np.conj(E[:, j]) * p) for j in twist_idx for p in prof]
report('kind 0, N(m) <= M, unit classes', basis(tw0))
report('kinds 1/2, N(m) <= M, unit classes', basis(tw1 + tw2))
report('all kinds: classes mod 36 (m = 1) + twists', basis(k0 + k1 + tw0 + tw1 + tw2))
# ---- the source theta restricted to large sources: does its row image keep its strength off the low-twist family?
Q_all = basis(k0 + k1 + tw0 + tw1 + tw2)
SN = F.SN.astype(float)
for cut in (M, 10 * M, 100 * M):
    fl = f * (SN > cut)
    if np.linalg.norm(fl) == 0:
        continue
    b = E @ fl
    b = b - Q_all @ (Q_all.conj().T @ b)
    rq = float(np.linalg.norm(E.conj().T @ b) ** 2 / (S * np.linalg.norm(b) ** 2))
    print('  source theta on N(x) > %6d (|f|^2 share %.3f): row image off the family, Rayleigh s^2/S %.3f'
          % (cut, np.linalg.norm(fl) ** 2 / np.linalg.norm(f) ** 2, rq), flush=True)
rnd = E @ (np.exp(2j * np.pi * np.random.default_rng(71).random(S)) * (SN > M))
rnd = rnd - Q_all @ (Q_all.conj().T @ rnd)
print('  control: random phases on N(x) > %d, same projection: Rayleigh s^2/S %.3f'
      % (M, np.linalg.norm(E.conj().T @ rnd) ** 2 / (S * np.linalg.norm(rnd) ** 2)), flush=True)
# ---- flatness of the row image and its mass on slot-selected rows
g = np.abs(Ef) ** 2 / np.mean(np.abs(Ef) ** 2)
print('  row image |Ef|^2 / mean: quantiles 10/50/90/99%% %s, max %.2f (exponential law: 0.11/0.69/2.30/4.61)'
      % (np.round(np.quantile(g, [0.1, 0.5, 0.9, 0.99]), 2), g.max()), flush=True)
spf = F.spf
for P0 in (40, 100):
    sl = np.nonzero((SN >= P0) & (SN <= 2 * P0) & np.array([int(spf[int(n)]) == int(n) for n in F.SN]))[0]
    T = E[:, sl].sum(1)
    for rho in (0.1, 0.01):
        W = np.argsort(-np.abs(T))[:max(2, int(rho * R))]
        print('  slot P0=%d (%d primes), W = top %.0f%% by |T|: share of |Ef|^2 on W %.4f; of |u0|^2 %.4f'
              % (P0, len(sl), 100 * rho, g[W].sum() / g.sum(), float(np.sum(np.abs(U[W, 0]) ** 2))), flush=True)
print('done in %.0fs' % (time.time() - t0))
