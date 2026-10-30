"""Theta span V of the sextic large sieve: where does the excess live, and what is left off it?

Matrix E[z, x] = chi_z(x) = prod_{pi | z} (x/pi)_6: rows z = squarefree ideals with N(z) in [B, 2B] coprime to 6 (the
moduli), columns x = primary elements with squarefree norm <= L (the sources).  Xu-Sang (arXiv 2610.17675) attain the
de Faveri excess with Gauss-sum vectors on the moduli side, c_z = conj G(z,1) * profile(N z / B): their Gram main term
is a rank-one form in the profile, proportional to I(U) = int U(t) t^{-5/6} dt.  This script measures, at the sizes we
can reach:
  * the dual energy ratio r(c) = ||E^T c||^2 / (S ||c||^2) of theta row vectors (random c gives 1; the Marchenko-
    Pastur edge is (sqrt R + sqrt S)^2 / S), with Gauss-sum conjugation/unit-twist variants;
  * the Gram of theta vectors across radial profiles (rank-one test against I(U));
  * the overlap of the theta direction with the top singular vectors of E;
  * the projections of detectors (plain sum, prime pool, random) onto the source-side theta direction E^T c / |.|;
  * the top singular value of E with the theta direction removed ("large sieve off V").
G(z,1) uses the Kubota character e(Tr(x/(sqrt(-3) z))) (ppcore 'canon'), extended to composite z by
G(c1 c2) = (c1/c2)_6 (c2/c1)_6 G(c1) G(c2).

usage: python3 -I theta_span.py B L
"""
import os, sys, math, time
sys.dont_write_bytecode = True
import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import theta_core as tc      # noqa: E402

B = int(sys.argv[1]); L = int(sys.argv[2])
rng = np.random.default_rng(5)
F = tc.build(B, L)
E, R, S, rows, SA, SB, SN, spf, ID = F.E, F.R, F.S, F.rows, F.SA, F.SB, F.SN, F.spf, F.ID
Grow, unit_tw, generator, sym, sqfree_int, pc, t0 = F.Grow, F.unit_tw, F.generator, F.sym, F.sqfree_int, F.pc, F.t0

# ---------------------------------------------------------------- spectra
from scipy.sparse.linalg import svds, LinearOperator  # noqa: E402
Uv, sv, Vh = svds(E, k=6)
o = np.argsort(-sv); Uv, sv, Vh = Uv[:, o], sv[o], Vh[o]
mp = (math.sqrt(R) + math.sqrt(S)) ** 2 / S
print('  top singular^2/S: %s   MP edge %.3f' % (np.round(sv[:5] ** 2 / S, 3), mp))


def ratio(c):
    v = E.T @ c
    return float(np.vdot(v, v).real / (S * np.vdot(c, c).real))


tN = rows['N'] / B
w_flat = tN ** -0.5
print('\n== dual energy ratio r(c) = |E^T c|^2/(S|c|^2) on the moduli side (random c -> 1) ==')
rr = [ratio(np.exp(2j * np.pi * rng.random(R)) * w_flat) for _ in range(20)]
rnd = float(np.mean(rr))
print('  random-phase rows, same profile: mean %.3f  sd %.3f  max %.3f' % (rnd, np.std(rr), np.max(rr)))
variants = {}
for name, base in (('conj G', np.conj(Grow)), ('G', Grow)):
    for k in range(6):
        c = base * unit_tw[:, k] * w_flat
        variants['%s * chi(u%d)' % (name, k)] = c
best = None
for name, c in variants.items():
    r_ = ratio(c)
    ov = abs(np.vdot(Uv[:, 0], c)) / np.linalg.norm(c)
    ov5 = np.linalg.norm(Uv[:, :5].conj().T @ c) / np.linalg.norm(c)
    print('  %-16s r = %.3f   overlap with top singular vector %.3f, with top-5 span %.3f' % (name, r_, ov, ov5))
    if best is None or r_ > best[1]:
        best = (name, r_, c)
print('  strongest theta variant: %s (r = %.3f)' % (best[0], best[1]))
c_theta = best[2] / np.linalg.norm(best[2])

# ---------------------------------------------------------------- rank-one test across radial profiles
print('\n== Gram of theta vectors across radial profiles (bumps on [1,2]) ==')
centers = np.linspace(1.1, 1.9, 9)
cols = []
Ivals = []
for c0 in centers:
    U = np.exp(-((tN - c0) / 0.09) ** 2)
    cols.append(best[2] / w_flat * U * tN ** -0.5)
    tt = np.linspace(1, 2, 2001)
    Ivals.append(np.trapezoid(np.exp(-((tt - c0) / 0.09) ** 2) * tt ** (-5 / 6), tt))
C = np.array(cols).T                          # R x 9
Fv = E.T @ C                                  # S x 9
K = Fv.conj().T @ Fv / S
D = np.real(np.diag(C.conj().T @ C))          # diagonal (random) expectation
Kn = K / np.sqrt(np.outer(D, D))
ev = np.linalg.eigvalsh(Kn)[::-1]
print('  normalized Gram eigenvalues: %s' % np.round(ev[:5], 3))
phase = np.exp(2j * np.pi * rng.random(R))
Cr = np.array([phase / w_flat * np.exp(-((tN - c0) / 0.09) ** 2) * tN ** -0.5 for c0 in centers]).T
Fr = E.T @ Cr
Kr = Fr.conj().T @ Fr / S
Dr = np.real(np.diag(Cr.conj().T @ Cr))
evr = np.linalg.eigvalsh(Kr / np.sqrt(np.outer(Dr, Dr)))[::-1]
print('  baseline (random phases, same bumps): %s' % np.round(evr[:5], 3))
Iv = np.array(Ivals)
evec = np.linalg.eigh(Kn)[1][:, -1]
cosI = abs(np.dot(evec.conj(), Iv / np.sqrt(D))) / (np.linalg.norm(Iv / np.sqrt(D)))
print('  top eigenvector vs I(U)-weights: |cos| = %.3f' % cosI)

# ---------------------------------------------------------------- detectors on the source side
print('\n== detectors: projection onto the source-side theta direction f = E^T c / |E^T c| ==')
f = E.T @ c_theta
f = f / np.linalg.norm(f)
is_prime = np.array([sqfree_int(int(n)) and int(spf[int(n)]) == int(n) for n in SN])
dets = {
    'plain sum (all ones)': np.ones(S),
    'plain, smooth weight': np.exp(-((SN / L - 0.6) / 0.25) ** 2),
    'prime pool': is_prime.astype(float),
    'random +-1': rng.choice([-1.0, 1.0], S),
}
for name, a in dets.items():
    pr_ = abs(np.vdot(f, a)) / np.linalg.norm(a)
    ea = float(np.linalg.norm(E @ a) ** 2 / (R * np.linalg.norm(a) ** 2))
    print('  %-22s |<a,f>|/|a| = %.4f   (random level 1/sqrt S = %.4f)   energy |Ea|^2/(R|a|^2) = %.3f' %
          (name, pr_, 1 / math.sqrt(S), ea))

# ---------------------------------------------------------------- large sieve off V
print('\n== large sieve off V: top singular^2/S of E with the theta row direction removed ==')
def top_off(Q):
    op = LinearOperator((R, S), dtype=complex,
                        matvec=lambda v: (E @ v) - Q @ (Q.conj().T @ (E @ v)),
                        rmatvec=lambda u: E.conj().T @ (u - Q @ (Q.conj().T @ u)))
    return svds(op, k=1, return_singular_vectors=False)[0]
s1 = top_off(c_theta[:, None])
print('  full: %.3f   off V (rank 1): %.3f   MP edge %.3f' % (sv[0] ** 2 / S, s1 ** 2 / S, mp))
Vmat = np.array([v / np.linalg.norm(v) for v in variants.values()]).T
Q, _ = np.linalg.qr(Vmat)
s2 = top_off(Q)
print('  off V (12 twist variants): %.3f' % (s2 ** 2 / S))
print('done in %.1fs' % (time.time() - t0))
