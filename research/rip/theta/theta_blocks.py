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

usage: python3 -I theta_blocks.py B L
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


# ---------------------------------------------------------------- block vectors: chi_z(m) for small m, and units
def ratio(c):
    v = E.T @ c
    return float(np.vdot(v, v).real / (S * np.vdot(c, c).real))
PIDs = rows['PID']
w = (rows['N'] / B) ** -0.5
rr = [ratio(np.exp(2j * np.pi * rng.random(R)) * w) for _ in range(20)]
print('random-phase baseline r = %.3f +- %.3f' % (np.mean(rr), np.std(rr)))
elems = []
for a in range(-7, 8):
    for b in range(-7, 8):
        n = a * a - a * b + b * b
        if 1 < n <= 60 and a % 3 == 2 and b % 3 == 0:
            elems.append(((a, b), n))
elems.sort(key=lambda t: t[1])
res = []
for m, n in elems[:16]:
    vals = np.array([np.prod([sym(generator(int(i))['prime'], m) or 0 for i in PIDs[z] if i >= 0]) for z in range(R)])
    if np.abs(vals).sum() == 0:
        continue
    r_ = ratio(vals * w)
    res.append((r_, m, n))
for j in range(6):
    res.append((ratio(unit_tw[:, j] * w), pc.UNITS[j], 1))
res.sort(reverse=True)
for r_, m, n in res[:6]:
    print('  chi_z(%s) [N=%d]: r = %.3f  (excess %+.0f%%)' % (m, n, r_, 100 * (r_ / np.mean(rr) - 1)))
print('  theta (conj G chi(u0)): r = %.3f' % ratio(np.conj(Grow) * unit_tw[:, 0] * w))
print('twisted theta conj G(z) chi_z(m) chi_z(u):')
tw = []
for m, n in elems[:16]:
    vals = np.array([np.prod([sym(generator(int(i))['prime'], m) or 0 for i in PIDs[z] if i >= 0]) for z in range(R)])
    for j in range(6):
        for e in (1, 5):
            c = np.conj(Grow) * vals ** e * unit_tw[:, j] * w
            if np.abs(c).sum():
                tw.append((ratio(c), m, n, j, e))
tw.sort(reverse=True)
for r_, m, n, j, e in tw[:10]:
    print('  m=%s [N=%d]^%d, unit %d: r = %.3f (excess %+.0f%%)' % (m, n, e, j, r_, 100 * (r_ / np.mean(rr) - 1)))
print('  ... median over all twisted: %.3f' % np.median([t[0] for t in tw]))
