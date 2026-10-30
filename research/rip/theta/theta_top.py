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

usage: python3 -I theta_top.py B L
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


# ---------------------------------------------------------------- what are the top singular vectors?
from scipy.sparse.linalg import svds  # noqa: E402
k = 6
Uv, sv, Vh = svds(E, k=k)
o = np.argsort(-sv); Uv, sv, Vh = Uv[:, o], sv[o], Vh[o]
mp = (math.sqrt(R) + math.sqrt(S)) ** 2 / S
print('top singular^2/S: %s  MP edge %.3f' % (np.round(sv ** 2 / S, 3), mp))
NR = rows['N'].astype(float); PIDs = rows['PID']
def small_prime_flags(p):
    """rows / sources divisible by a prime ideal of norm p (split: either conjugate; inert: norm p^2)."""
    if p % 3 == 1:
        k_ = int(ID.pidx[p]); ids = {2 * k_, 2 * k_ + 1}
    else:
        ids = {ID.ns + ID.qidx[p]}
    rowf = np.array([any(int(i) in ids for i in PIDs[z] if i >= 0) for z in range(R)])
    q = p if p % 3 == 1 else p * p
    srcf = (SN % q == 0)
    return rowf, srcf
for t in range(4):
    u = Uv[:, t]; v = Vh[t].conj()
    wu = np.abs(u) ** 2 * R; wv = np.abs(v) ** 2 * S
    line = ['#%d s^2/S=%.3f' % (t, sv[t] ** 2 / S)]
    # radial structure
    line.append('corr(|u|^2, N z)=%+.2f corr(|v|^2, N x)=%+.2f' % (np.corrcoef(wu, NR)[0, 1], np.corrcoef(wv, SN)[0, 1]))
    # localisation
    line.append('IPR rows %.1f sources %.1f' % ((wu ** 2).mean(), (wv ** 2).mean()))
    print('  ' + '   '.join(line))
    # small primes: mass on rows/sources divisible by p, relative to their share
    out = []
    for p in (5, 7, 11, 13, 19, 31, 37, 43):
        rf, sf = small_prime_flags(p)
        if rf.sum() and sf.sum():
            out.append('p=%d rows %.2f src %.2f' % (p, wu[rf].mean(), wv[sf].mean()))
    print('     mass ratio on multiples (1 = neutral): ' + '; '.join(out))
    # row-side characters at small elements m: chi_z(m) = prod (m/pi)_6
    best = []
    for m in [(2, 0), (-1, 0), (2, 3), (-1, 3), (5, 0), (2, -3), (-4, -3), (-1, -3)]:
        if m == (-1, 0):
            vals = unit_tw[:, 3]
        else:
            vals = np.array([np.prod([sym(generator(int(i))['prime'], m) or 0 for i in PIDs[z] if i >= 0]) for z in range(R)])
        ov = abs(np.vdot(vals, u)) / (np.linalg.norm(vals) + 1e-12)
        best.append((ov, m))
    best.sort(reverse=True)
    print('     row overlap with chi_z(m) for small m (random ~ %.3f): %s' % (1 / math.sqrt(R), ', '.join('%s:%.3f' % (m, o_) for o_, m in best[:4])))
    # unit twists
    ovu = [abs(np.vdot(unit_tw[:, j], u)) / np.linalg.norm(unit_tw[:, j]) for j in range(6)]
    print('     row overlap with unit twists chi_z(u): %s' % np.round(ovu, 3))
    # source side: small-modulus sextic characters (m0/x)_6 for small primes m0
    outs = []
    for p in (7, 13, 19, 31, 37):
        k_ = int(ID.pidx[p])
        for w in (0, 1):
            pp, rr = ID.split_pr(np.array([2 * k_ + w]))
            codes = pc.sym_codes(pp, rr, SA, SB)[0]
            vals = np.where(codes >= pc.ZCODE, 0, pc.ZETA6[np.minimum(codes, 5)])
            for e in (1, 2, 3):
                vv = vals ** e
                outs.append((abs(np.vdot(vv, v)) / (np.linalg.norm(vv) + 1e-12), '(x/pi_%d)^%d' % (p, e)))
    outs.sort(reverse=True)
    print('     source overlap with (x/pi)^e for small pi (random ~ %.3f): %s' % (1 / math.sqrt(S), ', '.join('%s:%.3f' % (n_, o_) for o_, n_ in outs[:4])))
