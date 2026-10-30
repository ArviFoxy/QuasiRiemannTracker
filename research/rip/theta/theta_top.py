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

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', 'prime_pool'))
sys.path.insert(0, os.path.join(HERE, '..'))
import ppcore as pc          # noqa: E402
import zomega as zo          # noqa: E402

B = int(sys.argv[1]); L = int(sys.argv[2])
rng = np.random.default_rng(5)
t0 = time.time()
ID = pc.Ideals(max(2 * B, L) + 16)
rows = pc.enumerate_rows(B, ID)
R = rows['R']
# sources: primary elements with squarefree odd norm, coprime to 3, 1 < N <= L
SA, SB, SN = pc.primary_elements(L)
spf = ID.spf


def sqfree_int(n):
    while n > 1:
        p = int(spf[n]); n //= p
        if n % p == 0:
            return False
    return True


keep = np.array([(1 < n) and (n % 2 == 1) and (n % 3 != 0) and sqfree_int(int(n)) for n in SN])
SA, SB, SN = SA[keep], SB[keep], SN[keep]
S = len(SA)
uid = np.unique(rows['PID'][rows['PID'] >= 0])
T = pc.symbol_table(ID, uid, SA, SB)
LOC = pc.local_index(rows['PID'], uid)
E = pc.chi_chunk(LOC, T, 0, R).astype(np.complex128)
print('B=%d L=%d  R=%d rows  S=%d sources   built in %.1fs' % (B, L, R, S, time.time() - t0), flush=True)

# ---------------------------------------------------------------- Gauss sums of the moduli (rows)
gen_cache = {}


def generator(i):
    """primary generator (a, b) and a symbol function for prime ideal id i."""
    if i in gen_cache:
        return gen_cache[i]
    if i < ID.ns:
        p, r = ID.split_pr(np.array([i]))
        p = int(p[0]); r = int(r[0])
        a, b = pc.primary_generator(p, r)
        gs, gc = pc.gauss_sums(dict(p=p, r=r, a=a, b=b))
        val = dict(a=a, b=b, G=gc, prime=zo.Prime(p, (a, b)))
    else:
        q = int(ID.inert_q[i - ID.ns])
        pr = zo.Prime(q)
        # inert Gauss sum over F_{q^2} with the Kubota character: Tr(x/(sqrt(-3) q)) = b_x / q
        tot = 0j
        for aa in range(q):
            for bb in range(q):
                k = pr.sym((aa, bb))
                if k is None:
                    continue
                tot += np.exp(2j * np.pi * k / 6) * np.exp(2j * np.pi * bb / q)
        val = dict(a=q, b=0, G=tot / q, prime=pr)
    gen_cache[i] = val
    return val


def sym(prime, x):
    k = prime.sym((int(x[0]), int(x[1])))
    return None if k is None else np.exp(2j * np.pi * k / 6)


Grow = np.zeros(R, complex)
unit_tw = np.zeros((R, 6), complex)          # chi_z(u) for the six units u (twist variants)
for zi in range(R):
    ids = [int(i) for i in rows['PID'][zi] if i >= 0]
    gens = [generator(i) for i in ids]
    g = 1 + 0j
    for gi in gens:
        g *= gi['G']
    for a_ in range(len(gens)):
        for b_ in range(a_ + 1, len(gens)):
            s1 = sym(gens[b_]['prime'], (gens[a_]['a'], gens[a_]['b']))
            s2 = sym(gens[a_]['prime'], (gens[b_]['a'], gens[b_]['b']))
            g *= s1 * s2
    Grow[zi] = g
    for k, u in enumerate(pc.UNITS):
        v = 1 + 0j
        for gi in gens:
            v *= sym(gi['prime'], u)
        unit_tw[zi, k] = v
print('  |G(z,1)|: min %.3f max %.3f   (built %.1fs)' % (np.abs(Grow).min(), np.abs(Grow).max(), time.time() - t0), flush=True)


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
