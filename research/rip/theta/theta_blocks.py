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
