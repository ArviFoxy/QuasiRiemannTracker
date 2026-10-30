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


# ---------------------------------------------------------------- do the top singular vectors live in the twisted-theta span?
from scipy.sparse.linalg import svds  # noqa: E402
Uv, sv, Vh = svds(E, k=6)
o = np.argsort(-sv); Uv, sv, Vh = Uv[:, o], sv[o], Vh[o]
mp = (math.sqrt(R) + math.sqrt(S)) ** 2 / S
print('top singular^2/S: %s  MP edge %.3f' % (np.round(sv ** 2 / S, 3), mp))
PIDs = rows['PID']
w = (rows['N'] / B) ** -0.5
elems = []
for a in range(-9, 10):
    for b in range(-9, 10):
        n = a * a - a * b + b * b
        if 1 <= n <= 100 and a % 3 == 2 and b % 3 == 0:
            elems.append(((a, b), n))
elems.sort(key=lambda t: t[1])
vecs_theta, vecs_block = [], []
for m, n in elems:
    vals = np.array([np.prod([sym(generator(int(i))['prime'], m) or 0 for i in PIDs[z] if i >= 0]) for z in range(R)])
    for j in range(6):
        for e in (1, 5):
            vb = vals ** e * unit_tw[:, j]
            if np.abs(vb).sum():
                vecs_theta.append(np.conj(Grow) * vb * w)
                vecs_block.append(vb * w)
def span_overlap(vecs, u):
    Q, _ = np.linalg.qr(np.array(vecs).T)
    return np.linalg.norm(Q.conj().T @ u), Q.shape[1]
for t in range(6):
    u = Uv[:, t]
    ot, dt = span_overlap(vecs_theta, u)
    ob, db = span_overlap(vecs_block, u)
    print('  #%d s^2/S=%.3f: overlap with twisted-theta span (dim %d) %.3f, with block span (dim %d) %.3f, random level %.3f' %
          (t, sv[t] ** 2 / S, dt, ot, db, ob, math.sqrt(dt / R)))
# the energy captured by the twisted-theta span vs a random subspace of the same dimension
Q, _ = np.linalg.qr(np.array(vecs_theta).T)
EQ = E.conj().T @ Q
ev = np.linalg.eigvalsh(EQ.conj().T @ EQ)[::-1] / S
Qr, _ = np.linalg.qr(rng.standard_normal((R, Q.shape[1])) + 1j * rng.standard_normal((R, Q.shape[1])))
EQr = E.conj().T @ Qr
evr = np.linalg.eigvalsh(EQr.conj().T @ EQr)[::-1] / S
print('  compressed spectrum on twisted-theta span: top %s ; on a random span of same dim: top %s' % (np.round(ev[:4], 3), np.round(evr[:4], 3)))
Qb, _ = np.linalg.qr(np.array(vecs_block).T)
EQb = E.conj().T @ Qb
Kb = EQb.conj().T @ EQb / S
evb, Vb = np.linalg.eigh(Kb)
print('  compressed spectrum on block span (chi_z(m) chi_z(u), dim %d): top %s' % (Qb.shape[1], np.round(evb[::-1][:4], 3)))
ub = Qb @ Vb[:, -1]
print('  top block-span vector: overlap with top singular vector %.3f' % abs(np.vdot(ub, Uv[:, 0])))
# what is the top block combination? weights on (m, unit, e)
coef = np.abs(Qb.conj().T @ ub)
labels = []
for m, n in elems:
    vals = None
    for j in range(6):
        for e in (1, 5):
            labels.append((m, n, j, e))
# project ub on each block vector individually
ovs = []
for (m, n, j, e), v in zip(labels, vecs_block):
    ovs.append((abs(np.vdot(v, ub)) / np.linalg.norm(v), m, n, j, e))
ovs.sort(reverse=True)
print('  top block-span vector loads on: ' + ', '.join('m=%s^%d u%d:%.2f' % (m, e, j, o_) for o_, m, n, j, e in ovs[:8]))
# source side: which sources carry the image?
f = E.T @ ub
f = np.abs(f) ** 2; f /= f.sum()
order = np.argsort(-f)[:12]
print('  image on sources: top sources (a,b,N,share): ' + ', '.join('(%d,%d,N=%d,%.3f)' % (SA[i], SB[i], SN[i], f[i]) for i in order))
print('  share of image on sources with N<=100: %.3f (their count share %.3f)' % (f[SN <= 100].sum(), (SN <= 100).mean()))
