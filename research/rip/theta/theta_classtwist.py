"""Thetas on congruence classes: the large sieve off the class-twisted spike span (sextic and cubic families).

The sources are primary (a congruence condition modulo 3) and coprime to 2.  Poisson summation over such a set has
dual frequencies in a coarser lattice, which twists the Gauss sums of the rows by the supplementary symbols
(lambda/z), (omega/z), (2/z); these depend only on the class of the row z modulo 9 and modulo 4.  The twist families of
theta_offspan / theta_cubic use twists coprime to 6 only and miss them; the Lean statement's twist box (all
elements of norm <= M) contains them.

For the family E^k (k = 1 sextic, k = 2 cubic) at B = L the script prints the top s^2/S of E^k and of E^k with the rows
projected off
  * the class span: class indicators (z mod 9, z mod 4) times {G_k, conj G_k, 1} times profiles (N z/B)^{-j/2}, j < 2;
  * the class span plus the twisted spans of theta_offspan (twists coprime to 6, N(m) <= M, six units);
  * a random span of the same dimension,
with the Marchenko-Pastur edge for each dimension, and the mass of the top left vectors in the class span.

usage: python3 -I theta_classtwist.py B L k [M]   (M <= 0: class span only)
"""
import os, sys, math, time
sys.dont_write_bytecode = True
import numpy as np
from scipy.sparse.linalg import svds, LinearOperator

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import theta_core as tc      # noqa: E402

B = int(sys.argv[1]); L = int(sys.argv[2]); kk = int(sys.argv[3])
M = int(sys.argv[4]) if len(sys.argv) > 4 else 30
F = tc.build(B, L)
E, R, S, rows, SN, ID, pc, zo, sym, unit_tw, t0 = (F.E, F.R, F.S, F.rows, F.SN, F.ID, F.pc, F.zo, F.sym, F.unit_tw,
                                                   F.t0)
Ek = E ** kk
del E
ZETA6 = np.exp(2j * np.pi * np.arange(6) / 6)
cache = {}


def genk(i):
    if i in cache:
        return cache[i]
    if i < ID.ns:
        p, r = ID.split_pr(np.array([i]))
        p = int(p[0]); r = int(r[0])
        a, b = pc.primary_generator(p, r)
        x = np.arange(1, p, dtype=np.int64)
        code = pc.sym_codes(np.array([p]), np.array([r]), x, np.zeros_like(x))[0]
        ch = ZETA6[(kk * code.astype(np.int64)) % 6]
        G = np.sum(ch * np.exp(-2j * np.pi * ((b * x) % p) / p)) / math.sqrt(p)
        val = dict(a=a, b=b, G=G, prime=zo.Prime(p, (a, b)))
    else:
        q = int(ID.inert_q[i - ID.ns])
        pr = zo.Prime(q)
        tot = 0j
        for aa in range(q):
            for bb in range(q):
                c = pr.sym((aa, bb))
                if c is not None:
                    tot += ZETA6[(kk * c) % 6] * np.exp(2j * np.pi * bb / q)
        val = dict(a=q, b=0, G=tot / q, prime=pr)
    cache[i] = val
    return val


def symk(prime, x):
    v = sym(prime, x)
    return None if v is None else v ** kk


Gk = np.zeros(R, complex)
for zi in range(R):
    gens = [genk(int(i)) for i in rows['PID'][zi] if i >= 0]
    g = 1 + 0j
    for gi in gens:
        g *= gi['G']
    for a_ in range(len(gens)):
        for b_ in range(a_ + 1, len(gens)):
            g *= symk(gens[b_]['prime'], (gens[a_]['a'], gens[a_]['b'])) * symk(gens[a_]['prime'], (gens[b_]['a'], gens[b_]['b']))
    Gk[zi] = g
uk = unit_tw ** kk
print('  k = %d: |G_k| %.3f..%.3f   (%.0fs)' % (kk, np.abs(Gk).min(), np.abs(Gk).max(), time.time() - t0), flush=True)

A = np.asarray(rows['A'], np.int64); Bc = np.asarray(rows['Bc'], np.int64)
cls = ((A % 9) * 9 + (Bc % 9)) * 16 + ((A % 4) * 4 + (Bc % 4))
uc, inv = np.unique(cls, return_inverse=True)
ind = np.zeros((R, len(uc)))
ind[np.arange(R), inv] = 1.0
Nz = rows['N'].astype(float)
profs = [np.ones(R), (Nz / B) ** -0.5]
rng = np.random.default_rng(53)


def orth(V):
    Q, Rr = np.linalg.qr(V)
    keep = np.abs(np.diag(Rr)) > 1e-8 * np.abs(np.diag(Rr)).max()
    return Q[:, keep]


def top_off(Q, k=4):
    if Q is None:
        s = svds(Ek, k=k, random_state=0, return_singular_vectors=False)
    else:
        op = LinearOperator((R, S), dtype=complex,
                            matvec=lambda v: (lambda w: w - Q @ (Q.conj().T @ w))(Ek @ v),
                            rmatvec=lambda u: Ek.conj().T @ (u - Q @ (Q.conj().T @ u)))
        s = svds(op, k=k, random_state=0, return_singular_vectors=False)
    return np.sort(s)[::-1] ** 2 / S


def mp(d):
    return (1 + math.sqrt((R - d) / S)) ** 2


U, s, _ = svds(Ek, k=4, random_state=0)
o = np.argsort(-s); U, s = U[:, o], s[o]
print('%d row classes (z mod 9, z mod 4); full top %s   MP edge %.3f' % (len(uc), np.round(s ** 2 / S, 3), mp(0)), flush=True)
cols = []
for fac in (Gk, np.conj(Gk), np.ones(R)):
    for p in profs:
        cols.append(ind * (fac * p)[:, None])
Qc = orth(np.concatenate(cols, axis=1).astype(complex))
print('class span dim %d: mass of the top left vectors %s' % (Qc.shape[1], np.round(np.linalg.norm(Qc.conj().T @ U, axis=0), 3)),
      flush=True)
order = np.argsort(SN)
idx = order[SN[order] <= max(M, 0)]
tw = np.concatenate([np.ones((R, 1), complex), Ek[:, idx]], axis=1)
base = (tw[:, :, None] * uk[:, None, :]).reshape(R, -1)
vecs = []
for p in profs:
    for c in base.T:
        vecs += [Gk * np.conj(c) * p, c * p, np.conj(c) * p]
Qall = orth(np.concatenate([np.concatenate(cols, axis=1).astype(complex), np.array(vecs).T], axis=1))
spans = (('class span', Qc), ('class + twists N(m) <= %d' % M, Qall)) if M > 0 else (('class span', Qc),)
for name, Q in spans:
    d = Q.shape[1]
    Qr = orth(rng.standard_normal((R, d)) + 1j * rng.standard_normal((R, d)))
    print('  off %-26s dim %4d: %s   MP edge %.3f' % (name, d, np.round(top_off(Q), 3), mp(d)), flush=True)
    print('  off a random span           dim %4d: %s' % (Qr.shape[1], np.round(top_off(Qr), 3)), flush=True)
print('done in %.0fs' % (time.time() - t0))
