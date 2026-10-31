"""The cubic family: is the theta spike there, and is the large sieve off the spike span at the bulk level?

The cubic symbol is the square of the sextic one, (x/z)_3 = (x/z)_6^2, so the cubic matrix is E3 = E**2 (entrywise)
on the same rows and sources.  Its theta term is (QN)^{2/3} (Heath-Brown), i.e. an excess ~ B^{1/3} at B = L, against
B^{1/6} for the sextic family, so the theta spike should reach the bulk edge at accessible sizes.  This tests the
cubic case of the Lean conjecture (lean/arvi_kwall/SexticSpikeFree.lean, CubicSpikeFree) in its convention
b* E3 E3^H b:
  * r_H(b) = |E3^H b|^2 / (S |b|^2) for the cubic theta b = G3 conj chi^2(u) N^{-1/2} (G3 = normalized cubic Gauss sum
    of the row, Kubota character, twisted multiplicativity), its conjugate, and random phases;
  * the top singular values s^2/S of E3, and of E3 with the rows projected off the theta span (twists m = 1 and the
    sources with N(m) <= M, six units, profiles (N z / B)^{-j/2}, j < J), the block span chi^2(m) chi^2(u) in both
    conjugations, all of them, and a random span of the same dimension; the Marchenko-Pastur edge for each.

usage: python3 -I theta_cubic.py B L [M] [J]
"""
import os, sys, math, time
sys.dont_write_bytecode = True
import numpy as np
from scipy.sparse.linalg import svds, LinearOperator

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import theta_core as tc      # noqa: E402

B = int(sys.argv[1]); L = int(sys.argv[2])
M = int(sys.argv[3]) if len(sys.argv) > 3 else 30
J = int(sys.argv[4]) if len(sys.argv) > 4 else 2
F = tc.build(B, L)
E, R, S, rows, SN, ID, pc, zo, sym, unit_tw, t0 = (F.E, F.R, F.S, F.rows, F.SN, F.ID, F.pc, F.zo, F.sym, F.unit_tw,
                                                   F.t0)
E3 = E ** 2
del E
ZETA6 = np.exp(2j * np.pi * np.arange(6) / 6)

# ---- cubic Gauss sums of the row primes (same additive character as theta_core's G), then of the rows
g3cache = {}


def gen3(i):
    if i in g3cache:
        return g3cache[i]
    if i < ID.ns:
        p, r = ID.split_pr(np.array([i]))
        p = int(p[0]); r = int(r[0])
        a, b = pc.primary_generator(p, r)
        x = np.arange(1, p, dtype=np.int64)
        code = pc.sym_codes(np.array([p]), np.array([r]), x, np.zeros_like(x))[0]
        chi3 = ZETA6[(2 * code.astype(np.int64)) % 6]
        G = np.sum(chi3 * np.exp(-2j * np.pi * ((b * x) % p) / p)) / math.sqrt(p)
        val = dict(a=a, b=b, G=G, prime=zo.Prime(p, (a, b)))
    else:
        q = int(ID.inert_q[i - ID.ns])
        pr = zo.Prime(q)
        tot = 0j
        for aa in range(q):
            for bb in range(q):
                k = pr.sym((aa, bb))
                if k is None:
                    continue
                tot += ZETA6[(2 * k) % 6] * np.exp(2j * np.pi * bb / q)
        val = dict(a=q, b=0, G=tot / q, prime=pr)
    g3cache[i] = val
    return val


def sym3(prime, x):
    v = sym(prime, x)
    return None if v is None else v ** 2


G3 = np.zeros(R, complex)
for zi in range(R):
    ids = [int(i) for i in rows['PID'][zi] if i >= 0]
    gens = [gen3(i) for i in ids]
    g = 1 + 0j
    for gi in gens:
        g *= gi['G']
    for a_ in range(len(gens)):
        for b_ in range(a_ + 1, len(gens)):
            g *= sym3(gens[b_]['prime'], (gens[a_]['a'], gens[a_]['b'])) * sym3(gens[a_]['prime'], (gens[b_]['a'], gens[b_]['b']))
    G3[zi] = g
u3 = unit_tw ** 2
print('  |G3(z)|: min %.3f max %.3f   (%.0fs)' % (np.abs(G3).min(), np.abs(G3).max(), time.time() - t0), flush=True)

rng = np.random.default_rng(29)
Nz = rows['N'].astype(float)
profs = [(Nz / B) ** (-j / 2) for j in range(J)]
prof = profs[min(1, J - 1)]


def rH(b):
    v = E3.conj().T @ b
    return float(np.vdot(v, v).real / (S * np.vdot(b, b).real))


rb = [rH(np.exp(2j * np.pi * rng.random(R)) * prof) for _ in range(12)]
print('r_H random phases: %.3f +- %.3f' % (np.mean(rb), np.std(rb)))
print('r_H cubic theta G3 conj chi^2(u) prof (Lean conj): %s' % np.round([rH(G3 * np.conj(u3[:, k]) * prof) for k in range(6)], 3))
print('r_H conjugate conj G3 chi^2(u) prof:               %s' % np.round([rH(np.conj(G3) * u3[:, k] * prof) for k in range(6)], 3),
      flush=True)


def top_off(Q, k=4):
    if Q is None:
        s = svds(E3, k=k, random_state=0, return_singular_vectors=False)
    else:
        op = LinearOperator((R, S), dtype=complex,
                            matvec=lambda v: (lambda w: w - Q @ (Q.conj().T @ w))(E3 @ v),
                            rmatvec=lambda u: E3.conj().T @ (u - Q @ (Q.conj().T @ u)))
        s = svds(op, k=k, random_state=0, return_singular_vectors=False)
    return np.sort(s)[::-1] ** 2 / S


def orth(vecs):
    Q, Rr = np.linalg.qr(np.array(vecs).T)
    keep = np.abs(np.diag(Rr)) > 1e-8 * np.abs(np.diag(Rr)).max()
    return Q[:, keep]


def mp(d):
    return (1 + math.sqrt((R - d) / S)) ** 2


print('full: %s   MP edge %.3f' % (np.round(top_off(None), 3), mp(0)), flush=True)
order = np.argsort(SN)
idx = order[SN[order] <= M]
tw = np.concatenate([np.ones((R, 1), complex), E3[:, idx]], axis=1)          # chi^2(m), m = 1 and sources N(m) <= M
base = (tw[:, :, None] * u3[:, None, :]).reshape(R, -1)
th, bl = [], []
for p in profs:
    for c in base.T:
        th.append(G3 * np.conj(c) * p)
        bl.append(c * p)
        bl.append(np.conj(c) * p)
Qt, Qb = orth(th), orth(bl)
Qa = orth(th + bl)
d = Qa.shape[1]
Qr = np.linalg.qr(rng.standard_normal((R, d)) + 1j * rng.standard_normal((R, d)))[0]
print('N(m) <= %d (%d twists, J = %d):' % (M, tw.shape[1], J))
for name, Q in (('theta (Lean conj)', Qt), ('block, both conj', Qb), ('all', Qa), ('random', Qr)):
    print('  %-18s dim %4d: %s   MP edge %.3f' % (name, Q.shape[1], np.round(top_off(Q), 3), mp(Q.shape[1])), flush=True)
print('done in %.0fs' % (time.time() - t0))
