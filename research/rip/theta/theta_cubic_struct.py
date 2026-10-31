"""Structure of the top singular vectors of the cubic family E3 = E**2 at B = L.

The cubic symbols of the units, of lambda = omega - 1 and of 2 modulo a row z depend only on the class of z modulo 9
and modulo 2 (supplementary laws and cubic reciprocity at 2).  The twist families of theta_offspan / theta_cubic use
twists coprime to 6 only, so they miss these.  For the top left vectors u_t (t < k) the script prints
  * flatness: the share of |u_t|^2 on the top 10% of rows (0.1 for a flat vector);
  * the mass of u_t in the span of class indicators (z mod 9, z mod 2: 27 classes) times profiles (N z/B)^{-j/2}, j < 2,
    and times {1, G3, conj G3}, against a random span of the same dimension;
  * the largest normalized correlations |<u_t, v>| / |v| over v = chi_z^2(lambda^e 2^f u) * {1, G3, conj G3} * profile.

usage: python3 -I theta_cubic_struct.py B L [k]
"""
import os, sys, math, time
sys.dont_write_bytecode = True
import numpy as np
from scipy.sparse.linalg import svds

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import theta_core as tc      # noqa: E402

B = int(sys.argv[1]); L = int(sys.argv[2])
k = int(sys.argv[3]) if len(sys.argv) > 3 else 4
F = tc.build(B, L)
E, R, S, rows, ID, pc, zo, sym, unit_tw, t0 = F.E, F.R, F.S, F.rows, F.ID, F.pc, F.zo, F.sym, F.unit_tw, F.t0
E3 = E ** 2
del E
ZETA6 = np.exp(2j * np.pi * np.arange(6) / 6)
cache = {}


def gen3(i):
    if i in cache:
        return cache[i]
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
                kk = pr.sym((aa, bb))
                if kk is not None:
                    tot += ZETA6[(2 * kk) % 6] * np.exp(2j * np.pi * bb / q)
        val = dict(a=q, b=0, G=tot / q, prime=pr)
    cache[i] = val
    return val


def sym3(prime, x):
    v = sym(prime, x)
    return None if v is None else v ** 2


G3 = np.zeros(R, complex)
lam3 = np.zeros(R, complex); two3 = np.zeros(R, complex)
for zi in range(R):
    gens = [gen3(int(i)) for i in rows['PID'][zi] if i >= 0]
    g = 1 + 0j; vl = 1 + 0j; v2 = 1 + 0j
    for gi in gens:
        g *= gi['G']
        vl *= sym3(gi['prime'], (-1, 1))         # lambda = omega - 1
        v2 *= sym3(gi['prime'], (2, 0))
    for a_ in range(len(gens)):
        for b_ in range(a_ + 1, len(gens)):
            g *= sym3(gens[b_]['prime'], (gens[a_]['a'], gens[a_]['b'])) * sym3(gens[a_]['prime'], (gens[b_]['a'], gens[b_]['b']))
    G3[zi] = g; lam3[zi] = vl; two3[zi] = v2
u3 = unit_tw ** 2
print('  built cubic Gauss sums and supplementary symbols (%.0fs)' % (time.time() - t0), flush=True)

U, s, Vh = svds(E3, k=k, random_state=0)
o = np.argsort(-s); U, s = U[:, o], s[o]
print('top s^2/S: %s   MP edge %.3f' % (np.round(s ** 2 / S, 3), (1 + math.sqrt(R / S)) ** 2), flush=True)
rng = np.random.default_rng(41)
Nz = rows['N'].astype(float)
profs = [np.ones(R), (Nz / B) ** -0.5]

for t in range(k):
    w = np.abs(U[:, t]) ** 2
    top10 = np.sort(w)[::-1][: R // 10].sum() / w.sum()
    print('  u_%d: share of |u|^2 on the top 10%% of rows %.3f (flat 0.100)' % (t, top10))

A = np.asarray(rows['A'], np.int64); Bc = np.asarray(rows['Bc'], np.int64)
cls = ((A % 9) * 9 + (Bc % 9)) * 4 + ((A % 2) * 2 + (Bc % 2))
uc, inv = np.unique(cls, return_inverse=True)
print('  %d row classes (z mod 9, z mod 2)' % len(uc))
ind = np.zeros((R, len(uc)))
ind[np.arange(R), inv] = 1.0


def orth(V):
    Q, Rr = np.linalg.qr(V)
    keep = np.abs(np.diag(Rr)) > 1e-8 * np.abs(np.diag(Rr)).max()
    return Q[:, keep]


for name, fac in (('classes x 1', np.ones(R)), ('classes x G3', G3), ('classes x conj G3', np.conj(G3))):
    V = np.concatenate([ind * (fac * p)[:, None] for p in profs], axis=1).astype(complex)
    Q = orth(V)
    d = Q.shape[1]
    Qr = orth(rng.standard_normal((R, d)) + 1j * rng.standard_normal((R, d)))
    print('  %-18s dim %3d: mass of u_0..u_%d %s ; random span %s' %
          (name, d, k - 1, np.round(np.linalg.norm(Q.conj().T @ U, axis=0), 3),
           np.round(np.linalg.norm(Qr.conj().T @ U, axis=0), 3)), flush=True)

best = []
for e in range(3):
    for f_ in range(3):
        for kk in range(6):
            base = lam3 ** e * two3 ** f_ * u3[:, kk]
            for fname, fac in (('1', np.ones(R)), ('G3', G3), ('conj G3', np.conj(G3))):
                for jj, p in enumerate(profs):
                    v = base * fac * p
                    v = v / np.linalg.norm(v)
                    c = np.abs(v.conj() @ U)
                    best.append((c[0], c, 'lam^%d 2^%d u%d %s prof%d' % (e, f_, kk, fname, jj)))
best.sort(key=lambda t: -t[0])
print('  strongest single correlations with u_0 (random level %.3f):' % (1 / math.sqrt(R)))
for c0, c, nm in best[:8]:
    print('    %-28s |<u_t, v>| = %s' % (nm, np.round(c, 3)))
print('done in %.0fs' % (time.time() - t0))
