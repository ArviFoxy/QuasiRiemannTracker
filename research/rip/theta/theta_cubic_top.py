"""What are the top outliers of the cubic family E3 = E**2?

For the top left (row) and right (source) singular vectors of E3 at B = L, the script prints
  * the mass of each top left vector in the row spike span V(M) of the Lean statement (twisted thetas
    G3 conj chi^2(m) chi^2(u) and plain characters chi^2(m) chi^2(u) in both conjugations, profiles (N z/B)^{-j/2},
    j < 2), for growing twist cutoffs M, against random spans of the same dimension;
  * the mass of each top right vector in the source-side theta span: G3(x) chi_x^2(h) chi_x^2(u) N(x)^{-1/2}
    (normalized cubic Gauss sums of the sources, both conjugations), N(h) <= M;
  * the dual energy r_src(f) = |E3 f|^2/(R |f|^2) of the untwisted source thetas.
At the balanced point the nonzero spectra of E3 E3^H and E3^H E3 agree, so a source-side spike shows up on the rows as
E3 f, which need not lie in the row spike span.

usage: python3 -I theta_cubic_top.py B L [M,M,...]
"""
import os, sys, math, time
sys.dont_write_bytecode = True
import numpy as np
from scipy.sparse.linalg import svds

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import theta_core as tc      # noqa: E402

B = int(sys.argv[1]); L = int(sys.argv[2])
Ms = [int(t) for t in sys.argv[3].split(',')] if len(sys.argv) > 3 else [30, 100, 300]
F = tc.build(B, L)
E, R, S, rows, SA, SB, SN, spf, ID, pc, zo, sym, unit_tw, t0 = (F.E, F.R, F.S, F.rows, F.SA, F.SB, F.SN, F.spf, F.ID,
                                                               F.pc, F.zo, F.sym, F.unit_tw, F.t0)
E3 = E ** 2
del E
ZETA6 = np.exp(2j * np.pi * np.arange(6) / 6)
cache = {}


def gen3(i):
    """primary generator, cubic Gauss sum (Kubota character, as theta_core) and prime object of prime ideal id i."""
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
                k = pr.sym((aa, bb))
                if k is not None:
                    tot += ZETA6[(2 * k) % 6] * np.exp(2j * np.pi * bb / q)
        val = dict(a=q, b=0, G=tot / q, prime=pr)
    cache[i] = val
    return val


def sym3(prime, x):
    v = sym(prime, x)
    return None if v is None else v ** 2


def gauss_of(ids):
    gens = [gen3(i) for i in ids]
    g = 1 + 0j
    for gi in gens:
        g *= gi['G']
    for a_ in range(len(gens)):
        for b_ in range(a_ + 1, len(gens)):
            g *= sym3(gens[b_]['prime'], (gens[a_]['a'], gens[a_]['b'])) * sym3(gens[a_]['prime'], (gens[b_]['a'], gens[b_]['b']))
    return g, gens


G3 = np.array([gauss_of([int(i) for i in rows['PID'][zi] if i >= 0])[0] for zi in range(R)])
u3 = unit_tw ** 2
# sources: prime ideal factorization (squarefree norm: split primes only), cubic Gauss sums and unit twists
src_ids = []
for a, b, n in zip(SA, SB, SN):
    n = int(n); ids = []
    while n > 1:
        p = int(spf[n]); n //= p
        k = int(ID.pidx[p]); r0 = int(ID.split_r[k])
        r = r0 if (int(a) + int(b) * r0) % p == 0 else p - 1 - r0
        ids.append(ID.ideal_id(p, r))
    src_ids.append(ids)
Gs = np.zeros(S, complex); su3 = np.zeros((S, 6), complex); src_gens = []
for j, ids in enumerate(src_ids):
    g, gens = gauss_of(ids)
    Gs[j] = g
    src_gens.append(gens)
    for kk, u in enumerate(pc.UNITS):
        v = 1 + 0j
        for gi in gens:
            v *= sym3(gi['prime'], u)
        su3[j, kk] = v
print('  |G3| rows %.3f..%.3f, sources %.3f..%.3f   (%.0fs)' % (np.abs(G3).min(), np.abs(G3).max(), np.abs(Gs).min(),
                                                             np.abs(Gs).max(), time.time() - t0), flush=True)

k = 6
U, s, Vh = svds(E3, k=k, random_state=0)
o = np.argsort(-s); U, s, Vh = U[:, o], s[o], Vh[o]
print('top s^2/S: %s   MP edge %.3f' % (np.round(s ** 2 / S, 3), (1 + math.sqrt(R / S)) ** 2), flush=True)
rng = np.random.default_rng(37)


def orth(vecs):
    Q, Rr = np.linalg.qr(np.array(vecs).T)
    keep = np.abs(np.diag(Rr)) > 1e-8 * np.abs(np.diag(Rr)).max()
    return Q[:, keep]


def mass(Q, X):
    return np.linalg.norm(Q.conj().T @ X, axis=0)


Nz = rows['N'].astype(float)
profs = [np.ones(R), (Nz / B) ** -0.5]
order = np.argsort(SN)
for M in Ms:
    idx = order[SN[order] <= M]
    tw = np.concatenate([np.ones((R, 1), complex), E3[:, idx]], axis=1)
    base = (tw[:, :, None] * u3[:, None, :]).reshape(R, -1)
    vecs = []
    for p in profs:
        for c in base.T:
            vecs += [G3 * np.conj(c) * p, c * p, np.conj(c) * p]
    Q = orth(vecs)
    d = Q.shape[1]
    if d >= R // 2:
        print('row span V(%d): dim %d >= R/2, skipped' % (M, d)); break
    Qr = np.linalg.qr(rng.standard_normal((R, d)) + 1j * rng.standard_normal((R, d)))[0]
    print('row span V(%4d) dim %4d: top left vectors mass %s ; random span %s' %
          (M, d, np.round(mass(Q, U), 3), np.round(mass(Qr, U), 3)), flush=True)

# ---- source side
NS = SN.astype(float)
sprof = NS ** -0.5


def rsrc(f):
    v = E3 @ f
    return float(np.vdot(v, v).real / (R * np.vdot(f, f).real))


rb = [rsrc(np.exp(2j * np.pi * rng.random(S)) * sprof) for _ in range(8)]
print('source side: random phases r_src %.3f +- %.3f' % (np.mean(rb), np.std(rb)))
print('  G3(x) chi_x^2(u) N^{-1/2}:      r_src %s' % np.round([rsrc(Gs * su3[:, kk] * sprof) for kk in range(6)], 3))
print('  conj G3(x) chi_x^2(u) N^{-1/2}: r_src %s' % np.round([rsrc(np.conj(Gs) * su3[:, kk] * sprof) for kk in range(6)], 3),
      flush=True)
hs = [((a, b), a * a - a * b + b * b) for a in range(-15, 16) for b in range(-15, 16)
      if a % 3 == 2 and b % 3 == 0 and 1 <= a * a - a * b + b * b <= max(Ms)]
hs.sort(key=lambda t: t[1])


def chi3_src(h):
    out = np.zeros(S, complex)
    for j, gens in enumerate(src_gens):
        v = 1 + 0j
        for gi in gens:
            t = sym3(gi['prime'], h)
            if t is None:
                v = 0; break
            v *= t
        out[j] = v
    return out


Vs = Vh.conj().T                                  # right singular vectors as columns
for M in Ms:
    vecs = []
    for h, nh in hs:
        if nh > M:
            continue
        ch = chi3_src(h)
        for kk in range(6):
            for base in (Gs, np.conj(Gs)):
                vecs.append(base * ch * su3[:, kk] * sprof)
    if not vecs:
        continue
    Q = orth(vecs)
    d = Q.shape[1]
    if d >= S // 2:
        print('source span (N(h) <= %d): dim %d >= S/2, skipped' % (M, d)); break
    Qr = np.linalg.qr(rng.standard_normal((S, d)) + 1j * rng.standard_normal((S, d)))[0]
    print('source theta span N(h) <= %4d dim %4d: top right vectors mass %s ; random span %s' %
          (M, d, np.round(mass(Q, Vs), 3), np.round(mass(Qr, Vs), 3)), flush=True)
print('done in %.0fs' % (time.time() - t0))
