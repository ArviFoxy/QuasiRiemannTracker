"""The cubic family with both thetas removed (the two-sided statement of lean/arvi_kwall/SourceSpike.lean).

E3 = E**2 is the cubic symbol on the sextic rows and sources at B = L.  The script removes, on the row side, the span
V(M) of the row thetas G3(z) conj chi3_z(t m) (N z/B)^{-j/2} (t over the 27 supplementary characters, m over 1 and the
sources with N(m) <= M, j < J; as theta_cubic_vm.py), and on the source side the span P of the source thetas
  conj g3(x) N(x)^{-beta}  and  g3(x) N(x)^{-beta}  on each cell (x_* mod 4, x_* mod 9, parity of omega(x)),
with g3(x) the source's cubic Gauss sum (twisted multiplicativity over its prime factors) and beta in the list given.
Poisson in the rows predicts multiplicity (N(x)N(x')/B)^{1/3}, i.e. the profile N(x)^{-1/6}.  It prints the top s^2/S
of E3, of E3 off V(M) (one-sided), of E3 with both spans removed (two-sided), and of the same with random spans of the
same dimensions, the energies of the full top pairs in V(M) and P (for n = 3 Patterson's theorem suggests one
spike seen from both sides), and the energy of the one-sided residual's top right vector in P.

usage: python3 -I theta_cubic_twosided.py B L [M] [J] [beta,beta,...]
"""
import os, sys, math, time
sys.dont_write_bytecode = True
import numpy as np
from scipy.sparse.linalg import svds, LinearOperator

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import theta_core as tc      # noqa: E402
import theta_util as tu      # noqa: E402

B = int(sys.argv[1]); L = int(sys.argv[2])
M = int(sys.argv[3]) if len(sys.argv) > 3 else 60
J = int(sys.argv[4]) if len(sys.argv) > 4 else 2
betas = [float(t) for t in sys.argv[5].split(',')] if len(sys.argv) > 5 else [1.0 / 6]
F = tc.build(B, L)
R, S, rows, ID, pc, zo, sym, SN, t0 = F.R, F.S, F.rows, F.ID, F.pc, F.zo, F.sym, F.SN, F.t0
E3 = F.E ** 2
F.E = None
ZETA6 = np.exp(2j * np.pi * np.arange(6) / 6)
cache = {}


def gen3(i):
    """primary generator, cubic Gauss sum (unimodular) and prime object of the prime ideal with id i."""
    if i in cache:
        return cache[i]
    if i < ID.ns:
        p, r = ID.split_pr(np.array([i]))
        p = int(p[0]); r = int(r[0])
        a, b = pc.primary_generator(p, r)
        x = np.arange(1, p, dtype=np.int64)
        code = pc.sym_codes(np.array([p]), np.array([r]), x, np.zeros_like(x))[0]
        ch = ZETA6[(2 * code.astype(np.int64)) % 6]
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
                    tot += ZETA6[(2 * c) % 6] * np.exp(2j * np.pi * bb / q)
        val = dict(a=q, b=0, G=tot / q, prime=pr)
    cache[i] = val
    return val


def sym3(prime, x):
    v = sym(prime, x)
    return None if v is None else v ** 2


def gauss3(gens):
    g = 1 + 0j
    for gi in gens:
        g *= gi['G']
    for a_ in range(len(gens)):
        for b_ in range(a_ + 1, len(gens)):
            g *= sym3(gens[b_]['prime'], (gens[a_]['a'], gens[a_]['b'])) * \
                sym3(gens[a_]['prime'], (gens[b_]['a'], gens[b_]['b']))
    return g


# ---- row side: G3, the 27 supplementary characters, V(M)
G3 = np.zeros(R, complex); lam = np.zeros(R, complex); two = np.zeros(R, complex); om = np.zeros(R, complex)
for zi in range(R):
    gens = [gen3(int(i)) for i in rows['PID'][zi] if i >= 0]
    vl = 1 + 0j; v2 = 1 + 0j; vo = 1 + 0j
    for gi in gens:
        vl *= sym3(gi['prime'], (-1, 1)); v2 *= sym3(gi['prime'], (2, 0)); vo *= sym3(gi['prime'], (0, 1))
    G3[zi] = gauss3(gens); lam[zi] = vl; two[zi] = v2; om[zi] = vo
sup = [lam ** e * two ** f * om ** g for e in range(3) for f in range(3) for g in range(3)]
Nz = rows['N'].astype(float)
profs = [(Nz / B) ** (-j / 2) for j in range(J)]
order = np.argsort(SN)
idx = order[SN[order] <= M]
tw = [np.ones(R, complex)] + [E3[:, j] for j in idx]
cols = [G3 * np.conj(t * m) * p for t in sup for m in tw for p in profs]


def orth(V):
    Q, Rr = np.linalg.qr(V)
    d = np.abs(np.diag(Rr))
    return Q[:, d > 1e-8 * d.max()]


QV = orth(np.array(cols).T)
dV = QV.shape[1]
print('  row side: G3 and 27 supplementary characters; V(%d): %d twists, dim %d   (%.0fs)'
      % (M, len(tw), dV, time.time() - t0), flush=True)

# ---- source side: cubic Gauss sums of the sources, cells (class mod 4, class mod 9, parity of omega)
g3s = np.zeros(S, complex); npr = np.zeros(S, int)
for j, (a, b, n) in enumerate(zip(F.SA, F.SB, SN)):
    ids = tu.source_prime_ids(F, a, b, n)
    g3s[j] = gauss3([gen3(i) for i in ids]); npr[j] = len(ids)
cell = (((F.SA % 4) * 4 + F.SB % 4) * 81 + (F.SA % 9) * 9 + F.SB % 9) * 2 + npr % 2
ncell = len(set(cell.tolist()))
pcols = []
for be in betas:
    prof = SN.astype(float) ** (-be)
    pcols.append(tu.class_span(cell, np.conj(g3s) * prof))
    pcols.append(tu.class_span(cell, g3s * prof))
QP = orth(np.concatenate(pcols, axis=1))
dP = QP.shape[1]
print('  source side: |g3| %.3f..%.3f, %d cells, betas %s: dim %d   (%.0fs)'
      % (np.abs(g3s).min(), np.abs(g3s).max(), ncell, betas, dP, time.time() - t0), flush=True)
rng = np.random.default_rng(73)
QVr = orth(rng.standard_normal((R, dV)) + 1j * rng.standard_normal((R, dV)))
QPr = orth(rng.standard_normal((S, dP)) + 1j * rng.standard_normal((S, dP)))


def top(Qrow=None, Qsrc=None, k=4, vecs=False):
    def rp(u):
        return u if Qrow is None else u - Qrow @ (Qrow.conj().T @ u)

    def sp(v):
        return v if Qsrc is None else v - Qsrc @ (Qsrc.conj().T @ v)
    op = LinearOperator((R, S), dtype=complex, matvec=lambda v: rp(E3 @ sp(v)),
                        rmatvec=lambda u: sp(E3.conj().T @ rp(u)))
    U, s, Vh = svds(op, k=k, random_state=0)
    o = np.argsort(-s)
    if vecs:
        return s[o] ** 2 / S, U[:, o], Vh[o]
    return s[o] ** 2 / S


def edge(dr, ds):
    return (math.sqrt((R - dr) / S) + math.sqrt((S - ds) / S)) ** 2


t0_, U0, V0 = top(vecs=True)
print('full top                     %s   MP edge %.3f' % (np.round(t0_, 3), edge(0, 0)), flush=True)
for t in range(2):
    cP = QP.conj().T @ V0[t].conj()
    cV = QV.conj().T @ U0[:, t]
    print('  top pair %d: left vector in V(%d) %.3f (random %.3f); right vector in P %.3f (random %.3f)'
          % (t, M, float(np.vdot(cV, cV).real), dV / R, float(np.vdot(cP, cP).real), dP / S), flush=True)
t1, U1, V1 = top(QV, None, vecs=True)
print('one-sided, off V(%d)         %s   MP edge %.3f' % (M, np.round(t1, 3), edge(dV, 0)), flush=True)
c = QP.conj().T @ V1[0].conj()
print('  energy of its top right vector in the source-theta span P: %.3f (random %.3f)'
      % (float(np.vdot(c, c).real), dP / S), flush=True)
print('two-sided, off V(%d) and P   %s   MP edge %.3f' % (M, np.round(top(QV, QP), 3), edge(dV, dP)), flush=True)
print('random spans, same dims      %s' % np.round(top(QVr, QPr), 3), flush=True)
print('V(%d) with a random source span %s' % (M, np.round(top(QV, QPr), 3)), flush=True)
print('done in %.0fs' % (time.time() - t0))
