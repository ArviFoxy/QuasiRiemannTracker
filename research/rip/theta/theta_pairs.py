"""Row theta and source theta: one spike (cubic) or two (sextic)?

For E^k at B = L (k = 1: sextic, order q = 6; k = 2: cubic, q = 3) the script measures, for the top singular pairs
(u_t, v_t), the energy of u_t in the row-theta span and of v_t in the source-theta span:
  row thetas     G_k(z) (N z/B)^{-j/2}, j < 2, on each class (z_* mod 4, z_* mod 9)          (Poisson in the sources)
  source thetas  conj g_k(x) N(x)^{-beta} and g_k(x) N(x)^{-beta} on each cell (x_* mod 4, x_* mod 9, parity of
                 omega(x)), beta = 1/2 - 1/q                                                  (Poisson in the rows)
with random baselines dim / R and dim / S.  G_k and g_k are the order-q Gauss sums of rows and sources (twisted
multiplicativity), normalized to modulus 1.  For q = 3 Patterson's theorem (the cubic theta function has Gauss-sum
coefficients) suggests that the source theta's row image is the row theta: one spike, seen from both sides.  For q = 6
the theta coefficients are not Gauss sums, and the numerics of SourceSpike.lean say the two are different.

usage: python3 -I theta_pairs.py B L k [ntop]
"""
import os, sys, math, time
sys.dont_write_bytecode = True
import numpy as np
from scipy.sparse.linalg import svds

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import theta_core as tc      # noqa: E402
import theta_util as tu      # noqa: E402

B = int(sys.argv[1]); L = int(sys.argv[2]); kk = int(sys.argv[3])
ntop = int(sys.argv[4]) if len(sys.argv) > 4 else 4
q = 6 // math.gcd(6, kk)
F = tc.build(B, L)
R, S, rows, ID, pc, zo, sym, SN, t0 = F.R, F.S, F.rows, F.ID, F.pc, F.zo, F.sym, F.SN, F.t0
Ek = F.E ** kk
F.E = None
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
        qq = int(ID.inert_q[i - ID.ns])
        pr = zo.Prime(qq)
        tot = 0j
        for aa in range(qq):
            for bb in range(qq):
                c = pr.sym((aa, bb))
                if c is not None:
                    tot += ZETA6[(kk * c) % 6] * np.exp(2j * np.pi * bb / qq)
        val = dict(a=qq, b=0, G=tot / qq, prime=pr)
    cache[i] = val
    return val


def gauss(gens):
    g = 1 + 0j
    for gi in gens:
        g *= gi['G']
    for a_ in range(len(gens)):
        for b_ in range(a_ + 1, len(gens)):
            g *= (sym(gens[b_]['prime'], (gens[a_]['a'], gens[a_]['b'])) *
                  sym(gens[a_]['prime'], (gens[b_]['a'], gens[b_]['b']))) ** kk
    return g


def orth(V):
    Q, Rr = np.linalg.qr(V)
    d = np.abs(np.diag(Rr))
    return Q[:, d > 1e-8 * d.max()]


Gr = np.array([gauss([genk(int(i)) for i in rows['PID'][zi] if i >= 0]) for zi in range(R)])
rgen = tu.row_data(F)['gen']
rcls = ((rgen[:, 0] % 4) * 4 + rgen[:, 1] % 4) * 81 + (rgen[:, 0] % 9) * 9 + rgen[:, 1] % 9
Nz = rows['N'].astype(float)
QR_ = orth(np.concatenate([tu.class_span(rcls, Gr * (Nz / B) ** (-j / 2)) for j in range(2)], axis=1))
gs = np.zeros(S, complex); npr = np.zeros(S, int)
for j, (a, b, n) in enumerate(zip(F.SA, F.SB, SN)):
    ids = tu.source_prime_ids(F, a, b, n)
    gs[j] = gauss([genk(i) for i in ids]); npr[j] = len(ids)
cell = (((F.SA % 4) * 4 + F.SB % 4) * 81 + (F.SA % 9) * 9 + F.SB % 9) * 2 + npr % 2
beta = 0.5 - 1.0 / q
prof = SN.astype(float) ** (-beta)
QS_ = orth(np.concatenate([tu.class_span(cell, np.conj(gs) * prof), tu.class_span(cell, gs * prof)], axis=1))
print('k=%d (order %d): |G_k| rows %.3f..%.3f, sources %.3f..%.3f; row-theta span dim %d, source-theta span dim %d '
      '(beta %.3f)   (%.0fs)' % (kk, q, np.abs(Gr).min(), np.abs(Gr).max(), np.abs(gs).min(), np.abs(gs).max(),
                                QR_.shape[1], QS_.shape[1], beta, time.time() - t0), flush=True)
U, s, Vh = svds(Ek, k=ntop, random_state=0)
o = np.argsort(-s)
s, U, Vh = s[o], U[:, o], Vh[o]
print('top s^2/S %s   MP edge %.3f' % (np.round(s ** 2 / S, 3), (1 + math.sqrt(R / S)) ** 2), flush=True)
for t in range(ntop):
    cl = QR_.conj().T @ U[:, t]
    cr = QS_.conj().T @ Vh[t].conj()
    print('  pair %d (s^2/S %.3f): left in row thetas %.3f (random %.3f)   right in source thetas %.3f (random %.3f)'
          % (t, s[t] ** 2 / S, float(np.vdot(cl, cl).real), QR_.shape[1] / R, float(np.vdot(cr, cr).real),
             QS_.shape[1] / S), flush=True)
print('done in %.0fs' % (time.time() - t0))
