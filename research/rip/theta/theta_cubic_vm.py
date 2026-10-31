"""The cubic family off the predicted spike family V(M) (the Lean statement's family, cubic case).

V(M) is spanned by, for every supplementary twist t = lambda^e 2^f omega^g (27 cubic characters of the row class modulo
9 and 2) and every twist m in {1} and the sources with N(m) <= M,
  theta   G3 conj chi3(t m) (N z/B)^{-j/2},
  plain   chi3(t m) (N z/B)^{-j/2} and its conjugate,
for j < J.  The script prints the top s^2/S of E3 = E**2 and of E3 off V(M) for the cutoffs given, each against a random
span of the same dimension, with the Marchenko-Pastur edge for R - dim.

usage: python3 -I theta_cubic_vm.py B L [M,M,...] [J] [kinds]   (kinds: 'all' or 'theta')
"""
import os, sys, math, time
sys.dont_write_bytecode = True
import numpy as np
from scipy.sparse.linalg import svds, LinearOperator

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import theta_core as tc      # noqa: E402

B = int(sys.argv[1]); L = int(sys.argv[2])
Ms = [int(t) for t in sys.argv[3].split(',')] if len(sys.argv) > 3 else [0, 30]
J = int(sys.argv[4]) if len(sys.argv) > 4 else 2
kinds = sys.argv[5] if len(sys.argv) > 5 else 'all'
F = tc.build(B, L)
E, R, S, rows, SN, ID, pc, zo, sym, t0 = F.E, F.R, F.S, F.rows, F.SN, F.ID, F.pc, F.zo, F.sym, F.t0
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


G3 = np.zeros(R, complex); lam = np.zeros(R, complex); two = np.zeros(R, complex); om = np.zeros(R, complex)
for zi in range(R):
    gens = [gen3(int(i)) for i in rows['PID'][zi] if i >= 0]
    g = 1 + 0j; vl = 1 + 0j; v2 = 1 + 0j; vo = 1 + 0j
    for gi in gens:
        g *= gi['G']
        vl *= sym3(gi['prime'], (-1, 1)); v2 *= sym3(gi['prime'], (2, 0)); vo *= sym3(gi['prime'], (0, 1))
    for a_ in range(len(gens)):
        for b_ in range(a_ + 1, len(gens)):
            g *= sym3(gens[b_]['prime'], (gens[a_]['a'], gens[a_]['b'])) * sym3(gens[a_]['prime'], (gens[b_]['a'], gens[b_]['b']))
    G3[zi] = g; lam[zi] = vl; two[zi] = v2; om[zi] = vo
sup = [lam ** e * two ** f * om ** g for e in range(3) for f in range(3) for g in range(3)]
print('  cubic Gauss sums and 27 supplementary characters built (%.0fs)' % (time.time() - t0), flush=True)
Nz = rows['N'].astype(float)
profs = [(Nz / B) ** (-j / 2) for j in range(J)]
rng = np.random.default_rng(61)


def orth(V):
    Q, Rr = np.linalg.qr(V)
    keep = np.abs(np.diag(Rr)) > 1e-8 * np.abs(np.diag(Rr)).max()
    return Q[:, keep]


def top_off(Q, k=4):
    if Q is None:
        s = svds(E3, k=k, random_state=0, return_singular_vectors=False)
    else:
        op = LinearOperator((R, S), dtype=complex,
                            matvec=lambda v: (lambda w: w - Q @ (Q.conj().T @ w))(E3 @ v),
                            rmatvec=lambda u: E3.conj().T @ (u - Q @ (Q.conj().T @ u)))
        s = svds(op, k=k, random_state=0, return_singular_vectors=False)
    return np.sort(s)[::-1] ** 2 / S


def mp(d):
    return (1 + math.sqrt((R - d) / S)) ** 2


print('full top %s   MP edge %.3f' % (np.round(top_off(None), 3), mp(0)), flush=True)
order = np.argsort(SN)
for M in Ms:
    idx = order[SN[order] <= M]
    tw = [np.ones(R, complex)] + [E3[:, j] for j in idx]
    cols = []
    for t in sup:
        for m in tw:
            c = t * m
            for p in profs:
                cols.append(G3 * np.conj(c) * p)
                if kinds == 'all':
                    cols.append(c * p)
                    cols.append(np.conj(c) * p)
    Q = orth(np.array(cols).T)
    d = Q.shape[1]
    if d >= R // 2:
        print('V(%d): dim %d >= R/2, skipped' % (M, d)); continue
    Qr = orth(rng.standard_normal((R, d)) + 1j * rng.standard_normal((R, d)))
    print('V(%4d) [%d twists x 27 supplementary, J = %d, %s]: dim %4d' % (M, len(tw), J, kinds, d), flush=True)
    print('  off V(M)        %s   MP edge %.3f' % (np.round(top_off(Q), 3), mp(d)), flush=True)
    print('  off random span %s' % np.round(top_off(Qr), 3), flush=True)
print('done in %.0fs' % (time.time() - t0))
