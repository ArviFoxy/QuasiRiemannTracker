# How much alignment do the ALGEBRAIC properties of cubic Gauss sums permit?
# Adversary: c'(n) = prod_i u(pi_i) * prod_{i<j} conj((pi_i/pi_j)_3)   (twisted multiplicative, |c'|=1)
# with free prime values u(pi) (unimodular), or u(pi) restricted to lam(pi)^(1/3) * {1,w,w^2} (so c'^3 = lam,
# the identity satisfied by g~).  Maximize ||Phi c'||^2 by exact coordinate ascent over primes.
# usage: python3 exp_adversary.py K N [sweeps] [with_marks L]
import sys, os, math, numpy as np
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from zw import *
W3 = np.exp(2j * np.pi / 3)
K, N = int(sys.argv[1]), int(sys.argv[2]); sweeps = int(sys.argv[3]) if len(sys.argv) > 3 else 4
Lm = int(sys.argv[4]) if len(sys.argv) > 4 else 0
ar = Arith(N + 10)
rows = ar.elems(1, K); cols = ar.elems(N // 2, N)
pel = {}
for e in ar.elems(1, N, primes_only=True): pel[(e['ps'][0], e['rs'][0])] = e
A, B = col_arrays(cols)
Phi = np.array([quad_row(ar, A, B, k) for k in rows], dtype=float)
Kp, Np = Phi.shape
# factorization data
keys = sorted({(p, r) for c in cols for p, r in zip(c['ps'], c['rs'])})
kid = {k: i for i, k in enumerate(keys)}
cross = np.ones(Np, complex)          # prod_{i<j} conj((pi_i/pi_j)_3)
members = [[] for _ in keys]
for j, c in enumerate(cols):
    ks = list(zip(c['ps'], c['rs']))
    for i in range(len(ks)):
        members[kid[ks[i]]].append(j)
        for l in range(i + 1, len(ks)):
            ei = pel[ks[i]]
            cross[j] *= np.conj(cubic_sym_elem(ar, ei['a'], ei['b'], ks[l][0], ks[l][1]))
members = [np.array(m) for m in members]
gtab = GaussTable(ar, [pel[k] for k in keys])
utrue = np.array([gtab.prime[k][2] for k in keys])
lam13 = np.array([np.exp(1j * np.angle(complex(pel[k]['a'] - pel[k]['b'] / 2, pel[k]['b'] * math.sqrt(3) / 2)) / 3) for k in keys])
fac_idx = [[kid[k] for k in zip(c['ps'], c['rs'])] for c in cols]
nprime_cols = sum(1 for c in cols if len(c['ps']) == 1)
if Lm:
    marks = ar.elems(Lm, 2 * Lm, primes_only=True)
    Xc = np.array([[0 if t < 0 else np.conj(W3 ** t) for t in cubic_exp(ar, A, B, P)] for P in marks]).T
    Amark = (Xc / np.sqrt([P['N'] for P in marks])).sum(1)     # true orientation conj((n/P)_3)
else:
    Amark = np.ones(Np)

def vec(u):
    v = cross.copy()
    for j, f in enumerate(fac_idx):
        for i in f: v[j] *= u[i]
    return v * Amark

diag = np.sum((Phi ** 2) @ np.abs(Amark) ** 2)
def ratio(u): return np.sum((Phi @ vec(u)) ** 2 if False else np.abs(Phi @ vec(u)) ** 2) / diag
print(f'K={K} N={N} marks={"L="+str(Lm) if Lm else "none"}: K\'={Kp} N\'={Np} primes-in-play={len(keys)} prime columns={nprime_cols} ({nprime_cols/Np:.2%})')
print(f'  large-sieve allowance (K\'+N\')||c||^2/Diag = {(Kp+Np)*np.sum(np.abs(Amark)**2)/diag:.1f}')
print(f'  true Gauss sums: ratio = {ratio(utrue):.3f}')

def ascend(u, mode):
    u = u.copy()
    for s in range(sweeps):
        for i in np.random.default_rng(s).permutation(len(keys)):
            m = members[i]
            v = vec(u) if False else None
            # c' = u_i * a + b with a supported on columns divisible by pi_i
            full = vec(u)
            a = np.zeros(Np, complex); a[m] = full[m] / u[i]
            b = full.copy(); b[m] = 0
            Pa, Pb = Phi @ a, Phi @ b
            z = np.vdot(Pa, Pb)            # <Pa,Pb>; objective 2 Re(conj(u) z) up to constants
            if mode == 'free':
                u[i] = z / abs(z) if abs(z) > 0 else u[i]
            else:                           # u in lam^(1/3) * {1,w,w^2}
                cands = lam13[i] * W3 ** np.arange(3)
                u[i] = cands[np.argmax(np.real(np.conj(cands) * z))]
        print(f'    [{mode}] sweep {s+1}: ratio = {ratio(u):.3f}', flush=True)
    return u
rng = np.random.default_rng(7)
u0 = utrue.copy()
print('  adversary, free unimodular prime values (start: true Gauss sums):')
ascend(u0, 'free')
print('  adversary, prime values constrained to cube roots of lam (start: true Gauss sums):')
ascend(u0, 'cube')
