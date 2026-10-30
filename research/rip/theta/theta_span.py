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

# ---------------------------------------------------------------- spectra
from scipy.sparse.linalg import svds, LinearOperator  # noqa: E402
Uv, sv, Vh = svds(E, k=6)
o = np.argsort(-sv); Uv, sv, Vh = Uv[:, o], sv[o], Vh[o]
mp = (math.sqrt(R) + math.sqrt(S)) ** 2 / S
print('  top singular^2/S: %s   MP edge %.3f' % (np.round(sv[:5] ** 2 / S, 3), mp))


def ratio(c):
    v = E.T @ c
    return float(np.vdot(v, v).real / (S * np.vdot(c, c).real))


tN = rows['N'] / B
w_flat = tN ** -0.5
print('\n== dual energy ratio r(c) = |E^T c|^2/(S|c|^2) on the moduli side (random c -> 1) ==')
rr = [ratio(np.exp(2j * np.pi * rng.random(R)) * w_flat) for _ in range(20)]
rnd = float(np.mean(rr))
print('  random-phase rows, same profile: mean %.3f  sd %.3f  max %.3f' % (rnd, np.std(rr), np.max(rr)))
variants = {}
for name, base in (('conj G', np.conj(Grow)), ('G', Grow)):
    for k in range(6):
        c = base * unit_tw[:, k] * w_flat
        variants['%s * chi(u%d)' % (name, k)] = c
best = None
for name, c in variants.items():
    r_ = ratio(c)
    ov = abs(np.vdot(Uv[:, 0], c)) / np.linalg.norm(c)
    ov5 = np.linalg.norm(Uv[:, :5].conj().T @ c) / np.linalg.norm(c)
    print('  %-16s r = %.3f   overlap with top singular vector %.3f, with top-5 span %.3f' % (name, r_, ov, ov5))
    if best is None or r_ > best[1]:
        best = (name, r_, c)
print('  strongest theta variant: %s (r = %.3f)' % (best[0], best[1]))
c_theta = best[2] / np.linalg.norm(best[2])

# ---------------------------------------------------------------- rank-one test across radial profiles
print('\n== Gram of theta vectors across radial profiles (bumps on [1,2]) ==')
centers = np.linspace(1.1, 1.9, 9)
cols = []
Ivals = []
for c0 in centers:
    U = np.exp(-((tN - c0) / 0.09) ** 2)
    cols.append(best[2] / w_flat * U * tN ** -0.5)
    tt = np.linspace(1, 2, 2001)
    Ivals.append(np.trapezoid(np.exp(-((tt - c0) / 0.09) ** 2) * tt ** (-5 / 6), tt))
C = np.array(cols).T                          # R x 9
Fv = E.T @ C                                  # S x 9
K = Fv.conj().T @ Fv / S
D = np.real(np.diag(C.conj().T @ C))          # diagonal (random) expectation
Kn = K / np.sqrt(np.outer(D, D))
ev = np.linalg.eigvalsh(Kn)[::-1]
print('  normalized Gram eigenvalues: %s' % np.round(ev[:5], 3))
phase = np.exp(2j * np.pi * rng.random(R))
Cr = np.array([phase / w_flat * np.exp(-((tN - c0) / 0.09) ** 2) * tN ** -0.5 for c0 in centers]).T
Fr = E.T @ Cr
Kr = Fr.conj().T @ Fr / S
Dr = np.real(np.diag(Cr.conj().T @ Cr))
evr = np.linalg.eigvalsh(Kr / np.sqrt(np.outer(Dr, Dr)))[::-1]
print('  baseline (random phases, same bumps): %s' % np.round(evr[:5], 3))
Iv = np.array(Ivals)
evec = np.linalg.eigh(Kn)[1][:, -1]
cosI = abs(np.dot(evec.conj(), Iv / np.sqrt(D))) / (np.linalg.norm(Iv / np.sqrt(D)))
print('  top eigenvector vs I(U)-weights: |cos| = %.3f' % cosI)

# ---------------------------------------------------------------- detectors on the source side
print('\n== detectors: projection onto the source-side theta direction f = E^T c / |E^T c| ==')
f = E.T @ c_theta
f = f / np.linalg.norm(f)
is_prime = np.array([sqfree_int(int(n)) and int(spf[int(n)]) == int(n) for n in SN])
dets = {
    'plain sum (all ones)': np.ones(S),
    'plain, smooth weight': np.exp(-((SN / L - 0.6) / 0.25) ** 2),
    'prime pool': is_prime.astype(float),
    'random +-1': rng.choice([-1.0, 1.0], S),
}
for name, a in dets.items():
    pr_ = abs(np.vdot(f, a)) / np.linalg.norm(a)
    ea = float(np.linalg.norm(E @ a) ** 2 / (R * np.linalg.norm(a) ** 2))
    print('  %-22s |<a,f>|/|a| = %.4f   (random level 1/sqrt S = %.4f)   energy |Ea|^2/(R|a|^2) = %.3f' %
          (name, pr_, 1 / math.sqrt(S), ea))

# ---------------------------------------------------------------- large sieve off V
print('\n== large sieve off V: top singular^2/S of E with the theta row direction removed ==')
def top_off(Q):
    op = LinearOperator((R, S), dtype=complex,
                        matvec=lambda v: (E @ v) - Q @ (Q.conj().T @ (E @ v)),
                        rmatvec=lambda u: E.conj().T @ (u - Q @ (Q.conj().T @ u)))
    return svds(op, k=1, return_singular_vectors=False)[0]
s1 = top_off(c_theta[:, None])
print('  full: %.3f   off V (rank 1): %.3f   MP edge %.3f' % (sv[0] ** 2 / S, s1 ** 2 / S, mp))
Vmat = np.array([v / np.linalg.norm(v) for v in variants.values()]).T
Q, _ = np.linalg.qr(Vmat)
s2 = top_off(Q)
print('  off V (12 twist variants): %.3f' % (s2 ** 2 / S))
print('done in %.1fs' % (time.time() - t0))
