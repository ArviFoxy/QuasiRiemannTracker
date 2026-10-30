"""Is the top of the sextic spectrum the source-side theta spike?

Poisson in the moduli (rows) writes the source Gram E^H E through the Gauss sums of the sources, and its dual atoms
repeat (multiplicity), exactly as Poisson in the sources does for the row Gram.  The source-side theta vector is
f(x) = g~(x) chi_x(u) N(x)^{-1/2} (normalized Gauss sums of the sources, unit twists u).  Its row image
E f = sum_x g~(x) N(x)^{-1/2} chi_.(x) is dominated by small x, i.e. it is low-frequency in z, which is where the
excess at the top of the spectrum was located (theta_locate.py).

The script computes the source Gauss sums (twisted multiplicativity over the prime factors, as for the rows), the
source-side energy ratio r_src(f) = |E f|^2/(R |f|^2) for f, conj f and random phases with the same profile, and
the overlap of f with the top right singular vectors of E (random level 1/sqrt S).

usage: python3 -I theta_srcspike.py B L
"""
import os, sys, math
sys.dont_write_bytecode = True
import numpy as np
from scipy.sparse.linalg import svds

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import theta_core as tc      # noqa: E402

B = int(sys.argv[1]); L = int(sys.argv[2])
F = tc.build(B, L)
E, R, S, SA, SB, SN, spf, ID, pc, gen, sym = F.E, F.R, F.S, F.SA, F.SB, F.SN, F.spf, F.ID, F.pc, F.generator, F.sym

# source factorization into split prime ideals (squarefree norm), then Gauss sums by twisted multiplicativity
Gsrc = np.zeros(S, complex)
utw = np.zeros((S, 6), complex)
for j, (a, b, n) in enumerate(zip(SA, SB, SN)):
    n = int(n); ids = []
    while n > 1:
        p = int(spf[n]); n //= p
        k = int(ID.pidx[p]); r0 = int(ID.split_r[k])
        r = r0 if (int(a) + int(b) * r0) % p == 0 else p - 1 - r0
        ids.append(ID.ideal_id(p, r))
    gens = [gen(i) for i in ids]
    g = 1 + 0j
    for gi in gens:
        g *= gi['G']
    for x_ in range(len(gens)):
        for y_ in range(x_ + 1, len(gens)):
            g *= sym(gens[y_]['prime'], (gens[x_]['a'], gens[x_]['b'])) * sym(gens[x_]['prime'], (gens[y_]['a'], gens[y_]['b']))
    Gsrc[j] = g
    for kk, u in enumerate(pc.UNITS):
        v = 1 + 0j
        for gi in gens:
            v *= sym(gi['prime'], u)
        utw[j, kk] = v
print('  source |G(x,1)|: min %.3f max %.3f' % (np.abs(Gsrc).min(), np.abs(Gsrc).max()), flush=True)
prof = SN.astype(float) ** -0.5


def rsrc(f):
    v = E @ f
    return float(np.vdot(v, v).real / (R * np.vdot(f, f).real))


U, s, Vh = svds(E, k=6, random_state=0)
o = np.argsort(-s); s = s[o]; Vh = Vh[o]
print('top s^2/S: %s' % np.round(s ** 2 / S, 3))
rng = np.random.default_rng(13)
rb = [rsrc(np.exp(2j * np.pi * rng.random(S)) * prof) for _ in range(12)]
print('random phases, profile N^-1/2: r_src = %.3f +- %.3f' % (np.mean(rb), np.std(rb)))
print('variant              r_src    overlap with top right singular vectors #0..#5 (random level %.3f)' % (1 / math.sqrt(S)))
for name, base in (('G', Gsrc), ('conj G', np.conj(Gsrc))):
    for kk in range(6):
        f = base * utw[:, kk] * prof
        fn = f / np.linalg.norm(f)
        ov = np.abs(Vh.conj() @ fn)
        print('  %-7s * chi(u%d)  %.3f    %s' % (name, kk, rsrc(f), np.round(ov, 3)))

# ---- the span of twisted source thetas G(x) chi_x(h) chi_x(u) N(x)^{-1/2}, small h (both conjugations)
from scipy.sparse.linalg import LinearOperator  # noqa: E402
src_primes = []
for j, (a, b, n) in enumerate(zip(SA, SB, SN)):
    n = int(n); prs = []
    while n > 1:
        p = int(spf[n]); n //= p
        k = int(ID.pidx[p]); r0 = int(ID.split_r[k])
        r = r0 if (int(a) + int(b) * r0) % p == 0 else p - 1 - r0
        prs.append(gen(ID.ideal_id(p, r))['prime'])
    src_primes.append(prs)


def chi_src(h):
    out = np.zeros(S, complex)
    for j, prs in enumerate(src_primes):
        v = 1 + 0j
        for pr in prs:
            t = sym(pr, h)
            if t is None:
                v = 0; break
            v *= t
        out[j] = v
    return out


def top_off_src(Q, k=4):
    op = LinearOperator((R, S), dtype=complex,
                        matvec=lambda v: E @ (v - Q @ (Q.conj().T @ v)),
                        rmatvec=lambda u: (lambda w: w - Q @ (Q.conj().T @ w))(E.conj().T @ u))
    s_ = svds(op, k=k, random_state=0, return_singular_vectors=False)
    return np.sort(s_)[::-1] ** 2 / S


hs = [((a, b), a * a - a * b + b * b) for a in range(-12, 13) for b in range(-12, 13)
      if a % 3 == 2 and b % 3 == 0 and 1 <= a * a - a * b + b * b <= 100]
hs.sort(key=lambda t: t[1])
for M in (1, 30, 100):
    vecs = []
    for h, nh in hs:
        if nh > M:
            continue
        ch = chi_src(h)
        for kk in range(6):
            for base in (Gsrc, np.conj(Gsrc)):
                vecs.append(base * ch * utw[:, kk] * prof)
    Q, _ = np.linalg.qr(np.array(vecs).T)
    mass = np.linalg.norm(Q.conj().T @ Vh[0].conj())
    Qr, _ = np.linalg.qr(rng.standard_normal((S, Q.shape[1])) + 1j * rng.standard_normal((S, Q.shape[1])))
    print('twists N(h) <= %3d: span dim %3d; top right vector mass in span %.3f (random span %.3f); top off span %s, off random span %s' %
          (M, Q.shape[1], mass, np.linalg.norm(Qr.conj().T @ Vh[0].conj()), np.round(top_off_src(Q), 3), np.round(top_off_src(Qr), 3)),
          flush=True)
