"""Reciprocity signs by row class mod 4: is any class anti-self-dual?

At L = B, Poisson in the sources gives G_off(z, z') ~ s(z, z') chi_z'(-1) g~(z) conj g~(z') conj G_dual(z, z'), with the
reciprocity factor s(z, z') = (z'/z)_6 conj (z/z')_6 (fresh look, section 1.5).  If the effective sign
s(z, z') chi_z'(-1) were -1 on all pairs of a row class, the class Gram would be anti-self-dual and positivity would cap
its top at about twice the diagonal.  The script, for rows z grouped by their primary generator mod 4 (12 classes):
  1. tabulates s(z, z') over pairs of a row sample, by class pair;
  2. tabulates chi_z(-1) by class;
  3. compares, per class, the off-diagonal spectrum of the class Gram (lambda_max + lambda_min, in units of the
     diagonal) with random phases on the same zero pattern and with Marchenko-Pastur;
  4. measures the theta excess r(conj G chi_z(u) profile) restricted to each class.

usage: python3 -I theta_classes.py B L [sample]
"""
import os, sys
sys.dont_write_bytecode = True
from collections import defaultdict
import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(HERE, '..'))
import theta_core as tc      # noqa: E402
import zomega as zo          # noqa: E402

B = int(sys.argv[1]); L = int(sys.argv[2])
nsamp = int(sys.argv[3]) if len(sys.argv) > 3 else 150
F = tc.build(B, L)
E, R, S, rows, gen, sym, Grow, unit_tw = F.E, F.R, F.S, F.rows, F.generator, F.sym, F.Grow, F.unit_tw
elts, primes, cls, chim1 = [], [], [], []
for zi in range(R):
    x = (1, 0); prs = []; v = 1 + 0j
    for i in rows['PID'][zi]:
        if i >= 0:
            g = gen(int(i)); x = zo.mul(x, (g['a'], g['b'])); prs.append(g['prime']); v *= sym(g['prime'], (-1, 0))
    elts.append(x); primes.append(prs); cls.append((x[0] % 4, x[1] % 4))
    chim1.append(int(round(np.angle(v) / (np.pi / 3))) % 6)
cls = np.array(cls); chim1 = np.array(chim1)
keys = sorted(set(map(tuple, cls)))


def chi(prs, x):
    v = 1 + 0j
    for p in prs:
        s = sym(p, x)
        if s is None:
            return 0
        v *= s
    return v


# 1. reciprocity factor on a sample of pairs
rng = np.random.default_rng(1)
pick = rng.choice(R, nsamp, replace=False)
tab = defaultdict(lambda: np.zeros(6, int))
for i in pick:
    for j in pick:
        if i == j:
            continue
        a = chi(primes[i], elts[j]); b = chi(primes[j], elts[i])
        if a != 0 and b != 0:
            tab[(tuple(cls[i]), tuple(cls[j]))][int(round(np.angle(a * np.conj(b)) / (np.pi / 3))) % 6] += 1
const = all((h > 0).sum() == 1 for h in tab.values())
print('1. s(z, z\') over %d ordered pairs: values %s; constant on every class pair: %s' %
      (sum(h.sum() for h in tab.values()), sorted({int(np.nonzero(h)[0][0]) * 60 for h in tab.values()}), const))
sdiag = {c: (int(np.nonzero(tab[(c, c)])[0][0]) if (c, c) in tab else None) for c in keys}
# 2. chi_z(-1) by class
print('2. class: s within the class (code: 0 = +1, 3 = -1), chi_z(-1) codes, effective sign')
for c in keys:
    h = np.bincount(chim1[(cls == c).all(1)], minlength=6)
    eff = (sdiag[c] + int(np.nonzero(h)[0][0])) % 6 if sdiag[c] is not None and (h > 0).sum() == 1 else None
    print('   %s  s %s  chi(-1) %s  effective %s' % (c, sdiag[c], h, '+1' if eff == 0 else ('-1' if eff == 3 else eff)))
# 3, 4. per-class spectra and theta excess
prof = (rows['N'] / B) ** -0.5


def r(c):
    v = E.T @ c
    return float(np.vdot(v, v).real / (S * np.vdot(c, c).real))


print('3, 4. class  n   lmax+lmin (sextic, masked random, MP)   theta excess (mean over units) vs random phases')
for c in keys:
    I = np.nonzero((cls == c).all(1))[0]
    A = E[I]
    G = A @ A.conj().T
    ev = np.linalg.eigvalsh(G - np.diag(np.diag(G))) / np.real(np.diag(G)).mean()
    Ar = np.abs(A) * np.exp(2j * np.pi * rng.random(A.shape))
    Gr = Ar @ Ar.conj().T
    evr = np.linalg.eigvalsh(Gr - np.diag(np.diag(Gr))) / np.real(np.diag(Gr)).mean()
    m = (cls == c).all(1).astype(float)
    th = np.mean([r(np.conj(Grow) * unit_tw[:, k] * prof * m) for k in range(6)])
    rb = np.mean([r(np.exp(2j * np.pi * rng.random(R)) * prof * m) for _ in range(4)])
    print('   %s %4d   %+.3f  %+.3f  %+.3f      %+.3f' % (c, len(I), ev[-1] + ev[0], evr[-1] + evr[0], 2 * len(I) / S, th - rb))
