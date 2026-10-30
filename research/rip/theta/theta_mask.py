"""Is the top of the sextic spectrum above Marchenko-Pastur arithmetic, or the coprimality mask?

E[z, x] = chi_z(x) vanishes when z and x share a prime, so E has a deterministic zero pattern whose variance profile
moves the spectral edge away from the plain Marchenko-Pastur value (sqrt R + sqrt S)^2 / S.  This script compares
the top singular values of E with those of random-phase matrices carrying exactly the same zero pattern
(|E| times i.i.d. uniform phases), and the small-prime structure of their top singular vectors.

usage: python3 -I theta_mask.py B L [seeds]
"""
import os, sys, math
sys.dont_write_bytecode = True
import numpy as np
from scipy.sparse.linalg import svds

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import theta_core as tc      # noqa: E402

B = int(sys.argv[1]); L = int(sys.argv[2])
seeds = int(sys.argv[3]) if len(sys.argv) > 3 else 4
F = tc.build(B, L)
E, R, S, rows, SN, spf = F.E, F.R, F.S, F.rows, F.SN, F.spf
mask = (np.abs(E) > 0.5)
print('zero entries: %.3f of the matrix; MP edge (no mask) %.3f' % (1 - mask.mean(), (math.sqrt(R) + math.sqrt(S)) ** 2 / S))


def top(M, k=5):
    U, s, Vh = svds(M, k=k, random_state=0)
    o = np.argsort(-s)
    return s[o] ** 2 / S, U[:, o[0]], Vh[o[0]]


def small_prime_mass(u, v):
    out = []
    for p in (7, 13, 19):
        rm = np.array([int(n) % p == 0 for n in rows['N']])
        sm = np.array([int(n) % p == 0 for n in SN])
        out.append('p=%d rows %.2f src %.2f' % (p, (np.abs(u[rm]) ** 2).sum() / rm.mean(),
                                                  (np.abs(v[sm]) ** 2).sum() / sm.mean()))
    return '; '.join(out)


s, u, v = top(E)
print('sextic E:        top s^2/S %s   mass ratio on multiples: %s' % (np.round(s, 3), small_prime_mass(u, v)), flush=True)
rng = np.random.default_rng(11)
tops = []
for t in range(seeds):
    Er = mask * np.exp(2j * np.pi * rng.random(E.shape))
    s, u, v = top(Er)
    tops.append(s[0])
    print('masked random %d: top s^2/S %s   mass ratio on multiples: %s' % (t, np.round(s, 3), small_prime_mass(u, v)),
          flush=True)
    del Er
Eu = np.exp(2j * np.pi * rng.random(E.shape))
s, _, _ = top(Eu)
print('unmasked random:  top s^2/S %s' % np.round(s, 3))
print('masked random top: mean %.3f sd %.3f' % (np.mean(tops), np.std(tops)))
