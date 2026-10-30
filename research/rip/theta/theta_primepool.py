"""Do prime-pool row vectors carry the top excess of the sextic spectrum?

Row vectors c(z) = sum_{pi split prime, N(pi) <= M} w(pi) chi_z(pi) chi_z(u) (pools of small primes, weights 1 or
N^-1/2, unit twists u), and the same over all small sources (composites included).  Prints the dual energy ratio
r(c) = |E^T c|^2/(S |c|^2) against random-phase pools with the same weights, and the overlap with the top left
singular vector of E.

usage: python3 -I theta_primepool.py B L
"""
import os, sys, math
sys.dont_write_bytecode = True
import numpy as np
from scipy.sparse.linalg import svds

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import theta_core as tc      # noqa: E402

B = int(sys.argv[1]); L = int(sys.argv[2])
F = tc.build(B, L)
E, R, S, SN, spf, unit_tw = F.E, F.R, F.S, F.SN, F.spf, F.unit_tw
U, s, Vh = svds(E, k=3, random_state=0)
o = np.argsort(-s); s = s[o]; U = U[:, o]
print('top s^2/S: %s' % np.round(s ** 2 / S, 3))
is_prime = np.array([int(spf[int(n)]) == int(n) for n in SN])
rng = np.random.default_rng(3)


def r(c):
    v = E.T @ c
    return float(np.vdot(v, v).real / (S * np.vdot(c, c).real))


print('pool                 M     n    r (u0..u5 max, mean)   random-phase pool r    |<c, u_top>| (max over units)')
for kind in ('primes', 'all'):
    for wname in ('flat', 'N^-1/2'):
        for M in (30, 100, 300, 1000):
            sel = (SN <= M) & (is_prime if kind == 'primes' else True)
            idx = np.nonzero(sel)[0]
            if len(idx) == 0:
                continue
            wt = np.ones(len(idx)) if wname == 'flat' else SN[idx].astype(float) ** -0.5
            base = E[:, idx] @ wt
            rs = [r(base * unit_tw[:, k]) for k in range(6)]
            ov = [abs(np.vdot(U[:, 0], base * unit_tw[:, k])) / np.linalg.norm(base) for k in range(6)]
            rr = [r(E[:, idx] @ (wt * np.exp(2j * np.pi * rng.random(len(idx))))) for _ in range(4)]
            print('%-7s %-7s %5d %5d   %.3f  %.3f            %.3f +- %.3f          %.3f' %
                  (kind, wname, M, len(idx), max(rs), np.mean(rs), np.mean(rr), np.std(rr), max(ov)), flush=True)
