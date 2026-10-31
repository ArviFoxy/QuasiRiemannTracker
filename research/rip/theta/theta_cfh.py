"""Is the sextic outlier's row vector the sextic theta function?  (a Chinta-Friedberg-Hoffstein-type test)

The top left singular vector u0 of the sextic matrix is the row image of the source theta (theta_mech_*,
SourceSpike.lean). If it were the coefficient vector tau_6(z) of the theta series on the 6-fold cover of GL(2), then on
prime rows (a) |u0(z)|^2 would be nearly constant, and (b) u0(z)^2, whose analogue tau_6(pi)^2 is conjecturally given by
cubic data (Chinta-Friedberg-Hoffstein; Broker-Hoffstein, Math. Comp. 2016), would correlate with the cubic Gauss sum
g3(z) times class functions of z (mod 4, mod 9).  The script prints, on prime rows and on all rows, the quantiles of
R|u0|^2 (the exponential law is 0.11/0.69/2.30/4.61) and the energy of the unit vectors u0^2/|u0| and its conjugate in
the span of {g3, conj g3, g6, conj g6, 1} times the class indicators, against the same for random phases.

usage: python3 -I theta_cfh.py B L
"""
import os, sys, math, time
sys.dont_write_bytecode = True
import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import theta_util as tu      # noqa: E402

B = int(sys.argv[1]); L = int(sys.argv[2])
A = tu.load_all(B, L, 8)
F, R, rd, U = A.F, A.R, A.rd, A.U
ID, pc, zo, sym, rows = F.ID, F.pc, F.zo, F.sym, F.rows
ZETA6 = np.exp(2j * np.pi * np.arange(6) / 6)
cache = {}


def g3_prime(i):
    """unimodular cubic Gauss sum of a split prime ideal (inert primes: None)."""
    if i in cache:
        return cache[i]
    if i >= ID.ns:
        cache[i] = None
        return None
    p, r = ID.split_pr(np.array([i]))
    p = int(p[0]); r = int(r[0])
    a, b = pc.primary_generator(p, r)
    x = np.arange(1, p, dtype=np.int64)
    code = pc.sym_codes(np.array([p]), np.array([r]), x, np.zeros_like(x))[0]
    G = np.sum(ZETA6[(2 * code.astype(np.int64)) % 6] * np.exp(-2j * np.pi * ((b * x) % p) / p)) / math.sqrt(p)
    cache[i] = G
    return G


prime = rd['isprime'].copy()
g3 = np.zeros(R, complex)
for zi in np.nonzero(prime)[0]:
    ids = [int(i) for i in rows['PID'][zi] if i >= 0]
    v = g3_prime(ids[0])
    if v is None:
        prime[zi] = False
    else:
        g3[zi] = v
g6 = F.Grow
gen = rd['gen']
cls = ((gen[:, 0] % 4) * 4 + gen[:, 1] % 4) * 81 + (gen[:, 0] % 9) * 9 + gen[:, 1] % 9
P = np.nonzero(prime)[0]
print('B=%d: R=%d rows, %d split prime rows, %d classes on them' % (B, R, len(P), len(set(cls[P].tolist()))),
      flush=True)
expo = '(exponential law 0.11/0.69/2.30/4.61)'
for name, sel in (('all rows', np.arange(R)), ('prime rows', P)):
    for t in range(2):
        w = np.abs(U[sel, t]) ** 2
        w = w / w.mean()
        print('  u%d on %-10s: quantiles 10/50/90/99%% of |u|^2/mean %s %s'
              % (t, name, np.round(np.quantile(w, [0.1, 0.5, 0.9, 0.99]), 2), expo), flush=True)


def energy_in(Q, v):
    c = Q.conj().T @ v
    return float(np.vdot(c, c).real / np.vdot(v, v).real)


basis_fns = {'g3': g3[P], 'conj g3': np.conj(g3[P]), 'g6': g6[P], 'conj g6': np.conj(g6[P]), '1': np.ones(len(P))}
Xall = np.concatenate([tu.class_span(cls[P], b.astype(complex)) for b in basis_fns.values()], axis=1)
Q, Rr = np.linalg.qr(Xall)
d = np.abs(np.diag(Rr))
Q = Q[:, d > 1e-8 * d.max()]
print('  span of {g3, conj g3, g6, conj g6, 1} x classes on prime rows: dim %d of %d (random %.3f)'
      % (Q.shape[1], len(P), Q.shape[1] / len(P)), flush=True)
rng = np.random.default_rng(79)
for t in range(2):
    u = U[P, t]
    ph2 = u ** 2 / np.maximum(np.abs(u), 1e-300)
    ph = u / np.maximum(np.abs(u), 1e-300)
    rnd = np.exp(2j * np.pi * rng.random(len(P)))
    print('  u%d: energy in the span of  u^2/|u| %.3f   conj %.3f   phase u/|u| %.3f   |  random phases %.3f'
          % (t, energy_in(Q, ph2), energy_in(Q, np.conj(ph2)), energy_in(Q, ph), energy_in(Q, rnd)), flush=True)
    for nm, b in basis_fns.items():
        if nm == '1':
            continue
        Qb, _ = np.linalg.qr(tu.class_span(cls[P], b.astype(complex)))
        print('      single family %-8s x classes (dim %d): u^2/|u| %.3f, conj %.3f, random %.3f'
              % (nm, Qb.shape[1], energy_in(Qb, ph2), energy_in(Qb, np.conj(ph2)), energy_in(Qb, rnd)), flush=True)
print('done in %.0fs' % (time.time() - F.t0))
