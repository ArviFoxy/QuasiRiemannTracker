"""Theta excess of the supplementary twists lambda^e 2^f u (sextic and cubic families).

For the family E^k at B = L (k = 1 sextic, k = 2 cubic) and every twist t = lambda^e 2^f u (lambda = omega - 1, u a
unit; e, f modulo 6/gcd), the script prints the dual energy r_H(b) = |E^k^H b|^2 / (S |b|^2) of
  theta (Lean convention)  b = G_k conj chi_z^k(t) N^{-1/2},
  other conjugation        b = conj G_k chi_z^k(t) N^{-1/2},
  plain                    b = chi_z^k(t) N^{-1/2},
sorted by the theta excess, against random phases.  G_k is the row Gauss sum of order 6/k with the Kubota character
e(Tr(x/(sqrt(-3) z))) (theta_core's convention).

usage: python3 -I theta_suptwist.py B L k [top]
"""
import os, sys, math, time
sys.dont_write_bytecode = True
import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import theta_core as tc      # noqa: E402

B = int(sys.argv[1]); L = int(sys.argv[2]); kk = int(sys.argv[3])
ntop = int(sys.argv[4]) if len(sys.argv) > 4 else 12
F = tc.build(B, L)
E, R, S, rows, ID, pc, zo, sym, t0 = F.E, F.R, F.S, F.rows, F.ID, F.pc, F.zo, F.sym, F.t0
Ek = E ** kk
del E
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
        q = int(ID.inert_q[i - ID.ns])
        pr = zo.Prime(q)
        tot = 0j
        for aa in range(q):
            for bb in range(q):
                c = pr.sym((aa, bb))
                if c is not None:
                    tot += ZETA6[(kk * c) % 6] * np.exp(2j * np.pi * bb / q)
        val = dict(a=q, b=0, G=tot / q, prime=pr)
    cache[i] = val
    return val


def symk(prime, x):
    v = sym(prime, x)
    return None if v is None else v ** kk


Gk = np.zeros(R, complex); lam = np.zeros(R, complex); two = np.zeros(R, complex); om = np.zeros(R, complex)
neg = np.zeros(R, complex)
for zi in range(R):
    gens = [genk(int(i)) for i in rows['PID'][zi] if i >= 0]
    g = 1 + 0j; vl = 1 + 0j; v2 = 1 + 0j; vo = 1 + 0j; vn = 1 + 0j
    for gi in gens:
        g *= gi['G']
        vl *= symk(gi['prime'], (-1, 1))
        v2 *= symk(gi['prime'], (2, 0))
        vo *= symk(gi['prime'], (0, 1))
        vn *= symk(gi['prime'], (-1, 0))
    for a_ in range(len(gens)):
        for b_ in range(a_ + 1, len(gens)):
            g *= symk(gens[b_]['prime'], (gens[a_]['a'], gens[a_]['b'])) * symk(gens[a_]['prime'], (gens[b_]['a'], gens[b_]['b']))
    Gk[zi] = g; lam[zi] = vl; two[zi] = v2; om[zi] = vo; neg[zi] = vn
prof = (rows['N'].astype(float) / B) ** -0.5
rng = np.random.default_rng(59)


def rH(b):
    v = Ek.conj().T @ b
    return float(np.vdot(v, v).real / (S * np.vdot(b, b).real))


rb = [rH(np.exp(2j * np.pi * rng.random(R)) * prof) for _ in range(12)]
print('k = %d: random phases r_H %.3f +- %.3f   (%.0fs)' % (kk, np.mean(rb), np.std(rb), time.time() - t0), flush=True)
order_k = 6 // math.gcd(6, kk)                       # order of the symbol
seen = {}
for e in range(order_k):
    for f in range(order_k):
        for g in range(3):                           # omega^g
            for h in range(2):                       # (-1)^h
                t = lam ** e * two ** f * om ** g * neg ** h
                key = tuple(np.round(t[:64], 6))
                if key in seen:
                    continue
                seen[key] = (e, f, g, h)
                th = rH(Gk * np.conj(t) * prof)
                ot = rH(np.conj(Gk) * t * prof)
                pl = rH(t * prof)
                seen[key] = (e, f, g, h, th, ot, pl)
res = sorted(seen.values(), key=lambda v: -v[4])
print('twist lambda^e 2^f omega^g (-1)^h   theta (Lean conj)   other conj   plain    [%d distinct twists]' % len(res))
for e, f, g, h, th, ot, pl in res[:ntop]:
    print('  e=%d f=%d g=%d h=%d                    %.3f              %.3f        %.3f' % (e, f, g, h, th, ot, pl))
print('  ... weakest theta twist: %.3f' % res[-1][4])
print('done in %.0fs' % (time.time() - t0))
