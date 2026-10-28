"""
e13_exhaustive.py -- exhaustive (not random) sweep over ALL pairs of primary primes D != n of norm <= 100 (and all prime-power
blocks D^m, m=1..3 where N(D)^m <= 500): the exact sign-free identity  g(D^m n,h) = g(D^m,h) g(n, E0(D^m)^3 D^{4m mod 6} h)
and the ray-sign form, for 3 random generic frequencies per pair.
"""
import itertools, collections
from common import *
rng = random.Random(1)
odd = [(a, b) for a in range(4) for b in range(4) if (a % 2 or b % 2)]
lam_one = {(0, 1), (1, 0), (1, 2), (1, 3), (2, 3), (3, 3)}
def minusq(s):
    N = s[0] * s[0] - s[0] * s[1] + s[1] * s[1]
    return 1 if ((N - 1) // 2) % 2 == 0 else -1
def lamq(s):
    return 1 if s in lam_one else -1
E0_of = {}
for r in odd:
    for E, q in [((1, 0), lambda s: 1), ((-1, 0), minusq), (LAM, lamq), (neg(LAM), lambda s: lamq(s) * minusq(s))]:
        if all(ray_sign(r, s) == q(s) for s in odd):
            E0_of[r] = E
            break
P = [p for p in PRIMES if norm(p) <= 100]
print("primary primes of norm <= 100:", len(P))
tot = bad = 0
by_class = collections.Counter()
for D in P:
    for n in P:
        if n == D:
            continue
        for m in (1, 2, 3):
            B = pw(D, m)
            if norm(B) > 500:
                continue
            for _ in range(3):
                h = generic_h(rng, {D: m, n: 1})
                gB, gn, gs = gauss(B, h), gauss(n, h), gauss(mul(B, n), h)
                k = (4 * m) % 6
                E = pw(E0_of[(B[0] % 4, B[1] % 4)], 3)
                if k:
                    E = mul(E, pw(D, k))
                ok = abs(gs - gB * gauss(n, mul(E, h))) < 1e-7 * abs(gs)
                tot += 1
                bad += (not ok)
                by_class[(B[0] % 4, B[1] % 4)] += 1
print("exhaustive sign-free identity: %d cases, %d failures; classes of B mod 4 covered: %d / 12" % (tot, bad, len(by_class)))
