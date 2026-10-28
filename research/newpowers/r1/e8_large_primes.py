"""
e8_large_primes.py -- the cross-factor / leftover / sign-free identities for D of large norm (up to ~10^3) and inert D up to q = 29,
to rule out small-prime artefacts.  n is a small primary prime (norm <= 60), m = 1, 2, 3.
"""
import time, collections
from common import *

rng = random.Random(1618)
t0 = time.time()
BIG = prime_elements(1500)
bigsplit = [p for p in BIG if is_prime_int(norm(p)) and norm(p) >= 200]
biginert = [p for p in BIG if not is_prime_int(norm(p)) and norm(p) >= 121]
small_n = [p for p in BIG if norm(p) <= 60]

odd_classes = [(a, b) for a in range(4) for b in range(4) if (a % 2 or b % 2)]
lam_one = {(0, 1), (1, 0), (1, 2), (1, 3), (2, 3), (3, 3)}
def minusq(s):
    N = s[0] * s[0] - s[0] * s[1] + s[1] * s[1]
    return 1 if ((N - 1) // 2) % 2 == 0 else -1
def lamq(s):
    return 1 if s in lam_one else -1
E0_of = {}
for r in odd_classes:
    for E, q in [((1, 0), lambda s: 1), ((-1, 0), minusq), (LAM, lamq), (neg(LAM), lambda s: lamq(s) * minusq(s))]:
        if all(ray_sign(r, s) == q(s) for s in odd_classes):
            E0_of[r] = E
            break

ok = Counter2()
classes_seen = set()
for trial in range(600):
    m = rng.choice([1, 1, 2, 3])
    cands = [p for p in BIG if norm(p) >= 40 and norm(p) ** m <= 400_000]
    D = rng.choice(cands)
    B = pw(D, m)
    n = rng.choice([x for x in small_n if x != D])
    if rng.random() < 0.3:
        n = mul(n, rng.choice([x for x in small_n if x != D]))
    if norm(B) * norm(n) > 1_800_000:
        continue
    fe = merge({D: m}, {x: e for x, e in factor(n)})
    h = generic_h(rng, fe)
    gB, gn, gs = gauss(B, h), gauss(n, h), gauss(mul(B, n), h)
    if abs(gB) < 1e-6 or abs(gn) < 1e-6:
        continue
    c = chi_exp(D, n)
    e = (ray_sign_exp(B, n) + 2 * m * c) % 6
    ok.add('cross m=%d' % m, root_index(gs / (gB * gn)) == e, (D, m, n))
    k = (4 * m) % 6
    E = mul(pw(E0_of[(B[0] % 4, B[1] % 4)], 3), pw(D, k)) if k else pw(E0_of[(B[0] % 4, B[1] % 4)], 3)
    ok.add('sign-free exact m=%d' % m, abs(gs - gB * gauss(n, mul(E, h))) < 1e-6 * abs(gs), (D, m, n))
    classes_seen.add((B[0] % 4, B[1] % 4))
for m in (1, 2, 3):
    print("m=%d  cross factor: %d/%d   sign-free exact form: %d/%d" % (m, ok.ok['cross m=%d' % m], ok.ok['cross m=%d' % m] + ok.bad['cross m=%d' % m],
          ok.ok['sign-free exact m=%d' % m], ok.ok['sign-free exact m=%d' % m] + ok.bad['sign-free exact m=%d' % m]))
print("residue classes of B mod 4 seen:", len(classes_seen), "of 12; failures:", dict(ok.bad), " time %.1fs" % (time.time() - t0))
