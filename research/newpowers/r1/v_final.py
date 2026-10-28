"""
v_final.py -- exhaustive finite checks and exact laws for the block scalars.

 V1  all 144 pairs of odd classes (B mod 4, n mod 4): the sextic reciprocity sign  chi_B(n)/chi_n(B)  equals ray_sign(B,n)
     (checked with actual primary elements in every class pair, 20 samples each)           [Lean: idealRowHom_primary_reciprocity]
 V2  the finite table identity   ray_sign(r,s) = (E0(r)/s)_2   for all 144 class pairs, with E0(r) in {1,-1,lambda,-lambda}
     where (-1/s)_2 = (-1)^{(N(s)-1)/2},  (lambda/s)_2 = lambdaQuadraticTable(s)  (Lean tables)
 V3  g(D,h)^6 = (-1)^{(N D-1)/2} N(D) D^4  for squarefree primary D and every h prime to D
 V4  Kummer: G_2(pi,1)^3 = - N(pi) pi ,  G_3(pi,1)^2 = chi_pi(-1) N(pi)
 V5  inert q: g(q,h) = (-1)^{(q+1)/2} q chi_q(sqrt(-3) h)^{-1}
 V6  unit orbit laws:  g(n,-h) = (-1)^{(N n-1)/2} g(n,h),  g(n, w h) = w^{-(N n-1)/6} g(n,h)
"""
import time, collections
from common import *

rng = random.Random(31337)
t0 = time.time()
res = Counter2()

# --- classes ---------------------------------------------------------------------------------------------
def primary_reps(r, count, rng, bound=80):
    out = []
    tries = 0
    while len(out) < count and tries < 20000:
        tries += 1
        a, b = rng.randint(-bound, bound), rng.randint(-bound, bound)
        x = (a, b)
        if (a % 4, b % 4) == r and is_primary(x) and norm(x) > 1:
            out.append(x)
    return out

odd_classes = [(a, b) for a in range(4) for b in range(4) if (a % 2 or b % 2)]
assert len(odd_classes) == 12
for r in odd_classes:
    for s in odd_classes:
        Bs = primary_reps(r, 5, rng)
        ns = primary_reps(s, 5, rng)
        for B in Bs:
            for n in ns:
                if any(divides(p, n) for p, _ in factor(B)):
                    continue
                e = (chi_exp(n, B) - chi_exp(B, n)) % 6        # chi_B(n)/chi_n(B)
                res.add('V1', e == (0 if ray_sign(B, n) == 1 else 3), (B, n))
                res.add('V1b', ray_sign(B, n) == ray_sign(r, s), (B, n))
print("V1 reciprocity sign over all 144 class pairs: %d checks, %d failures" % (res.ok['V1'] + res.bad['V1'], res.bad['V1']))

# --- V2 -----------------------------------------------------------------------------------------------
lam_table_one = {(0, 1), (1, 0), (1, 2), (1, 3), (2, 3), (3, 3)}

def lamq(s):      # lambdaQuadraticTable
    return 1 if s in lam_table_one else -1

def minusq(s):    # (-1/s)_2 = (-1)^{(N(s)-1)/2}, N(s) from the class mod 4
    N = s[0] * s[0] - s[0] * s[1] + s[1] * s[1]
    return 1 if ((N - 1) // 2) % 2 == 0 else -1

# check these two tables against actual symbols
for s in odd_classes:
    for n in primary_reps(s, 6, rng):
        res.add('V2tab', (3 * chi_exp(LAM, n)) % 6 == (0 if lamq(s) == 1 else 3), (s, n))
        res.add('V2tab', (3 * chi_exp((-1, 0), n)) % 6 == (0 if minusq(s) == 1 else 3), (s, n))
print("V2 tables (lambdaQuadraticTable, (-1/s)_2) vs actual symbols: %d checks, %d failures" % (res.ok['V2tab'] + res.bad['V2tab'], res.bad['V2tab']))

E0 = {}
for r in odd_classes:
    found = None
    for name, q in [('1', lambda s: 1), ('-1', minusq), ('lambda', lamq), ('-lambda', lambda s: lamq(s) * minusq(s))]:
        if all(ray_sign(r, s) == q(s) for s in odd_classes):
            found = name
            break
    E0[r] = found
    res.add('V2', found is not None, r)
print("V2 ray_sign(r,s) = (E0(r)/s)_2 for all 12 x 12 class pairs; E0 by class mod 4:")
byE = collections.defaultdict(list)
for r, nm in E0.items():
    byE[nm].append(r)
for nm in ['1', '-1', 'lambda', '-lambda']:
    print("      E0 = %-8s : B mod 4 in %s" % (nm, sorted(byE[nm])))
print("   failures:", res.bad['V2'])

# --- V3 ------------------------------------------------------------------------------------------------
pl = [p for p in PRIMES if norm(p) <= 150]
for _ in range(400):
    k = rng.randint(1, 3)
    ps = rng.sample(pl, k)
    D = build_element([(p, 1) for p in ps])
    if norm(D) > 60000:
        continue
    h = rand_h0(rng, ps)
    g = gauss(D, h)
    N = norm(D)
    sign = 1 if ((N - 1) // 2) % 2 == 0 else -1
    pred = sign * N * to_complex(pw(D, 4))
    res.add('V3', abs(g ** 6 - pred) < 1e-6 * abs(pred), (D, h))
print("V3 g(D,h)^6 = (-1)^{(N-1)/2} N(D) D^4 : %d checks, %d failures" % (res.ok['V3'] + res.bad['V3'], res.bad['V3']))

# --- V4 ------------------------------------------------------------------------------------------------
for pi in [x for x in PRIMES if is_prime_int(norm(x)) and norm(x) <= 700]:
    N = norm(pi)
    G2 = Gj(pi, 2, ONE)
    G3 = Gj(pi, 3, ONE)
    res.add('V4a', abs(G2 ** 3 + N * to_complex(pi)) < 1e-6 * N ** 1.5, pi)
    res.add('V4b', abs(G3 ** 2 - (1 if ((N - 1) // 2) % 2 == 0 else -1) * N) < 1e-6 * N, pi)
print("V4 Kummer G_2^3 = -N pi : %d checks, %d failures;  G_3^2 = chi(-1) N : %d checks, %d failures" %
      (res.ok['V4a'] + res.bad['V4a'], res.bad['V4a'], res.ok['V4b'] + res.bad['V4b'], res.bad['V4b']))

# --- V5 ------------------------------------------------------------------------------------------------
sq3 = (1, 2)
for q in [5, 11, 17, 23, 29, 41, 47, 53, 59, 71, 83, 89, 101]:
    a = (-q, 0)
    for _ in range(5):
        h = rand_h0(rng, [a])
        g = gauss(a, h)
        c = chi_exp(mul(sq3, h), a)
        pred = (-1) ** ((q + 1) // 2) * q * zeta6(-c)
        res.add('V5', abs(g - pred) < 1e-6 * q, (q, h))
print("V5 inert Gauss sums g(q,h) = (-1)^{(q+1)/2} q chi_q(sqrt(-3) h)^{-1} : %d checks, %d failures" % (res.ok['V5'] + res.bad['V5'], res.bad['V5']))

# --- V6 ------------------------------------------------------------------------------------------------
for _ in range(300):
    ps = rng.sample(pl, rng.randint(1, 3))
    n = build_element([(p, rng.choice([1, 1, 2])) for p in ps])
    if norm(n) > 40000:
        continue
    h = rand_h0(rng, ps)
    N = norm(n)
    g = gauss(n, h)
    res.add('V6a', abs(gauss(n, neg(h)) - (-1) ** ((N - 1) // 2) * g) < 1e-6 * math.sqrt(N), (n, h))
    res.add('V6b', abs(gauss(n, mul(W, h)) - zeta6(-((N - 1) // 3)) * g) < 1e-6 * math.sqrt(N), (n, h))
print("V6 unit orbit: g(n,-h)=(-1)^{(N-1)/2} g(n,h): %d checks, %d failures ; g(n,w h) = zeta6^{-(N-1)/3} g(n,h): %d checks, %d failures" %
      (res.ok['V6a'] + res.bad['V6a'], res.bad['V6a'], res.ok['V6b'] + res.bad['V6b'], res.bad['V6b']))
print("time %.1fs" % (time.time() - t0))
