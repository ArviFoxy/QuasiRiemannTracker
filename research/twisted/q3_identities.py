"""q3_identities.py -- numerical checks for Q3 (other twisted constructions), on R1's exact Lean-normalised implementation
(research/newpowers/r1/zw.py, validated there against sexticGauss_unit_scale, sexticGauss_coprime_product,
idealRowHom_primary_reciprocity).  Read-only use of R1's code.

A  block-side placement of the j=0 twist (bi-dilation with k = 0):
     g(Dn,h) = eps(D,n) g(D, n^4 h) g(n,h)          and the sign-free form   g(Dn,h) = g(D, n^4 h) g(n, E0(D)^3 h)
   (so the residual is D-independent inside one E0-class of D, and the twist sits in the block factor
    g(D,n^4 h) = chi_n(D)^2 g(D,h) = (n/D)_3-type cubic character of n mod D).
B  twist cancellation: for pairs of primary primes D1 != D2 (incl. conjugate pairs and inert -q), is there (a,b) != (0,0) mod 6
   with chi_n(D1)^a chi_n(D2)^b = 1 for every primary prime n of a large sample?  (expected: never)
C  rational blocks: chi_n(B)^2 = (B/n)_3 for rational B (split p as (p,0), inert -q):
     C1 n = degree-one primary primes  -> distribution of the cubic exponent
     C2 n rational ((p',0) split rational, (-q',0) inert)  -> expected identically 1 (classical: (a/b)_3 = 1 for coprime
        rational a, b);  also the sextic exponent (only the quadratic part may survive).
"""
import sys, os, random, collections, itertools
sys.path.insert(0, '/home/user/QuasiRiemannTracker/research/newpowers/r1')
from common import *          # noqa: F401,F403  (zw: gauss, chi_exp, ray_sign, PRIMES, ...)

rng = random.Random(20261029)
odd = [(a, b) for a in range(4) for b in range(4) if (a % 2 or b % 2)]
lam_one = {(0, 1), (1, 0), (1, 2), (1, 3), (2, 3), (3, 3)}


def minusq(s):
    N = s[0] * s[0] - s[0] * s[1] + s[1] * s[1]
    return 1 if ((N - 1) // 2) % 2 == 0 else -1


def lamq(s):
    return 1 if s in lam_one else -1


E0_of = {}
for r in odd:
    for E, qf in [((1, 0), lambda s: 1), ((-1, 0), minusq), (LAM, lamq), (neg(LAM), lambda s: lamq(s) * minusq(s))]:
        if all(ray_sign(r, s) == qf(s) for s in odd):
            E0_of[r] = E
            break
assert len(E0_of) == 12

# ------------------------------------------------------------------------------------------------------------- A
SMALL = [p for p in PRIMES if 7 <= norm(p) <= 200]
cntA = collections.Counter()
for trial in range(400):
    D = rng.choice(SMALL)
    # n: one or two primes, coprime to D, product norm bounded
    k = rng.choice([1, 1, 2])
    fac = rng.sample([p for p in SMALL if p != D], k)
    n = ONE
    for p in fac:
        n = mul(n, p)
    if norm(n) * norm(D) > 400_000:
        continue
    fe = {D: 1}
    for p in fac:
        fe[p] = fe.get(p, 0) + 1
    h = generic_h(rng, fe)
    gs = gauss(mul(D, n), h)
    if abs(gs) < 1e-6:
        continue
    eps = ray_sign(D, n)
    lhs1 = eps * gauss(D, mul(pw(n, 4), h)) * gauss(n, h)
    E = pw(E0_of[(D[0] % 4, D[1] % 4)], 3)
    lhs2 = gauss(D, mul(pw(n, 4), h)) * gauss(n, mul(E, h))
    cntA['cases'] += 1
    cntA['ok_sign_form'] += abs(gs - lhs1) < 1e-7 * abs(gs)
    cntA['ok_signfree_form'] += abs(gs - lhs2) < 1e-7 * abs(gs)
    # negative control: drop the sign / drop the n^4
    cntA['ctrl_no_sign_ok'] += abs(gs - gauss(D, mul(pw(n, 4), h)) * gauss(n, h)) < 1e-7 * abs(gs)
    cntA['ctrl_no_n4_ok'] += abs(gs - eps * gauss(D, h) * gauss(n, h)) < 1e-7 * abs(gs)
print('A  block-side j=0 form:', dict(cntA))

# ------------------------------------------------------------------------------------------------------------- B
NSAMP = [p for p in PRIMES if 7 <= norm(p) <= 400]
rng.shuffle(NSAMP)
NSAMP = NSAMP[:160]
pairs = []
split = [p for p in PRIMES if is_prime_int(norm(p)) and 7 <= norm(p) <= 150]
inert = [p for p in PRIMES if not is_prime_int(norm(p))]
for D in split[:12]:
    pairs.append(('conjugate', D, conj(D)))
for D1, D2 in itertools.combinations(split[:10], 2):
    pairs.append(('distinct', D1, D2))
for D in split[:6]:
    for q in inert[:2]:
        pairs.append(('split-inert', D, q))
resB = collections.Counter()
witness = []
for kind, D1, D2 in pairs:
    good = []
    for a in range(6):
        for b in range(6):
            if a == 0 and b == 0:
                continue
            allone = True
            for n in NSAMP:
                if n in (D1, D2) or divides(n, D1) or divides(n, D2):
                    continue
                e1, e2 = chi_exp(D1, n), chi_exp(D2, n)
                if e1 is None or e2 is None:
                    continue
                if (a * e1 + b * e2) % 6 != 0:
                    allone = False
                    break
            if allone:
                good.append((a, b))
    resB[(kind, 'pairs')] += 1
    resB[(kind, 'with_relation')] += bool(good)
    if good:
        witness.append((kind, D1, D2, good))
    # joint distribution of (chi_n(D1), chi_n(D2)) exponents
cells = collections.Counter()
D1 = split[0]
D2 = conj(D1)
for n in NSAMP:
    if divides(n, D1) or divides(n, D2):
        continue
    cells[(chi_exp(D1, n), chi_exp(D2, n))] += 1
print('B  twist relations chi_n(D1)^a chi_n(D2)^b == 1 on %d primes n:' % len(NSAMP), dict(resB), 'witnesses:', witness[:3])
print('   joint (chi_n(D), chi_n(conj D)) exponent cells for D=%s: %d of 36 occur' % (D1, len(cells)))

# ------------------------------------------------------------------------------------------------------------- C
rat_split = [p for p in range(7, 200) if p % 3 == 1 and is_prime_int(p)]
rat_inert = [q for q in range(5, 60) if q % 3 == 2 and is_prime_int(q)]
Bs = [(p, 0) for p in rat_split[:8]] + [(-q, 0) for q in rat_inert[:5]]
c1 = collections.Counter()
for B in Bs:
    for n in NSAMP[:80]:
        if norm(n) == norm(B) or divides(n, B):
            continue
        if not is_prime_int(norm(n)):
            continue          # degree-one primes only
        e = chi_exp(B, n)
        if e is None:
            continue
        c1[(2 * e) % 6] += 1  # exponent of chi_n(B)^2 = (B/n)_3
print('C1 rational B, degree-one prime columns n: distribution of the exponent of (B/n)_3 = chi_n(B)^2:', dict(c1))
c2 = collections.Counter()
c2s = collections.Counter()
ncols = [(p, 0) for p in rat_split[8:20]] + [(-q, 0) for q in rat_inert[5:10]]
for B in Bs:
    for n in ncols:
        if abs(n[0]) == abs(B[0]):
            continue
        if not is_supported(n):
            continue
        e = chi_exp(B, n)
        if e is None:
            continue
        c2[(2 * e) % 6] += 1
        c2s[e] += 1
print('C2 rational B, rational columns n: exponent of (B/n)_3:', dict(c2), '; full sextic exponent of chi_n(B):', dict(c2s))
