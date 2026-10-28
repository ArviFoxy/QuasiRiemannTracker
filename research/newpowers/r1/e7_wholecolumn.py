"""
e7_wholecolumn.py -- whole-column (polynomial level) form of the exact identities, with the ray sign absorbed.

For a selected block B = D^m (D prime, primary), a family of residual columns a_v (primary, fifth-free, NOT necessarily
prime to D), coefficients B_v and a frequency k = D^{m-1} H' (so that g(B,k) != 0):

   LHS  = sum_v B_v 1[(D,a_v)=1] gaussRow(B a_v, k)
   RHS  = gaussRow(B,k) * sum_v B_v gaussRow(a_v, E * k),         E = E0(B)^3 * D^{(4m mod 6)}        (exact dilation incl. ray sign)

The identity holds for every B_v iff each column a_v with D | a_v vanishes on the right, i.e. v_p(a_v) <= (4m mod 6) + m - 1 =: kappa
(and 6 !| v_p(a_v)) at the primes p | D.   We test the identity inside and outside this range.
"""
import sys, time, collections
from common import *

rng = random.Random(4711)
t0 = time.time()
res = Counter2()
out_range = collections.Counter()

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
assert len(E0_of) == 12

def kfun(m):
    return (4 * m) % 6

for trial in range(900):
    m = rng.choice([1, 1, 2, 2, 3, 4, 5])
    N = rng.choice([7, 7, 13]) if m <= 3 else 7
    D = rng.choice([x for x in PRIMES if norm(x) == N])
    B = pw(D, m)
    if norm(B) > 20000:
        continue
    kap = kfun(m) + m - 1
    # columns
    cols = []
    nbad = 0
    maxj = 5
    for _ in range(rng.randint(3, 8)):
        j = rng.choice([0, 0, 0, 1, 2, 3, 4, 5]) if rng.random() < 0.5 else 0
        extra = rng.sample([x for x in PRIMES if norm(x) in (13, 19, 25, 31, 37) and x != D], rng.randint(0, 2))
        a = mul(pw(D, j), build_element([(x, 1) for x in extra]))
        if a == ONE:
            continue
        if norm(mul(B, a)) > 700_000:
            continue
        cols.append((a, j))
    if not cols:
        continue
    coeff = [complex(rng.gauss(0, 1), rng.gauss(0, 1)) for _ in cols]
    # frequency k = D^{m-1} H' with H' prime to D (sometimes divisible by D once more)
    t = rng.choice([0, 0, 0, 1])
    allp = [D] + [x for a, _ in cols for x, _ in factor(a)]
    Hp = mul(pw(D, t), rand_h0(rng, allp))
    k = mul(pw(D, m - 1), Hp)
    # LHS
    gB = gauss(B, k)
    if abs(gB) < 1e-6:
        continue
    LHS = 0
    for (a, j), c in zip(cols, coeff):
        if j == 0:
            LHS += c * gauss(mul(B, a), k) / math.sqrt(norm(mul(B, a)))
    E0 = E0_of[(B[0] % 4, B[1] % 4)]
    E = mul(pw(E0, 3), pw(D, kfun(m))) if kfun(m) else pw(E0, 3)
    RHS = 0
    for (a, j), c in zip(cols, coeff):
        RHS += c * gauss(a, mul(E, k)) / math.sqrt(norm(a))
    RHS *= gB / math.sqrt(norm(B))
    inrange = all((j == 0) or (j <= kap and j % 6 != 0) for _, j in cols)
    err = abs(LHS - RHS)
    scale = max(1.0, abs(LHS), abs(RHS))
    if inrange:
        res.add('in-range m=%d' % m, err < 1e-7 * scale, (D, m, cols, k))
    else:
        out_range['m=%d total' % m] += 1
        out_range['m=%d identity fails' % m] += (err > 1e-6 * scale)
print("whole-column identity  sum_v B_v 1[(D,a_v)=1] gaussRow(D^m a_v,k) = gaussRow(D^m,k) sum_v B_v gaussRow(a_v, E0^3 D^(4m mod 6) k)")
print("   inside the range v_p(a_v) <= (4m mod 6)+m-1 (and 6 !| v_p):")
for m in range(1, 6):
    print("      m=%d : %d / %d" % (m, res.ok['in-range m=%d' % m], res.ok['in-range m=%d' % m] + res.bad['in-range m=%d' % m]))
print("   outside the range (some column with v_p(a_v) > kappa, or 6 | v_p): identity failed in")
for m in range(1, 6):
    print("      m=%d : %d / %d cases" % (m, out_range['m=%d identity fails' % m], out_range['m=%d total' % m]))
print("failures:", dict(res.bad))
print("time %.1fs" % (time.time() - t0))
