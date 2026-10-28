"""
e11_bidilation.py -- symmetric ("bi-dilation") form of the CRT identity.  Unit scale on BOTH sides of the CRT gives, for coprime
primary D (prime) and n:

   g(D^m n, h) = g(D^m, n^j h) * g(n, D^k h)      exactly,   iff  m (j-1) even  and  k = -m (j+2) (mod 6)

(g(D^m, n^j h) = chi_{D}(n)^{-m j} g(D^m,h),  chi_D(n) = eps(D,n) chi_n(D)).  For odd m this needs j odd and then the ray sign is
absorbed WITHOUT any bounded dilation, e.g. g(Dn,h) = g(D, n h) g(n, D^3 h)  or  g(Dn,h) = g(D, n^3 h) g(n, D h).
"""
import collections
from common import *
rng = random.Random(2468)
tab = collections.defaultdict(lambda: [0, 0])
predicted_exact = {}
for m in range(1, 5):
    for j in range(0, 12):
        for k in range(0, 12):
            predicted_exact[(m, j, k)] = (m * (j - 1)) % 2 == 0 and (k + m * (j + 2)) % 6 == 0
cases = 0
for trial in range(900):
    m = rng.choice([1, 1, 2, 2, 3, 4])
    N = rng.choice([7, 13, 19]) if m <= 2 else 7
    D = rng.choice([x for x in PRIMES if norm(x) == N])
    n = rng.choice([x for x in PRIMES if norm(x) in (7, 13, 19, 31, 37) and x != D])
    if norm(pw(D, m)) * norm(n) > 600_000:
        continue
    h = generic_h(rng, {D: m, n: 1})
    gs = gauss(mul(pw(D, m), n), h)
    gn_h = gauss(n, h)
    if abs(gs) < 1e-6:
        continue
    cases += 1
    for j in range(0, 12):
        gD = gauss(pw(D, m), mul(pw(n, j), h))
        for k in (0, 1, 2, 3, 4, 5):
            val = gD * gauss(n, mul(pw(D, k), h))
            exact = abs(gs - val) < 1e-6 * abs(gs)
            key = (m, j % 6, k)       # only j mod 6 and k mod 6 matter on coprime data
            tab[key][1] += 1
            tab[key][0] += exact
viol = 0
for (m, j6, k), (ok_, tot) in sorted(tab.items()):
    pe = (m * (j6 - 1)) % 2 == 0 and (k + m * (j6 + 2)) % 6 == 0
    # predicted exact for ALL cases iff pe; if not pe the identity must fail for some case (eps=-1 or wrong cubic part)
    if pe and ok_ != tot:
        viol += 1
    if (not pe) and ok_ == tot:
        viol += 1
print("cases:", cases, " cells (m, j mod 6, k mod 6):", len(tab), " violations of the rule:", viol)
print("exact cells (m, j mod 6, k):")
for m in range(1, 5):
    cells = [(j6, k) for (mm, j6, k), (a, b) in sorted(tab.items()) if mm == m and a == b]
    print("   m=%d : (j mod 6, k) = %s" % (m, cells))
