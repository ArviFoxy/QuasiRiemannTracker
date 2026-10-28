"""
e6_gauss_structure.py -- structure of the block scalars g(D^m, h) themselves (item 5, "what the selected scalar is").

 6a  imprimitive reduction ("Hasse-Davenport-like", exact):   g(p^j, p^{j-1} h') = N^{j-1} G_j(p,h'),  G_j(p,h) := sum_{d mod p} chi_p(d)^j psi_p(h d)
     (so a squared block is a CUBIC Gauss sum, a cubed block a QUADRATIC Gauss sum, a 4th power a conjugate CUBIC sum, ...)
 6b  Davenport-Hasse product relation (m=2):   G_1 G_4 = chi_p(2)^{-2} G_2 G_3
 6c  inert primes (semiprimitive case): g(q,h) = +-q * chi_q(sqrt(-3) h)^{-1}  (real up to the symbol of sqrt(-3) h)
 6d  Kummer-type cube/sixth-power laws:  G_2(pi,1)^3 / (N pi) , G_3^2/N , G_1^6 / (N pi^4)
"""
import time, collections
from common import *

rng = random.Random(99)
t0 = time.time()
res = Counter2()


# 6a ------------------------------------------------------------------------------------------------------
for _ in range(60):
    N = rng.choice([7, 13, 19, 25])
    p = rng.choice([x for x in PRIMES if norm(x) == N])
    for j in range(1, 6 if N <= 13 else 4):
        h = rand_h0(rng, [p])
        lhs = gauss(pw(p, j), mul(pw(p, j - 1), h))
        rhs = N ** (j - 1) * Gj(p, j, h)
        res.add('6a', abs(lhs - rhs) < 1e-6 * abs(rhs), (p, j))
print("6a g(p^j, p^{j-1}h') = N^{j-1} G_j(p,h'):  %d checks, %d failures" % (res.ok['6a'], res.bad['6a']))

# 6b ------------------------------------------------------------------------------------------------------
for p in [x for x in PRIMES if norm(x) <= 400]:
    for h in [ONE, rand_h0(rng, [p]), rand_h0(rng, [p])]:
        G1, G2, G3, G4 = Gj(p, 1, h), Gj(p, 2, h), Gj(p, 3, h), Gj(p, 4, h)
        c2 = chi_exp((2, 0), p)
        pred = zeta6(-2 * c2) * G2 * G3
        res.add('6b', abs(G1 * G4 - pred) < 1e-6 * abs(pred), (p, h))
print("6b DH product: G1 G4 = chi_p(2)^{-2} G2 G3 :  %d checks, %d failures" % (res.ok['6b'], res.bad['6b']))

# 6c ------------------------------------------------------------------------------------------------------
print("6c inert q (primary generator -q):  g(q,h) / ( q * chi_q(sqrt(-3) h)^{-1} ) :")
sq3 = (1, 2)       # 1 + 2 w = sqrt(-3)
rows = []
for q in [5, 11, 17, 23, 29, 41, 47, 53, 59, 71, 83]:
    a = (-q, 0)
    vals = set()
    for _ in range(4):
        h = rand_h0(rng, [a])
        g = gauss(a, h)
        c = chi_exp(mul(sq3, h), a)
        r = g / (q * zeta6(-c))
        vals.add(round(r.real, 6) + 1j * round(r.imag, 6))
    rows.append((q, sorted(vals, key=lambda z: z.real)))
    res.add('6c', all(abs(abs(v) - 1) < 1e-6 and abs(v.imag) < 1e-6 for v in vals), q)
for q, v in rows:
    print("   q=%2d (q mod 12 = %2d):  g/(q chi^{-1}) in %s" % (q, q % 12, [complex(x).real for x in v]))
print("   6c reality check: %d ok, %d bad" % (res.ok['6c'], res.bad['6c']))

# 6d ------------------------------------------------------------------------------------------------------
print("6d Kummer-type laws (split primes pi, primary):")
cnt3 = collections.Counter()
cnt2 = collections.Counter()
cnt1 = collections.Counter()
cnt1b = collections.Counter()
for pi in [x for x in PRIMES if is_prime_int(norm(x)) and norm(x) <= 400]:
    N = norm(pi)
    G2 = Gj(pi, 2, ONE)
    G3 = Gj(pi, 3, ONE)
    G1 = Gj(pi, 1, ONE)
    r3 = G2 ** 3 / (N * to_complex(pi))
    r2 = G3 ** 2 / N
    r1 = G1 ** 6 / (N * to_complex(pi) ** 4)
    cnt3[(round(r3.real, 5), round(r3.imag, 5))] += 1
    cnt2[(round(r2.real, 5), round(r2.imag, 5))] += 1
    cnt1[(round(r1.real, 5), round(r1.imag, 5))] += 1
    # compare with the unit predicted by the DH product:
print("   G_2(pi,1)^3 / (N pi)   takes values:", dict(cnt3))
print("   G_3(pi,1)^2 / N        takes values:", dict(cnt2))
print("   G_1(pi,1)^6 / (N pi^4) takes values:", dict(cnt1))
print("time %.1fs" % (time.time() - t0))
