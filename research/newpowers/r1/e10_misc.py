"""
e10_misc.py -- small exact identities quoted in the report
  M1  generator change:          g(u s, h) = chi_s(u) g(s, h)           (u unit; the ideal, hence chi_s, is unchanged)
  M2  composite pool element:    g(a, E^6 h) = 1[(E,a)=1] g(a,h)         (a with v_p(a) <= 5 at every p | E)
  M3  unit orbit invariance:     N(n) = 1 mod 36 for all n in the support  =>  F_b(zeta h) = F_b(h)  for all six units zeta
"""
from common import *
rng = random.Random(77)
ok = Counter2()
for _ in range(300):
    ps = rng.sample([p for p in PRIMES if norm(p) <= 100], rng.randint(1, 2))
    s = build_element([(p, rng.choice([1, 1, 2])) for p in ps])
    if norm(s) > 20000:
        continue
    u = rng.choice(UNITS)
    h = rand_h0(rng, ps)
    lhs = gauss(mul(u, s), h)
    c = chi_exp(u, s)
    ok.add('M1', abs(lhs - zeta6(c) * gauss(s, h)) < 1e-7 * math.sqrt(norm(s)), (s, u, h))
print("M1 generator change g(us,h) = chi_s(u) g(s,h): %d checks, %d failures" % (ok.ok['M1'], ok.bad['M1']))

for _ in range(400):
    Eps = rng.sample([p for p in PRIMES if norm(p) <= 40], rng.randint(1, 2))
    E = build_element([(p, 1) for p in Eps])
    others = rng.sample([p for p in PRIMES if norm(p) <= 40 and p not in Eps], rng.randint(0, 1))
    a = ONE
    cols = {}
    for p in Eps:
        if rng.random() < 0.6:
            cols[p] = rng.randint(1, 5)
    for p in others:
        cols[p] = rng.randint(1, 2)
    if not cols:
        continue
    a = build_element(list(cols.items()))
    if norm(a) > 400_000:
        continue
    h = rand_h0(rng, list(cols.keys()), 30)
    lhs = gauss(a, mul(pw(E, 6), h))
    coprime = all(p not in cols for p in Eps)
    rhs = gauss(a, h) if coprime else 0
    ok.add('M2', abs(lhs - rhs) < 1e-6 * math.sqrt(norm(a)), (a, E, h))
print("M2 composite pool element g(a,E^6 h) = 1[(E,a)=1] g(a,h) (v_p(a)<=5): %d checks, %d failures" % (ok.ok['M2'], ok.bad['M2']))

# M3
good_primes = [p for p in PRIMES if norm(p) % 36 == 1 and norm(p) <= 800]
print("   primes with N = 1 mod 36 (norm <= 800):", len(good_primes), [norm(p) for p in good_primes[:8]])
for _ in range(100):
    ps = rng.sample(good_primes, rng.randint(1, 3))
    cols = [build_element([(p, 1)]) for p in ps]
    cols = [c for c in cols]
    coeff = [complex(rng.gauss(0, 1), rng.gauss(0, 1)) for _ in cols]
    h = rand_h0(rng, ps, 30)
    vals = []
    for z in UNITS:
        F = sum(c * gauss(a, mul(z, h)) for c, a in zip(coeff, cols))
        vals.append(F)
    ok.add('M3', max(abs(v - vals[0]) for v in vals) < 1e-6 * max(1, abs(vals[0])), (ps, h))
print("M3 unit-orbit invariance for columns with N(n) = 1 mod 36 : %d checks, %d failures" % (ok.ok['M3'], ok.bad['M3']))

# M4  conjugate pairs multiply without any twist:  cross(a^i, conj(a)^j) = 1, i.e. (a/conj a)_3 = 1 and eps(a, conj a) = 1;
#     hence g(a conj a, h) = g(a,h) g(conj a,h) for every h, and g(q,h) = N(a) = q for integer h prime to q (q = a conj a split)
tot = bad = 0
for a in [p for p in PRIMES if is_prime_int(norm(p))]:
    ab = conj(a)
    for i in range(1, 4):
        for j in range(1, 4):
            c2 = (i * j * chi_exp(ab, a) + i * j * chi_exp(a, ab)) % 6
            tot += 1
            bad += (c2 != 0)
    tot += 1
    bad += (ray_sign(a, ab) != 1 or (2 * chi_exp(a, ab)) % 6 != 0)
cnt = 0
okc = 0
for _ in range(100):
    a = rng.choice([p for p in PRIMES if is_prime_int(norm(p)) and norm(p) <= 100])
    h = rand_h0(rng, [a, conj(a)])
    cnt += 1
    okc += abs(gauss(mul(a, conj(a)), h) - gauss(a, h) * gauss(conj(a), h)) < 1e-7 * norm(a)
    hz = (rng.randint(1, 60), 0)
    if hz[0] % norm(a):
        cnt += 1
        okc += abs(gauss(mul(a, conj(a)), hz) - norm(a)) < 1e-7 * norm(a)
print("M4 conjugate pairs: symbol identities %d/%d (all split primary primes of norm <= 400, i,j<=3), Gauss sums %d/%d" % (tot - bad, tot, okc, cnt))
