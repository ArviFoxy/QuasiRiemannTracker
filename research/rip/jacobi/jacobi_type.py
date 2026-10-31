"""Infinity types of sextic Jacobi sums over Z[omega]: is J(chi6, chi6) ~ pi or conj(pi), and J(chi6, chi6^2)?"""
import cmath, math
w = cmath.exp(2j * math.pi / 3)
def primes(n):
    s = bytearray([1]) * (n + 1); s[0] = s[1] = 0
    for i in range(2, int(n ** .5) + 1):
        if s[i]: s[i*i::i] = bytearray(len(s[i*i::i]))
    return [i for i in range(n + 1) if s[i]]
units = [cmath.exp(2j * math.pi * k / 6) for k in range(6)]
def unit_index(z):
    best = min(range(6), key=lambda k: abs(z - units[k]))
    return best, abs(z - units[best])
stats = {'JJ': {'pi': 0, 'conjpi': 0, 'neither': 0}, 'JJ2': {'pi': 0, 'conjpi': 0, 'neither': 0}}
rows = []
for p in primes(3000):
    if p % 3 != 1:
        continue
    # pi = a + b w with norm a^2 - ab + b^2 = p
    found = None
    for a in range(-60, 61):
        for b in range(-60, 61):
            if a * a - a * b + b * b == p:
                found = (a, b); break
        if found: break
    a, b = found
    # r with r^2 + r + 1 = 0 mod p and a + b r = 0 mod p
    r = next(x for x in range(p) if (x * x + x + 1) % p == 0 and (a + b * x) % p == 0)
    sixth = {1: 1, p - 1: -1, r: w, r * r % p: w * w, (-r) % p: -w, (-r * r) % p: -w * w}
    e = (p - 1) // 6
    chi = [0] * p
    for x in range(1, p):
        chi[x] = sixth[pow(x, e, p)]
    J1 = sum(chi[x] * chi[(1 - x) % p] for x in range(2, p))
    J2 = sum(chi[x] * (chi[(1 - x) % p] ** 2) for x in range(2, p))
    pic = a + b * w
    for name, J in (('JJ', J1), ('JJ2', J2)):
        k1, d1 = unit_index(J / pic)
        k2, d2 = unit_index(J / pic.conjugate())
        if d1 < 1e-6: stats[name]['pi'] += 1
        elif d2 < 1e-6: stats[name]['conjpi'] += 1
        else: stats[name]['neither'] += 1
    rows.append((p, a, b, J1, J2))
print('primes p = 1 mod 3 up to 3000:', len(rows))
for name in stats:
    print(name, stats[name])
for p, a, b, J1, J2 in rows[:6]:
    print(p, (a, b), 'J(chi,chi)=%.3f%+.3fi' % (J1.real, J1.imag), ' J(chi,chi^2)=%.3f%+.3fi' % (J2.real, J2.imag),
          ' |J|^2/p = %.6f, %.6f' % (abs(J1) ** 2 / p, abs(J2) ** 2 / p))
