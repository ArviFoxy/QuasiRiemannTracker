"""cubic_checks.py -- numerics for the cubic analogue of the sextic amplifier identities over O = Z[w].

Uses research/newpowers/r1/zw.py (exact Lean conventions: chi_s(x) = idealRowHom x (span s), psi_s = quotientTrace s,
sexticGauss s h = sum_d chi_s(d) psi_s(h d)).  Cubic Gauss sum: g3(s,h) = sum_d chi_s(d)^2 psi_s(h d)
(chi^2 = cubic residue symbol (x/s)_3, Lean `idealRowHom_square`, `CubicSieve.cubicRow`).

Checks (all double precision; a ratio is identified with an exact root of unity at tolerance 1e-7):
  A  cubic CRT:            g3(ab,h) = chi_a(b)^2 chi_b(a)^2 g3(a,h) g3(b,h)           (a,b coprime, supported)
  A' cubic reciprocity:    chi_a(b)^2 = chi_b(a)^2  for primary coprime a,b (no sign)
  B  dilation:             g3(n,E h) = chi_n(E)^(-2) g3(n,h)                          ((E,n)=1)
  C  exponent table:       g3(D n,h) = c * g3(D,h) * g3(n, D^s h) with c independent of n  <=>  s = 1 (mod 3)
  C' twist-free transfer:  g3(D n,h) = g3(D,h) g3(n,D h)   (no sign, no unit)  -- the cubic "Sil" transfer, cost 2+1 = 3
  D  pool:                 g3(u,p^3 h) = 1_{p not| u} g3(u,h)  for v_p(u) <= 2 ;  fails for some h when v_p(u) = 3
  E  squared block:        g3(D^2 n, D H') = g3(D^2, D H') g3(n, H')   (cubic world: residual undilated, c = 4-1 = 3)
  F  HD decomposition:     g6(a,h)/sqrt N = (h/a)_2 mu(a) alpha(a) G(a) conj(g3(a,h)/sqrt N)   (a sf primary, (h,a)=1)
                           G(a) = conj(chi_a(4)) Gamma(a),  Gamma(a) = N^-1/2 sum_x psi_a(x^2)
  F' signal identities:    gamma1 gamma2 = mu alpha G ;  gamma2^3 = mu alpha ;  gamma4 gamma2 = 1   (a squarefree primary)
  G  sextic D^1 inside the sextic polynomial:  g6(D n,h) = (n/D)_2 g6(D,h) g6(n,D h)   ((n/D)_2 = chi_D(n)^3)
  H  cubic rigidity scan:  for m=1,2 and s in -1..6: twist-free (constant ratio over n) iff 2m+s = 0 mod 3
"""
import sys, math, cmath, random, itertools
sys.path.insert(0, '/home/user/QuasiRiemannTracker/research/newpowers/r1')
import numpy as np
import zw
from zw import mul, pw, norm, conj, is_primary, primary_associate, prime_elements, to_complex

TOL = 1e-7
rng = random.Random(20261029)


def gauss_k(s, h, k):
    """sum_{d mod s} chi_s(d)^k psi_s(h d)  (chi^k := 0 on nonunits, also for 6 | k)"""
    S = zw.get_modulus(s)
    X, Y = S.reps()
    h0, h1 = S.mod.reduce(h)
    P0 = h0 * X - h1 * Y
    P1 = h0 * Y + h1 * X - h1 * Y
    c0, c1 = S.cs
    W1 = P0 * c1 + P1 * c0 - P1 * c1
    ph = np.exp(2j * np.pi * ((W1 % S.N) / S.N))
    ex = S.exps()
    m = ex >= 0
    zeta = np.exp(2j * np.pi * ((k * ex[m]) % 6) / 6.0)
    return complex(np.sum(zeta * ph[m]))


def g6(s, h):
    return gauss_k(s, h, 1)


def g3(s, h):
    return gauss_k(s, h, 2)


def chi(s, x):
    """exponent of chi_s(x) in Z/6, None if not coprime"""
    return zw.get_modulus(s).chi(x)


def z6(j):
    return cmath.exp(2j * math.pi * j / 6)


def root_index(z, n=6):
    """j with z = zeta_n^j (|z| = 1 up to TOL), else None"""
    if abs(abs(z) - 1) > 1e-6:
        return None
    a = cmath.phase(z) / (2 * math.pi) * n
    j = round(a)
    if abs(a - j) > 1e-6:
        return None
    return j % n


PR = prime_elements(200)            # primary primes, norm <= 200 (split and inert -q)
PR = [p for p in PR if norm(p) > 4]


def coprime(a, b):
    return math.gcd(norm(a), norm(b)) == 1 or all(zw.exact_div(a, p) is None for p, _ in zw.factor(b))


def rand_prime(maxN=200, exclude=()):
    while True:
        p = rng.choice(PR)
        if norm(p) <= maxN and all(norm(p) != norm(e) or p != e for e in exclude):
            return p


NCAP = 250000


def rand_primary_sf(k, maxN=150, avoid=(), cap=None):
    """product of k distinct primary primes (squarefree primary element), avoiding the primes in `avoid`;
    total norm <= cap (default: NCAP ** (1/2) for k >= 2 so that products of two such stay small)"""
    cap = cap if cap is not None else (20000 if k == 1 else 3000)
    while True:
        ps = [rng.choice([p for p in PR if norm(p) <= maxN]) for _ in range(k)]
        if len(set(ps)) < k:
            continue
        if any(p == q for p in ps for q in avoid):
            continue
        # also avoid conjugate collisions with same ideal? distinct elements = distinct ideals for primary primes
        x = (1, 0)
        for p in ps:
            x = mul(x, p)
        if norm(x) > cap:
            continue
        return x, ps


def rand_h(s, coprime_to=None, R=60):
    while True:
        h = (rng.randrange(-R, R), rng.randrange(-R, R))
        if h == (0, 0):
            continue
        if coprime_to is not None and chi(coprime_to, h) is None:
            continue
        return h


def count(name, ok, tot):
    print(f"  {name}: {ok}/{tot} pass")
    return ok == tot


results = {}

# ---------------------------------------------------------------- A, A' : CRT and cubic reciprocity
print("A  cubic CRT  g3(ab,h) = chi_a(b)^2 chi_b(a)^2 g3(a,h) g3(b,h)")
ok = tot = 0
okr = totr = 0
for _ in range(300):
    a, pa = rand_primary_sf(rng.choice([1, 2]), 120)
    b, pb = rand_primary_sf(rng.choice([1, 2]), 120, avoid=pa)
    if chi(a, b) is None or norm(a) * norm(b) > NCAP:
        continue
    # random unit multiples (non-primary generators allowed for A)
    ua = rng.choice(zw.UNITS); ub = rng.choice(zw.UNITS)
    A_, B_ = mul(ua, a), mul(ub, b)
    h = rand_h(None)
    lhs = g3(mul(A_, B_), h)
    rhs = z6(2 * chi(A_, B_) + 2 * chi(B_, A_)) * g3(A_, h) * g3(B_, h)
    tot += 1
    ok += abs(lhs - rhs) < TOL * max(1, abs(lhs))
    # cubic reciprocity on the primary generators: chi_a(b)^2 == chi_b(a)^2
    totr += 1
    okr += ((2 * chi(a, b)) % 6 == (2 * chi(b, a)) % 6)
results['A'] = count("CRT (unit-twisted generators)", ok, tot)
results["A'"] = count("cubic reciprocity chi_a(b)^2 = chi_b(a)^2 (primary)", okr, totr)

# ---------------------------------------------------------------- B : dilation
print("B  dilation g3(n,E h) = chi_n(E)^-2 g3(n,h)")
ok = tot = 0
for _ in range(200):
    n, pn = rand_primary_sf(rng.choice([1, 2]), 150)
    E = rand_h(None, coprime_to=n, R=30)
    h = rand_h(None, R=60)
    lhs = g3(n, mul(E, h))
    rhs = z6(-2 * chi(n, E)) * g3(n, h)
    tot += 1
    ok += abs(lhs - rhs) < TOL * max(1, abs(lhs))
results['B'] = count("dilation", ok, tot)

# ---------------------------------------------------------------- C, C', H : transfer exponent table, rigidity
print("C/H  g3(D^m n, D^(m-1) H) = c * g3(D^m, D^(m-1) H) * g3(n, D^s D^(m-1) H): constant c over n  <=>  2m+s = 0 mod 3")
table = {}
for m in (1, 2):
    for s in range(-1, 7):
        if m == 1 and s < 0:
            continue
        consts = set()
        allconst = True
        nonzero = 0
        for trial in range(40):
            D = rand_prime(150)
            n, pn = rand_primary_sf(rng.choice([1, 2]), 120, avoid=[D])
            if chi(D, n) is None or norm(D) ** m * norm(n) > NCAP:
                continue
            H = rand_h(None, coprime_to=mul(D, n), R=40)
            Dm = pw(D, m)
            h = mul(pw(D, m - 1), H)
            lhs = g3(mul(Dm, n), h)
            hres = mul(pw(D, s), h) if s >= 0 else H   # s = -1 (m=2): residual at H' = h / D
            rhs0 = g3(Dm, h) * g3(n, hres)
            if abs(rhs0) < 1e-6:
                continue
            nonzero += 1
            r = lhs / rhs0
            j = root_index(r, 6)
            if j is None:
                allconst = False
                break
            consts.add(j)
        table[(m, s)] = (allconst and len(consts) == 1, sorted(consts), nonzero)
for m in (1, 2):
    row = []
    for s in range(-1, 7):
        if (m, s) not in table:
            row.append("  . ")
            continue
        exact, cs, nz = table[(m, s)]
        pred = ((2 * m + s) % 3 == 0)
        row.append(("EX" if exact else "tw") + ("*" if exact == pred else "!"))
    print(f"  m={m}  s=-1..6 : " + " ".join(row) + "     (EX = constant ratio, tw = twisted; * = as predicted)")
results['C/H'] = all(table[k][0] == ((2 * k[0] + k[1]) % 3 == 0) for k in table)
print("  exact cells:", {k: v[1] for k, v in table.items() if v[0]}, " all as predicted:", results['C/H'])

print("C' twist-free cubic transfer g3(Dn,h) = g3(D,h) g3(n,Dh), primary D,n (split and inert D, h arbitrary incl. D|h)")
ok = tot = 0
for _ in range(400):
    D = rand_prime(200)
    n, pn = rand_primary_sf(rng.choice([1, 2, 3]), 100 if rng.random() < 0.5 else 60, avoid=[D])
    if chi(D, n) is None or norm(D) * norm(n) > NCAP:
        continue
    h = rand_h(None, R=80)
    if rng.random() < 0.2:
        h = mul(D, h)
    lhs = g3(mul(D, n), h)
    rhs = g3(D, h) * g3(n, mul(D, h))
    tot += 1
    ok += abs(lhs - rhs) < TOL * max(1, abs(lhs))
results["C'"] = count("D^1 transfer exact (constant = 1)", ok, tot)

# ---------------------------------------------------------------- D : pool p^3
print("D  pool g3(u,p^3 h) = 1_{p not| u} g3(u,h)  for v_p(u) <= 2 ; v_p(u) = 3 fails")
okin = totin = 0
failout = totout = 0
for _ in range(250):
    p = rand_prime(60)
    u0, pu = rand_primary_sf(rng.choice([1, 2]), 50, avoid=[p])
    i = rng.choice([0, 0, 1, 2, 3])
    u = mul(pw(p, i), u0)
    if norm(u) > 60000:
        continue
    hs = [rand_h(None, R=40) for _ in range(3)]
    if i <= 2:
        allok = True
        for h in hs:
            lhs = g3(u, mul(pw(p, 3), h))
            rhs = g3(u, h) if i == 0 else 0.0
            allok &= abs(lhs - rhs) < TOL * max(1, abs(lhs), abs(rhs))
        totin += 1
        okin += allok
    else:
        anyfail = False
        for h in hs + [mul(p, hs[0]), mul(pw(p, 2), hs[1])]:
            lhs = g3(u, mul(pw(p, 3), h))
            anyfail |= abs(lhs) > 1e-6
        totout += 1
        failout += anyfail
results['D'] = count("pool, v_p(u) in {0,1,2}", okin, totin)
print(f"  pool, v_p(u) = 3: identity fails for some sampled h in {failout}/{totout} cases (expected: all)")

# ---------------------------------------------------------------- E : squared block in the cubic world
print("E  cubic squared block g3(D^2 n, D H') = g3(D^2, D H') g3(n, H')   (D not| H')")
ok = tot = 0
for _ in range(200):
    D = rand_prime(60)
    n, pn = rand_primary_sf(rng.choice([1, 2]), 60, avoid=[D])
    if chi(D, n) is None or norm(D) ** 2 * norm(n) > NCAP:
        continue
    H = rand_h(None, coprime_to=D, R=40)
    h = mul(D, H)
    lhs = g3(mul(pw(D, 2), n), h)
    rhs = g3(pw(D, 2), h) * g3(n, H)
    tot += 1
    ok += abs(lhs - rhs) < TOL * max(1, abs(lhs))
results['E'] = count("cubic squared block, residual undilated", ok, tot)

# ---------------------------------------------------------------- F, F' : Hasse-Davenport decomposition and signal identities
print("F  g6(a,h)/sqrtN = (h/a)_2 mu(a) alpha(a) G(a) conj(g3(a,h)/sqrtN),  G = conj(chi_a(4)) Gamma(a)")


def Gamma(a):
    S = zw.get_modulus(a)
    X, Y = S.reps()
    tot = 0j
    for x0, x1 in zip(X.tolist(), Y.tolist()):
        tot += zw.psi_phase(a, mul((x0, x1), (x0, x1)))
    return tot / math.sqrt(S.N)


ok = tot = 0
oks = [0, 0, 0]
for _ in range(120):
    a, pa = rand_primary_sf(rng.choice([1, 2, 3]), 80)
    if norm(a) > 30000:
        continue
    N = norm(a)
    mu = (-1) ** len(pa)
    alpha = to_complex(a) / abs(to_complex(a))
    G = z6(-chi(a, (4, 0))) * Gamma(a)
    g1 = g6(a, (1, 0)) / math.sqrt(N)
    g2 = g3(a, (1, 0)) / math.sqrt(N)
    g4 = gauss_k(a, (1, 0), 4) / math.sqrt(N)
    oks[0] += abs(g1 * g2 - mu * alpha * G) < 1e-7
    oks[1] += abs(g2 ** 3 - mu * alpha) < 1e-7
    oks[2] += abs(g4 * g2 - 1) < 1e-7
    for _h in range(3):
        h = rand_h(None, coprime_to=a, R=50)
        lhs = g6(a, h) / math.sqrt(N)
        quad = z6(3 * chi(a, h))                 # (h/a)_2 = chi_a(h)^3
        rhs = quad * mu * alpha * G * (g3(a, h) / math.sqrt(N)).conjugate()
        tot += 1
        ok += abs(lhs - rhs) < 1e-7
nF = tot // 3
results['F'] = count("HD decomposition with the quadratic factor (h/a)_2", ok, tot)
print(f"  F' gamma1*gamma2 = mu*alpha*G: {oks[0]}/{nF};  gamma2^3 = mu*alpha: {oks[1]}/{nF};  gamma4*gamma2 = 1 (cubic row: no Mobius): {oks[2]}/{nF}")

# ---------------------------------------------------------------- G : the cubic D^1 inside the SEXTIC polynomial
print("G  sextic: g6(Dn,h) = (n/D)_2 g6(D,h) g6(n,Dh)  (quadratic twist (n/D)_2 = chi_D(n)^3 left by the cubic dilation D^1)")
ok = tot = 0
trivial = 0
for _ in range(300):
    D = rand_prime(150)
    n, pn = rand_primary_sf(rng.choice([1, 2]), 120, avoid=[D])
    if chi(D, n) is None or norm(D) * norm(n) > NCAP:
        continue
    h = rand_h(None, R=60)
    lhs = g6(mul(D, n), h)
    rhs = z6(3 * chi(D, n)) * g6(D, h) * g6(n, mul(D, h))
    if abs(rhs) < 1e-6 and abs(lhs) < 1e-6:
        continue
    tot += 1
    ok += abs(lhs - rhs) < TOL * max(1, abs(lhs))
    trivial += (3 * chi(D, n)) % 6 == 0
results['G'] = count("sextic D^1 = quadratic-twisted", ok, tot)
print(f"  twist (n/D)_2 trivial in {trivial}/{tot} cases (so D^1 is NOT twist-free in the sextic polynomial)")

print("\nSUMMARY:", results)
