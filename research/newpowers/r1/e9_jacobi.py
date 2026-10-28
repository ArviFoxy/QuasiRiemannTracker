"""
e9_jacobi.py -- the Jacobi-sum link between simple and squared blocks:
    G_1(D;h)^2 = J_D G_2(D;h),  J_D = G_1(1)^2/G_2(1) in O,  N(J_D) = N(D)  (h-independent),
so  g(D^2, D H') = N(D) G_2(D;H') = N(D) g(D,H')^2 / J_D.
We test: J_D is a unit times D (not times conj D) for split primary D, find the unit u_D = J_D / D and compare with u^3 = -chi_D(-1).
"""
import collections
from common import *
from mpmath import mp
rng = random.Random(5)
tab = collections.Counter()
bad = 0
rows = []
for pi in [p for p in PRIMES if is_prime_int(norm(p)) and norm(p) <= 400]:
    N = norm(pi)
    G1, G2 = Gj(pi, 1, ONE), Gj(pi, 2, ONE)
    J = G1 ** 2 / G2
    # J should be an element of O: J = a + b w
    w = complex(-0.5, math.sqrt(3) / 2)
    b = J.imag / w.imag
    a = J.real - b * w.real
    isint = abs(a - round(a)) < 1e-6 and abs(b - round(b)) < 1e-6
    Jel = (round(a), round(b))
    u = None
    if isint:
        for j, un in enumerate(UNITS):
            if mul(un, pi) == Jel:
                u = j
    chi_m1 = (N - 1) // 2 % 2          # chi_D(-1) = (-1)^{(N-1)/2}
    pred_cube = (3 + 3 * chi_m1) % 6 if False else None
    tab[(isint, u)] += 1
    rows.append((pi, N, Jel, u, chi_m1))
    # h-independence of G1^2/G2
    h = rand_h0(rng, [pi])
    r2 = Gj(pi, 1, h) ** 2 / Gj(pi, 2, h)
    if abs(r2 - J) > 1e-6 * N ** 0.5:
        bad += 1
print("J_D = G_1(1)^2/G_2(1): in O and equal to (unit) * D for all?  counts {(is_integral, unit_index_j with J = zeta6^j * D)}:", dict(tab))
print("h-independence failures:", bad)
# relation of the unit to chi_D(-1):  u^3 = -chi_D(-1)
byparity = collections.defaultdict(collections.Counter)
for pi, N, Jel, u, c in rows:
    byparity[c][u] += 1
print("unit index j (J = zeta6^j D) by chi_D(-1) = (-1)^c :", {k: dict(v) for k, v in byparity.items()})
# squared-block scalar through the simple one
cnt = 0; okc = 0
for pi in [p for p in PRIMES if is_prime_int(norm(p)) and norm(p) in (7, 13, 19, 31)]:
    N = norm(pi)
    for _ in range(5):
        Hp = rand_h0(rng, [pi])
        lhs = gauss(pw(pi, 2), mul(pi, Hp))
        J = Gj(pi, 1, ONE) ** 2 / Gj(pi, 2, ONE)
        rhs = N * gauss(pi, Hp) ** 2 / J
        cnt += 1
        okc += abs(lhs - rhs) < 1e-6 * abs(lhs)
print("g(D^2, D H') = N(D) g(D,H')^2 / J_D :", okc, "/", cnt)

# explicit value of the cube-block scalar (quadratic Gauss sum) for split primary pi = a + b w, N = N(pi) prime:
#   G_3(pi,1) = ((-b)/N) * eps_N * sqrt(N),  eps_N = 1 (N = 1 mod 4), i (N = 3 mod 4)  =>  g(pi^3, pi^2 h') = N^2 (h'/pi)_2 G_3(pi,1)
def legendre(a, p):
    a %= p
    if a == 0:
        return 0
    return 1 if pow(a, (p - 1) // 2, p) == 1 else -1
c3 = [0, 0]
c3b = [0, 0]
for pi in [p for p in PRIMES if is_prime_int(norm(p)) and norm(p) <= 1200]:
    N = norm(pi)
    a, b = pi
    G3 = Gj(pi, 3, ONE) / math.sqrt(N)
    eps = 1 if N % 4 == 1 else 1j
    c3[1] += 1
    c3[0] += abs(G3 - legendre(-b, N) * eps) < 1e-6
    if N <= 20:
        Hp = rand_h0(rng, [pi])
        lhs = gauss(pw(pi, 3), mul(pw(pi, 2), Hp))
        # (h'/pi)_2 = chi_pi(h')^3
        rhs = N ** 2 * zeta6(3 * chi_exp(Hp, pi)) * legendre(-b, N) * eps * math.sqrt(N)
        c3b[1] += 1
        c3b[0] += abs(lhs - rhs) < 1e-6 * abs(lhs)
print("cube-block scalar: G_3(pi,1) = ((-b)/N) eps_N sqrt(N) for pi = a + b w :", c3[0], "/", c3[1],
      "   g(pi^3, pi^2 h') = N^2 (h'/pi)_2 G_3(pi,1):", c3b[0], "/", c3b[1])
