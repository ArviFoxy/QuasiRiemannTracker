"""
highprec.py -- re-verification of the key identities with mpmath at 40 significant digits
(the symbol exponents and the residue enumeration come from zw.py; every Gauss sum and every comparison below is done in mp).
"""
import time, random, math
from mpmath import mp, mpf, mpc
from common import *

mp.dps = 40
rng = random.Random(8080)
t0 = time.time()
_tabs = {}
ZETA = [mp.expjpi(mpf(j) / 3) for j in range(6)]        # exp(2 pi i j / 6)


def gauss_mp(s, h, j=1):
    """sum_{d mod s} chi_s(d)^j psi_s(h d) in 40-digit arithmetic"""
    S = get_modulus(s)
    N = S.N
    if N not in _tabs:
        _tabs[N] = [mp.expjpi(mpf(2 * k) / N) for k in range(N)]
    tab = _tabs[N]
    X, Y = S.reps()
    ex = S.exps().tolist()
    h0, h1 = S.mod.reduce(h)
    c0, c1 = S.cs
    tot = mpc(0)
    for a, b, e in zip(X.tolist(), Y.tolist(), ex):
        if e < 0:
            continue
        P0 = h0 * a - h1 * b
        P1 = h0 * b + h1 * a - h1 * b
        W1 = P0 * c1 + P1 * c0 - P1 * c1
        tot += ZETA[(j * e) % 6] * tab[W1 % N]
    return tot


def z6(e):
    return ZETA[e % 6]


worst = {}
count = {}


def rec(name, err):
    worst[name] = max(worst.get(name, mpf(0)), err)
    count[name] = count.get(name, 0) + 1


Dsmall = [p for p in PRIMES if norm(p) in (7, 13, 19)]
nsmall = [p for p in PRIMES if norm(p) in (7, 13, 19, 25, 31)]

# (i) m = 1 cross factor and the exact dilated form, (iv) sign absorption --------------------------------------------
E0_of = {}
odd_classes = [(a, b) for a in range(4) for b in range(4) if (a % 2 or b % 2)]
lam_one = {(0, 1), (1, 0), (1, 2), (1, 3), (2, 3), (3, 3)}
def minusq(s):
    N = s[0] * s[0] - s[0] * s[1] + s[1] * s[1]
    return 1 if ((N - 1) // 2) % 2 == 0 else -1
def lamq(s):
    return 1 if s in lam_one else -1
for r in odd_classes:
    for E, q in [((1, 0), lambda s: 1), ((-1, 0), minusq), (LAM, lamq), (neg(LAM), lambda s: lamq(s) * minusq(s))]:
        if all(ray_sign(r, s) == q(s) for s in odd_classes):
            E0_of[r] = E
            break

for trial in range(40):
    D = rng.choice(Dsmall)
    n = rng.choice([p for p in nsmall if p != D])
    h = generic_h(rng, {D: 1, n: 1})
    gD, gn, gDn = gauss_mp(D, h), gauss_mp(n, h), gauss_mp(mul(D, n), h)
    c = chi_exp(D, n)
    e = (ray_sign_exp(D, n) + 2 * c) % 6
    rec('m=1 cross: g(Dn,h) = eps chi_n(D)^2 g(D,h) g(n,h)', abs(gDn - z6(e) * gD * gn) / abs(gDn))
    gdil = gauss_mp(n, mul(pw(D, 4), h))
    rec('m=1 dilated: g(Dn,h) = eps g(D,h) g(n,D^4 h)', abs(gDn - (1 if ray_sign(D, n) == 1 else -1) * gD * gdil) / abs(gDn))
    E0 = E0_of[(D[0] % 4, D[1] % 4)]
    gdil2 = gauss_mp(n, mul(mul(pw(D, 4), pw(E0, 3)), h))
    rec('m=1 sign-free: g(Dn,h) = g(D,h) g(n, D^4 E0^3 h)', abs(gDn - gD * gdil2) / abs(gDn))
    gq = gauss_mp(n, mul(D, h))
    # D^1 dilation leaves (n/D)_2 = chi_D(n)^3
    q = z6(3 * chi_exp(n, D))
    rec('m=1 D^1: g(Dn,h) = g(D,h) (n/D)_2 g(n,D h)', abs(gDn - q * gD * gq) / abs(gDn))

# (ii) m = 2 ------------------------------------------------------------------------------------------------------
for trial in range(25):
    D = rng.choice([p for p in PRIMES if norm(p) in (7, 13)])
    n = rng.choice([p for p in nsmall if p != D and norm(p) <= 25])
    h = generic_h(rng, {D: 2, n: 1})
    B = pw(D, 2)
    gB, gn, gs = gauss_mp(B, h), gauss_mp(n, h), gauss_mp(mul(B, n), h)
    gdil = gauss_mp(n, mul(B, h))
    rec('m=2 squared block: g(D^2 n,h) = g(D^2,h) g(n,D^2 h)', abs(gs - gB * gdil) / abs(gs))
    rec('m=2 cross = chi_n(D)^4', abs(gs - z6(4 * chi_exp(D, n)) * gB * gn) / abs(gs))

# (iii) m = 3 -----------------------------------------------------------------------------------------------------
for trial in range(10):
    D = rng.choice([p for p in PRIMES if norm(p) == 7])
    n = rng.choice([p for p in nsmall if p != D and norm(p) in (13, 19)])
    h = generic_h(rng, {D: 3, n: 1})
    B = pw(D, 3)
    gB, gn, gs = gauss_mp(B, h), gauss_mp(n, h), gauss_mp(mul(B, n), h)
    rec('m=3 cube block: g(D^3 n,h) = eps g(D^3,h) g(n,h)', abs(gs - (1 if ray_sign(D, n) == 1 else -1) * gB * gn) / abs(gs))

# (v) pools --------------------------------------------------------------------------------------------------------
for trial in range(30):
    p = rng.choice([x for x in PRIMES if norm(x) in (7, 13)])
    i = rng.randint(0, 3)
    up = rng.choice([x for x in PRIMES if norm(x) in (13, 19, 31) and x != p])
    u = mul(pw(p, i), up)
    if norm(u) > 12000:
        continue
    h = rand_h0(rng, [p, up])
    lhs = gauss_mp(u, mul(pw(p, 6), h))
    if i == 0:
        rhs = gauss_mp(u, h)
        rec('pool p^6: g(u,p^6 h) = g(u,h) (p !| u)', abs(lhs - rhs) / abs(rhs))
    else:
        rec('pool p^6: g(u,p^6 h) = 0 (p | u, i<=3)  [abs value]', abs(lhs))
    # k = 3 on p !| u : quadratic twist (p/u)_2
    if i == 0:
        rhs3 = z6(-3 * chi_exp(p, u)) * gauss_mp(u, h)
        rec('pool p^3: g(u,p^3 h) = (p/u)_2 g(u,h)', abs(gauss_mp(u, mul(pw(p, 3), h)) - rhs3) / abs(rhs3))

# (vi) Kummer, (vii) inert, (viii) conjugation ------------------------------------------------------------------------
for pi in [x for x in PRIMES if is_prime_int(norm(x)) and norm(x) <= 150][:20]:
    G2 = gauss_mp(pi, ONE, j=2)
    rec('Kummer: G_2(pi,1)^3 = -N pi', abs(G2 ** 3 + norm(pi) * mpc(to_complex(pi).real, to_complex(pi).imag)) if False else
        abs(G2 ** 3 + norm(pi) * (pi[0] + pi[1] * mp.expjpi(mpf(2) / 3))) / (norm(pi) * abs(pi[0] + pi[1] * mp.expjpi(mpf(2) / 3))))
for q in [5, 11, 17, 23, 29]:
    a = (-q, 0)
    h = rand_h0(rng, [a])
    c = chi_exp(mul((1, 2), h), a)
    rec('inert: g(q,h) = (-1)^{(q+1)/2} q chi_q(sqrt(-3) h)^{-1}', abs(gauss_mp(a, h) - (-1) ** ((q + 1) // 2) * q * z6(-c)) / q)
for trial in range(20):
    a = build_element([(rng.choice(Dsmall), 1)])
    h = rand_h0(rng, [a], 20)
    g1 = gauss_mp(a, h)
    g2 = gauss_mp(conj(a), conj(h))
    rec('conjugation: g(conj a, conj h) = conj g(a,h)', abs(g2 - mp.conj(g1)) / abs(g1))

print("mpmath, %d digits:  (max relative error, number of cases)" % mp.dps)
for k in worst:
    print("  %-72s  max err %s   (%d cases)" % (k, mp.nstr(worst[k], 3), count[k]))
print("time %.1fs" % (time.time() - t0))
