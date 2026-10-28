"""common.py -- shared helpers for the R1 experiments (random primary moduli, frequencies with prescribed
valuations, counters)."""
import random, math, collections
from zw import *

PRIMES = prime_elements(400)                 # primary primes, norms <= 400 (incl. inert 25, 121)
SPLIT = [p for p in PRIMES if norm(p) % 3 == 1 and p[1] != 0 or (p[1] == 0 and norm(p) % 3 == 1 and False)]
SPLIT = [p for p in PRIMES if is_prime_int(norm(p))]
INERT = [p for p in PRIMES if not is_prime_int(norm(p))]
MAXMOD = 1_800_000                           # cap on the norm of any modulus whose Gauss sum we enumerate


def pnorm(p):
    return norm(p)


def valuation(x, p):
    if x == (0, 0):
        return 10 ** 9
    return val(x, p)


def coprime_to_all(x, primes):
    return all(not divides(p, x) for p in primes)


def rand_h0(rng, primes, r=40):
    """random nonzero element coprime to the given primes"""
    while True:
        x = (rng.randint(-r, r), rng.randint(-r, r))
        if x != (0, 0) and coprime_to_all(x, primes):
            return x


def generic_h(rng, fact_exps, r=40):
    """frequency h = prod p^{j_p - 1} * h0  (h0 random, coprime to all p) so that every local prime-power
    Gauss sum g(p^{j_p}, h) with 6 !| j_p is nonzero.  fact_exps: dict prime -> exponent in the modulus."""
    h = ONE
    for p, j in fact_exps.items():
        e = j - 1 if j % 6 else max(j - 1, 0)
        h = mul(h, pw(p, e))
    h0 = rand_h0(rng, list(fact_exps.keys()), r)
    return mul(h, h0)


def merge(*dicts):
    out = {}
    for d in dicts:
        for p, e in d.items():
            out[p] = out.get(p, 0) + e
    return out


def elt_from(dct):
    return build_element(list(dct.items()))


class Counter2:
    """pass/fail counters keyed by label"""

    def __init__(self):
        self.ok = collections.Counter()
        self.bad = collections.Counter()
        self.examples = {}

    def add(self, key, passed, info=None):
        if passed:
            self.ok[key] += 1
        else:
            self.bad[key] += 1
            self.examples.setdefault(key, info)

    def total(self, key):
        return self.ok[key] + self.bad[key]

    def all_ok(self):
        return not self.bad


def ray_sign_exp(a, b):
    """exponent (mod 6) of the ray sign: 0 for +1, 3 for -1"""
    s = ray_sign(a, b)
    assert s in (1, -1)
    return 0 if s == 1 else 3


def cmp_root(z, j, scale=1.0, tol=1e-7):
    """is z equal to zeta6^j (to relative tolerance)?"""
    return abs(z - zeta6(j)) <= tol


def root_index(z, tol=1e-7):
    """return j with z == zeta6^j, or None"""
    for j in range(6):
        if abs(z - zeta6(j)) <= tol:
            return j
    return None


def Gj(p, j, h):
    """G_j(p,h) = sum_{d mod p} chi_p(d)^j psi_p(h d)   (p a prime element, any generator): Gauss sum of the power character"""
    S = get_modulus(p)
    X, Y = S.reps()
    h0, h1 = S.mod.reduce(h)
    P0 = h0 * X - h1 * Y
    P1 = h0 * Y + h1 * X - h1 * Y
    c0, c1 = S.cs
    W1 = P0 * c1 + P1 * c0 - P1 * c1
    ph = np.exp(2j * np.pi * ((W1 % S.N) / S.N))
    ex = S.exps()
    m = ex >= 0
    return complex(np.sum(np.exp(2j * np.pi * (j * ex[m]) / 6.0) * ph[m]))
