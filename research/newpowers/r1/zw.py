"""
zw.py -- arithmetic in O = Z[w] (w = e^{2 pi i/3}, w^2 = -1 - w), sextic residue symbols and
sextic Gauss sums, normalised EXACTLY as in the Lean development (OpenAI baseline):

  elements         x = a + b w  <->  tuple (a, b)
  lambda           = w - 1           (the prime above 3)
  Supported(s)     := s != 0 and every prime factor P of (s) has  lambda not in P  and  char(O/P) != 2
                      (i.e. s is coprime to 6; NOT required squarefree, NOT required primary)
  primary          := lambda^2 | s - 1   <=>   s = 1 mod 3        (unique generator of an ideal prime to 3)
  (x/P)_6          := the unique zeta in mu_6 with zeta = x^{(N P - 1)/6} mod P,  embedded via w -> e^{2 pi i/3}
                      (Lean: actualSextic = canonicalSextic = (cubicChar^2 * quadraticChar).ringHomComp eisEmbedding)
  chi_s(x)         := idealRowHom x (span s) = prod_{P^e || s} (x/P)_6^e         (0 if x not coprime to s)
  psi_s(x)         := exp(2 pi i Tr_{K/Q}( x / (s * sqrt(-3)) )),  sqrt(-3) = 1 + 2 w = i sqrt 3
                      (Lean: quotientTrace s = breveE(eisEmbedding x / (eisLam * eisEmbedding s)),
                       breveE z = exp(2 pi i (z + conj z)), eisLam = 1 + 2 omega3)
  g(s,h)           := sexticGauss s h = sum_{d in O/(s)} chi_s(d) psi_s(h d)
  gaussRow(s,h)    := g(s,h) / sqrt(N(s))

All exact bookkeeping (symbol exponents, twists) is done with integers mod 6; complex numbers only enter
in Gauss sums themselves (double precision numpy; mpmath is used in `highprec.py` for a subset).
"""
import math
import cmath
import random
from functools import lru_cache

import numpy as np

# ----------------------------------------------------------------------------------------------
# basic arithmetic
# ----------------------------------------------------------------------------------------------
ONE = (1, 0)
W = (0, 1)
LAM = (-1, 1)                      # lambda = w - 1
UNITS = [(1, 0), (1, 1), (0, 1), (-1, 0), (-1, -1), (0, -1)]   # zeta6^j, zeta6 = 1 + w = e^{i pi/3}
UNIT_INDEX = {u: j for j, u in enumerate(UNITS)}


def add(x, y):
    return (x[0] + y[0], x[1] + y[1])


def sub(x, y):
    return (x[0] - y[0], x[1] - y[1])


def neg(x):
    return (-x[0], -x[1])


def mul(x, y):
    a, b = x
    c, d = y
    return (a * c - b * d, a * d + b * c - b * d)


def conj(x):
    a, b = x
    return (a - b, -b)


def norm(x):
    a, b = x
    return a * a - a * b + b * b


def pw(x, e):
    r = ONE
    b = x
    while e > 0:
        if e & 1:
            r = mul(r, b)
        b = mul(b, b)
        e >>= 1
    return r


def exact_div(x, d):
    """z with d*z = x, or None."""
    n = norm(d)
    t = mul(x, conj(d))
    if t[0] % n or t[1] % n:
        return None
    return (t[0] // n, t[1] // n)


def divides(d, x):
    return exact_div(x, d) is not None


def to_complex(x):
    a, b = x
    return a + b * complex(-0.5, math.sqrt(3) / 2)


def is_unit(x):
    return norm(x) == 1


def val(x, p):
    """valuation of x at the prime element p (x != 0)."""
    e = 0
    while True:
        q = exact_div(x, p)
        if q is None:
            return e
        x = q
        e += 1


def congruent(x, y, m):
    """x = y mod m (m an element)"""
    return divides(m, sub(x, y))


def is_primary(x):
    return x[0] % 3 == 1 and x[1] % 3 == 0     # x = 1 mod 3


def primary_associate(x):
    """the unique associate of x that is = 1 mod 3 (None if lambda | x)"""
    for u in UNITS:
        y = mul(u, x)
        if y[0] % 3 == 1 and y[1] % 3 == 0:
            return y
    return None


def egcd(a, b):
    if b == 0:
        return (abs(a), (1 if a >= 0 else -1), 0)
    g, x, y = egcd(b, a % b)
    return (g, y, x - (a // b) * y)


# ----------------------------------------------------------------------------------------------
# residues modulo an element s: canonical forms via HNF of the lattice (s) = s*Z + s*w*Z
# ----------------------------------------------------------------------------------------------
class Mod:
    def __init__(self, s):
        s1, s2 = s
        self.s = s
        self.N = norm(s)
        # lattice rows  v1 = s = (s1, s2),  v2 = s*w = (-s2, s1 - s2)
        g, p, q = egcd(s2, s1 - s2)
        assert g > 0
        self.C = g
        Bp = p * s1 + q * (-s2)
        self.A = self.N // self.C
        assert self.A * self.C == self.N
        self.B = Bp % self.A

    def reduce(self, x):
        a, b = x
        k = b // self.C
        a -= k * self.B
        b -= k * self.C
        return (a % self.A, b)

    def idx(self, x):
        a, b = self.reduce(x)
        return a * self.C + b

    def idx_arrays(self, X, Y):
        k = Y // self.C
        a = (X - k * self.B) % self.A
        b = Y - k * self.C
        return a * self.C + b

    def all_reps(self):
        return [(a, b) for a in range(self.A) for b in range(self.C)]

    def rep_arrays(self):
        a = np.repeat(np.arange(self.A, dtype=np.int64), self.C)
        b = np.tile(np.arange(self.C, dtype=np.int64), self.A)
        return a, b

    def powmod(self, x, e):
        r = (1, 0)
        r = self.reduce(r)
        b = self.reduce(x)
        while e > 0:
            if e & 1:
                r = self.reduce(mul(r, b))
            b = self.reduce(mul(b, b))
            e >>= 1
        return r


@lru_cache(maxsize=None)
def get_mod(s):
    return Mod(s)


# ----------------------------------------------------------------------------------------------
# rational factorisation and primes of O
# ----------------------------------------------------------------------------------------------
def factor_int(n):
    f = {}
    d = 2
    while d * d <= n:
        while n % d == 0:
            f[d] = f.get(d, 0) + 1
            n //= d
        d += 1
    if n > 1:
        f[n] = f.get(n, 0) + 1
    return f


def is_prime_int(n):
    if n < 2:
        return False
    d = 2
    while d * d <= n:
        if n % d == 0:
            return False
        d += 1
    return True


@lru_cache(maxsize=None)
def prime_above(p):
    """a prime element of norm p (p = 1 mod 3 prime), primary-normalised"""
    assert p % 3 == 1 and is_prime_int(p)
    R = int(math.isqrt(4 * p)) + 3
    for a in range(-R, R + 1):
        for b in range(-R, R + 1):
            if norm((a, b)) == p:
                return primary_associate((a, b))
    raise ValueError


def prime_elements(Nmax):
    """all primary prime elements (generator = 1 mod 3) with norm <= Nmax, norm != 3, excluding (2).
    Returns list sorted by norm."""
    out = []
    for p in range(7, Nmax + 1):
        if p % 3 == 1 and is_prime_int(p):
            pi = prime_above(p)
            out.append(pi)
            out.append(conj(pi))
    q = 5
    while q * q <= Nmax:
        if q % 3 == 2 and is_prime_int(q):
            out.append((-q, 0))        # -q = 1 mod 3
        q += 2
    out = sorted(set(out), key=lambda x: (norm(x), x))
    return out


def factor(s):
    """factor the element s into prime elements: list of (pi, e); pi primary when pi is prime to 6.
    pi for 2 is (2,0), for lambda is LAM."""
    n = norm(s)
    res = []
    rem = s
    for p, _ in sorted(factor_int(n).items()):
        cands = []
        if p == 3:
            cands = [LAM]
        elif p == 2:
            cands = [(2, 0)]
        elif p % 3 == 2:
            cands = [(-p, 0)]
        else:
            pi = prime_above(p)
            cands = [pi, conj(pi)]
        for pi in cands:
            e = 0
            while True:
                q = exact_div(rem, pi)
                if q is None:
                    break
                rem = q
                e += 1
            if e:
                res.append((pi, e))
    assert is_unit(rem), (s, rem)
    return res


def is_supported(s):
    if s == (0, 0):
        return False
    n = norm(s)
    return n % 2 == 1 and n % 3 != 0 and (s[0] % 2 or s[1] % 2) and n % 3 != 0


# ----------------------------------------------------------------------------------------------
# sextic symbol of a prime
# ----------------------------------------------------------------------------------------------
class PrimeSym:
    """table of (x/pi)_6 exponents j (value zeta6^j) for x mod pi; -1 for x = 0 mod pi"""

    def __init__(self, pi):
        self.pi = pi
        self.mod = get_mod(pi)
        N = self.mod.N
        self.N = N
        assert (N - 1) % 6 == 0, (pi, N)
        m = self.mod
        qs = list(factor_int(N - 1).keys())
        # find a generator
        rng = random.Random(12345 + N)
        while True:
            g = (rng.randrange(m.A), rng.randrange(m.C))
            g = m.reduce(g)
            if g == (0, 0):
                continue
            if all(m.powmod(g, (N - 1) // r) != m.reduce(ONE) for r in qs):
                break
        z0 = m.powmod(g, (N - 1) // 6)
        # j0 with zeta6^j0 == z0 mod pi
        j0 = None
        for j, u in enumerate(UNITS):
            if m.reduce(u) == z0:
                j0 = j
        assert j0 is not None
        table = np.full(N, -1, dtype=np.int8)
        cur = m.reduce(ONE)
        for t in range(N - 1):
            table[m.idx(cur)] = (j0 * t) % 6
            cur = m.reduce(mul(cur, g))
        self.table = table
        self.gen = g
        self.j0 = j0

    def sym(self, x):
        return int(self.table[self.mod.idx(x)])


@lru_cache(maxsize=None)
def prime_sym(pi):
    return PrimeSym(pi)


# ----------------------------------------------------------------------------------------------
# ideals (supported moduli): symbol exponents and Gauss sums
# ----------------------------------------------------------------------------------------------
class Modulus:
    """Supported modulus s (a specific generator), with all precomputed data."""

    def __init__(self, s):
        assert is_supported(s), s
        self.s = s
        self.N = norm(s)
        self.fact = factor(s)
        self.mod = get_mod(s)
        self._exps = None
        self._reps = None
        self.cs = conj(s)

    def chi(self, x):
        """exponent j in Z/6 of chi_s(x) = zeta6^j, or None if x not coprime to s"""
        tot = 0
        for pi, e in self.fact:
            j = prime_sym(pi).sym(x)
            if j < 0:
                return None
            tot += e * j
        return tot % 6

    def reps(self):
        if self._reps is None:
            self._reps = self.mod.rep_arrays()
        return self._reps

    def exps(self):
        """array of exponents of chi_s(d) over the canonical reps d (-1 for 0)"""
        if self._exps is None:
            X, Y = self.reps()
            tot = np.zeros(len(X), dtype=np.int64)
            bad = np.zeros(len(X), dtype=bool)
            for pi, e in self.fact:
                ps = prime_sym(pi)
                ix = ps.mod.idx_arrays(X, Y)
                j = ps.table[ix].astype(np.int64)
                bad |= (j < 0)
                tot += e * j
            tot %= 6
            tot[bad] = -1
            self._exps = tot
        return self._exps


@lru_cache(maxsize=None)
def get_modulus(s):
    return Modulus(s)


def psi_phase_direct(s, x):
    """psi_s(x) = exp(2 pi i Tr(x/(s sqrt(-3)))), computed from the definition with complex numbers"""
    w = complex(-0.5, math.sqrt(3) / 2)
    lam_tr = 1 + 2 * w
    z = to_complex(x) / (lam_tr * to_complex(s))
    return cmath.exp(2j * math.pi * (z + z.conjugate()).real)


def psi_phase(s, x):
    """psi_s(x) via the closed form  exp(2 pi i * [w-coordinate of x*conj(s)] / N(s))"""
    w1w2 = mul(x, conj(s))
    return cmath.exp(2j * math.pi * (w1w2[1] % norm(s)) / norm(s))


def gauss(s, h):
    """sexticGauss s h = sum_{d mod s} chi_s(d) psi_s(h d)   (double precision)"""
    S = get_modulus(s)
    X, Y = S.reps()
    h0, h1 = S.mod.reduce(h)          # g(s,h) only depends on h mod s (keeps the int64 arithmetic below safe)
    P0 = h0 * X - h1 * Y
    P1 = h0 * Y + h1 * X - h1 * Y
    c0, c1 = S.cs
    W1 = P0 * c1 + P1 * c0 - P1 * c1
    ph = np.exp(2j * np.pi * ((W1 % S.N) / S.N))
    ex = S.exps()
    m = ex >= 0
    zeta = np.exp(2j * np.pi * ex[m] / 6.0)
    return complex(np.sum(zeta * ph[m]))


def grow(s, h):
    return gauss(s, h) / math.sqrt(norm(s))


def zeta6(j):
    return cmath.exp(2j * math.pi * j / 6)


# ----------------------------------------------------------------------------------------------
# port of the Lean ray sign  QuadraticAllOddCRT.quadraticRaySign (residue a) (residue b)
# ----------------------------------------------------------------------------------------------
_EXP0 = {(0, 1), (0, 3), (1, 0), (1, 1), (3, 0), (3, 3)}
_EXP1 = {(1, 2), (1, 3), (2, 3)}


def _ray_exponent(r):
    if r in _EXP0:
        return 0
    if r in _EXP1:
        return 1
    return 3


def _coord_mul(x, y):
    return ((x[0] * y[0] - x[1] * y[1]) % 4, (x[0] * y[1] + x[1] * y[0] - x[1] * y[1]) % 4)


def _odd(r):
    return r[0] % 2 == 1 or r[1] % 2 == 1


def ray_sign(a, b):
    """quadraticRaySign (residue a) (residue b)  in {+1,-1,0}   (a,b elements of O)"""
    r = (a[0] % 4, a[1] % 4)
    s = (b[0] % 4, b[1] % 4)
    if not (_odd(r) and _odd(s)):
        return 0
    return 1 if _ray_exponent(_coord_mul(r, s)) == (_ray_exponent(r) + _ray_exponent(s)) % 4 else -1


# ----------------------------------------------------------------------------------------------
# convenience: exact symbol chi_b(a) exponent for general elements (b supported), and random generators
# ----------------------------------------------------------------------------------------------
def chi_exp(x, s):
    """exponent of chi_s(x) = idealRowHom x (span s); None if not coprime"""
    return get_modulus(s).chi(x)


def build_element(primes_exps):
    """product of prime powers, list of (pi, e)"""
    r = ONE
    for pi, e in primes_exps:
        r = mul(r, pw(pi, e))
    return r


def close(z, w, tol=1e-8, scale=1.0):
    return abs(z - w) <= tol * max(1.0, scale)
