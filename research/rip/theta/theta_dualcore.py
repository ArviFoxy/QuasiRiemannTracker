"""Helpers for the Poisson self-duality probes (theta_poisson.py, theta_dual.py): sextic symbols of the rows at
ARBITRARY elements a + b*omega, and the exact Poisson formula for Gaussian-weighted sums over primary elements.

Conventions (as in theta_core / ppcore):
  * a row z is a squarefree ideal; its generator is the element z_* = product of the primary generators of its prime
    ideals (so z_* is primary for an odd number of primes, and -z_* is primary for an even number);
  * g~(z) = F.Grow[z] is the normalised Gauss sum  g(z_*)/sqrt(N z) with g(z_*) = sum_{r mod z} chi_z(r) e(Tr(r/(sqrt(-3) z_*)));
  * chi_z(x) = prod_{pi | z} (x/pi)_6, a character of x modulo z that is 0 when x shares a prime with z;
  * w(n) = exp(-pi N(n)/L) is the 2D Gaussian weight; its Fourier transform is again Gaussian.

Exact Poisson formula (derived in the journal entry "Poisson self-duality at the balanced point", verified by theta_poisson.py)
for coprime rows z, z' (elements z_*, z'_*) and the sum over ALL primary n (n = 2 mod 3):

  G(z,z') = sum_{n = 2 (3)} exp(-pi N(n)/L) chi_z(n) conj chi_z'(n)
          = P * g~(z) conj g~(z') * Pair * T,
  P     = 2 L / (9 sqrt(3) sqrt(N(z) N(z'))),
  Pair  = chi_z(z') conj chi_z'(z) chi_z'(-1) chi_z(3) conj chi_z'(3),
  T     = sum_{h in Z[omega]} exp(-pi N(h)/Lt) phi_A(h) conj chi_z(h) chi_z'(h),   Lt = 27 N(z) N(z') / (4 L),
  phi_A(h) = exp(2 pi i * 2 A b(h) / 3),  h = a(h) + b(h) omega,  A = (z_* z'_*)^{-1} mod 3 (= +-1).

Reduction of T to sums over PRIMARY h (G~_prim(M) = sum_{h primary} exp(-pi N(h)/M) conj psi(h), psi = chi_z conj chi_z'),
according to the unit character psi|mu_6 of the pair:
  type a (psi(w) != 1):          T = U * G~_prim(Lt),            U = sum_u conj psi(u) exp(2 pi i A b(u)/3),  |U| = 3
  type b (psi(w) = 1, psi(-1) = -1): T = -3 sqrt(3) i A conj psi(pi3) G~_prim(Lt/3),   pi3 = sqrt(-3) = 1 + 2 omega
  type c (psi trivial on units):  T = -3 conj psi(pi3) G~_prim(Lt/3) + 6 conj psi(3) sum_{j>=0} conj psi(pi3)^j G~_prim(Lt/3^(j+2))
"""
import os, sys, math
import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import theta_core as tc      # noqa: E402

ZETA6 = np.exp(2j * np.pi * np.arange(6) / 6)
ZERO = 6                     # code meaning "symbol is 0"
PI3 = (1, 2)                 # sqrt(-3) = 1 + 2 omega


def elements_all(Nmax):
    """all (a, b) != (0, 0) with a^2 - a b + b^2 <= Nmax, as int64 arrays (a, b, N)."""
    M = int(math.isqrt((4 * int(Nmax)) // 3)) + 2
    r = np.arange(-M, M + 1, dtype=np.int64)
    a = np.repeat(r, len(r)); b = np.tile(r, len(r))
    N = a * a - a * b + b * b
    k = (N <= Nmax) & (N > 0)
    return a[k], b[k], N[k]


def elements_primary(Nmax):
    """primary elements (a = 2 mod 3, b = 0 mod 3) with N <= Nmax."""
    a, b, N = elements_all(Nmax)
    k = (a % 3 == 2) & (b % 3 == 0)
    return a[k], b[k], N[k]


def _inert_table(q):
    """codes (0..5, 100 at 0) of (a + b omega / q)_6 for a, b in F_q, as a (q, q) int8 table, vectorised."""
    a = np.repeat(np.arange(q, dtype=np.int64), q); b = np.tile(np.arange(q, dtype=np.int64), q)
    e = (q * q - 1) // 6
    r0 = np.ones_like(a); r1 = np.zeros_like(a)
    b0, b1 = a.copy(), b.copy()
    while e:
        if e & 1:
            r0, r1 = (r0 * b0 - r1 * b1) % q, (r0 * b1 + r1 * b0 - r1 * b1) % q
        b0, b1 = (b0 * b0 - b1 * b1) % q, (2 * b0 * b1 - b1 * b1) % q
        e >>= 1
    code = np.full(a.shape, -1, np.int8)
    code[(r0 == 1) & (r1 == 0)] = 0
    code[(r0 == 0) & (r1 == 1)] = 2
    code[(r0 == q - 1) & (r1 == q - 1)] = 4
    code[(r0 == q - 1) & (r1 == 0)] = 3
    code[(r0 == 0) & (r1 == q - 1)] = 5
    code[(r0 == 1) & (r1 == 1)] = 1
    zero = (a == 0) & (b == 0)
    assert (code[~zero] >= 0).all()
    code[zero] = 100
    return code.reshape(q, q)


class Symbols:
    """sextic symbol codes of rows against arbitrary elements; per-prime tables are cached."""

    def __init__(self, F):
        self.F = F
        self.ID = F.ID
        self.pc = F.pc
        self._tab = {}

    def table(self, pid):
        if pid in self._tab:
            return self._tab[pid]
        ID = self.ID
        if pid < ID.ns:
            p, r = ID.split_pr(np.array([pid]))
            p = int(p[0]); r = int(r[0])
            x = np.arange(p, dtype=np.int64)
            code = self.pc.sym_codes(np.array([p]), np.array([r]), x, np.zeros_like(x))[0]
            val = ('s', p, r, code)
        else:
            q = int(ID.inert_q[pid - ID.ns])
            val = ('i', q, 0, _inert_table(q))
        self._tab[pid] = val
        return val

    def prime_codes(self, pid, A, B):
        kind, p, r, code = self.table(pid)
        if kind == 's':
            return code[(A + B * r) % p]
        return code[A % p, B % p]

    def row_codes(self, zi, A, B):
        """int8 codes in 0..5 (6 = zero) of chi_z(a + b omega) for the row zi, arrays A, B."""
        acc = np.zeros(len(A), np.int16)
        for pid in self.F.rows['PID'][zi]:
            if pid < 0:
                continue
            acc += self.prime_codes(int(pid), A, B)
        out = (acc % 6).astype(np.int8)
        out[acc >= 100] = ZERO
        return out

    def row_value(self, zi, a, b):
        """chi_z(a + b omega) as a complex number for a single element."""
        c = self.row_codes(zi, np.array([a], np.int64), np.array([b], np.int64))[0]
        return 0j if c == ZERO else ZETA6[c]


def codes_to_chi(c):
    z = np.concatenate([ZETA6, [0]])
    return z[c]


def row_generators(F):
    """z_* = product of the primary generators of the prime ideals of each row, as (R, 2) int64."""
    zo = F.zo
    out = np.zeros((F.R, 2), np.int64)
    for zi in range(F.R):
        x = (1, 0)
        for pid in F.rows['PID'][zi]:
            if pid >= 0:
                g = F.generator(int(pid)); x = zo.mul(x, (g['a'], g['b']))
        out[zi] = x
    return out


def pair_factor(S, zi, zj, zs):
    """Pair = chi_z(z') conj chi_z'(z) chi_z'(-1) chi_z(3) conj chi_z'(3) for rows zi, zj (zs = row_generators)."""
    return (S.row_value(zi, *zs[zj]) * np.conj(S.row_value(zj, *zs[zi])) * S.row_value(zj, -1, 0)
            * S.row_value(zi, 3, 0) * np.conj(S.row_value(zj, 3, 0)))
