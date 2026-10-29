"""
Faithful toy model of the Arvi "initial energy" (Lean: InductionEnergy.lean:16 `energy`,
RetainedEnergy.lean:14 `positiveSlotRow`, HeckeHeight.lean:125 `rowTwistedSum`, HeckeSlots.lean:11 `rowSlot`).

Ring        O = Z[w], w = exp(2 pi i / 3)   (Eisenstein integers, class number 1, norm N(x+yw)=x^2-xy+y^2).
Family      rows z in O, weight Re Phi(N(z)/K), K = Z^M, kept iff NOT FixedInducingRow
            (initialKeep, DetectorEnergyInitialState.lean:21).
Row char    n -> eta(n) * (m^6 z / n)_6,  m = 2*lambda*unit  (fixedBadMask, SecondHeightFamily.lean:15):
            the sextic power-residue symbol, zero on primes above 2 and lambda = 1-w.
Plain poly  A_j(z) = sum_{ideals I} eta(I) (z/I)_6 N(I)^{it} W_j(N(I)/X_j)       (ALL ideals, W_j in [1/4, 9/4])
Slot poly   S_i(z) = sum_{P prime, ray-class pool} beta_i(P) eta(P) (z/P)_6 N(P)^{it}
            beta_i(P) = W(N(P)/D_i) (N(P)/D_i)^{-sigma + i v_i}    (annularWeight, PrimeAnnular.lean:15; W in [1,2])
Row         row_z = (X1 X2 prod D_i)^{-1/2} A_1 A_2 prod S_i
Energy      E = sum_{z kept} Re Phi(N(z)/K) |row_z|^2.

Choices made in the toy (all admissible instances of the Lean quantifiers):
  eta = (c0/.)_6 for a fixed element c0 (c0 = 1: trivial character), eta0 = trivial, rayModulus = (1), H = 1
  (so every prime is in the pool), Q = (72) so internalQ = (72):  a row is REMOVED iff the primitive character
  eta*(z/.)_6 has conductor dividing 72, i.e. iff c0*z = unit * 2^a * lambda^b * (sixth power) up to primes above 2, 3.
The symbol is the genuine one: (z/P)_6 = the unit u in mu_6(O) with u = z^{(N P-1)/6} mod P, mapped to C by omega -> e^{2 pi i/3}
(canonicalSextic, EisensteinEmbedding.lean:461, sexticChar = cubic^2 * quadratic, FiniteFourier.lean:801).
"""
from __future__ import annotations

import math
from dataclasses import dataclass, field

import numpy as np

TWO_PI_OVER_SQRT3 = 2.0 * math.pi / math.sqrt(3.0)  # lattice-point density of N(z) <= B is  (2 pi/sqrt3) B

# ----------------------------------------------------------------------------------------------
# small number theory helpers
# ----------------------------------------------------------------------------------------------


def sieve_primes(n: int) -> np.ndarray:
    s = np.ones(n + 1, dtype=bool)
    s[:2] = False
    for i in range(2, int(n ** 0.5) + 1):
        if s[i]:
            s[i * i :: i] = False
    return np.nonzero(s)[0]


def cube_root_of_unity_mod(p: int) -> int:
    """r with r^2 + r + 1 = 0 (mod p), p = 1 mod 3."""
    a = 2
    while True:
        r = pow(a, (p - 1) // 3, p)
        if r != 1:
            return r
        a += 1


def norm_eis(x, y):
    return x * x - x * y + y * y


def mul_eis(a, b):
    """(a0 + a1 w)(b0 + b1 w) with w^2 = -1 - w."""
    a0, a1 = a
    b0, b1 = b
    return (a0 * b0 - a1 * b1, a0 * b1 + a1 * b0 - a1 * b1)


# ----------------------------------------------------------------------------------------------
# prime ideals of O not above 2, 3
# ----------------------------------------------------------------------------------------------


@dataclass
class PrimeIdeals:
    norm: np.ndarray  # int64
    p: np.ndarray  # rational prime below
    kind: np.ndarray  # 0 split (norm p), 1 inert (norm p^2)
    r: np.ndarray  # root of r^2+r+1 mod p (split) or 0

    @property
    def n(self) -> int:
        return len(self.norm)


def build_prime_ideals(Nmax: int) -> PrimeIdeals:
    ps = sieve_primes(max(Nmax, 10))
    rows = []
    for p in ps.tolist():
        if p in (2, 3):
            continue
        if p % 3 == 1:
            if p <= Nmax:
                r = cube_root_of_unity_mod(p)
                rows.append((p, p, 0, r))
                rows.append((p, p, 0, (r * r) % p))
        else:  # p = 2 mod 3, inert, norm p^2
            if p * p <= Nmax:
                rows.append((p * p, p, 1, 0))
    rows.sort()
    arr = np.array(rows, dtype=np.int64).reshape(-1, 4)
    return PrimeIdeals(norm=arr[:, 0].copy(), p=arr[:, 1].copy(), kind=arr[:, 2].copy(), r=arr[:, 3].copy())


def _powmod_vec(t: np.ndarray, e: int, p: int) -> np.ndarray:
    res = np.ones_like(t)
    base = t % p
    while e:
        if e & 1:
            res = (res * base) % p
        e >>= 1
        if e:
            base = (base * base) % p
    return res


def _pow_fp2(a: np.ndarray, b: np.ndarray, e: int, p: int):
    """(a + b w)^e in F_p[w]/(w^2+w+1)."""
    ra = np.ones_like(a)
    rb = np.zeros_like(b)
    ba, bb = a % p, b % p
    while e:
        if e & 1:
            na = (ra * ba - rb * bb) % p
            nb = (ra * bb + rb * ba - rb * bb) % p
            ra, rb = na, nb
        e >>= 1
        if e:
            na = (ba * ba - bb * bb) % p
            nb = (2 * ba * bb - bb * bb) % p
            ba, bb = na, nb
    return ra, rb


ZETA6 = np.exp(2j * np.pi * np.arange(7) / 6.0)
ZETA6[6] = 0.0  # code 6 = "zero" (prime divides the row element)
MUL = np.full((7, 7), 6, dtype=np.uint8)
for _a in range(6):
    for _b in range(6):
        MUL[_a, _b] = (_a + _b) % 6


def prime_symbols(PI: PrimeIdeals, zx: np.ndarray, zy: np.ndarray) -> np.ndarray:
    """E[i, row] in {0..5} with (z/P_i)_6 = exp(2 pi i E/6), code 6 if P_i | z."""
    zx = np.asarray(zx, dtype=np.int64)
    zy = np.asarray(zy, dtype=np.int64)
    R = len(zx)
    E = np.empty((PI.n, R), dtype=np.uint8)
    pmax = int(PI.norm.max()) + 1 if PI.n else 2
    lut = np.full(pmax + 2, 6, dtype=np.uint8)
    for i in range(PI.n):
        p = int(PI.p[i])
        if PI.kind[i] == 0:
            r = int(PI.r[i])
            r2 = (r * r) % p
            t = (zx + zy * r) % p
            u = _powmod_vec(t, (p - 1) // 6, p)
            vals = (1, (-r2) % p, r, p - 1, r2, (-r) % p)  # k = 0..5  <->  e^{2 pi i k/6}
            for k, v in enumerate(vals):
                lut[v] = k
            e = lut[u]
            e[t == 0] = 6
            for v in vals:
                lut[v] = 6
            E[i] = e
        else:
            a = zx % p
            b = zy % p
            ra, rb = _pow_fp2(a, b, (p * p - 1) // 6, p)
            key = ra * p + rb
            vals = (1 * p + 0, 1 * p + 1, 0 * p + 1, (p - 1) * p + 0, (p - 1) * p + (p - 1), 0 * p + (p - 1))
            lut2 = np.full(p * p + 1, 6, dtype=np.uint8)
            for k, v in enumerate(vals):
                lut2[v] = k
            e = lut2[key]
            e[(a == 0) & (b == 0)] = 6
            E[i] = e
    return E


# ----------------------------------------------------------------------------------------------
# ideals coprime to 6, as products of the primes above
# ----------------------------------------------------------------------------------------------


@dataclass
class IdealList:
    norm: np.ndarray  # int64
    parent: np.ndarray  # int64, -1 for unit ideal
    last: np.ndarray  # index into PrimeIdeals of the last prime factor (-1 for unit ideal)

    @property
    def n(self) -> int:
        return len(self.norm)


def build_ideals(PI: PrimeIdeals, Nmax: int) -> IdealList:
    pn = PI.norm.tolist()
    npr = len(pn)
    norms = [1]
    parent = [-1]
    last = [-1]
    i = 0
    while i < len(norms):
        nI = norms[i]
        start = last[i] if last[i] >= 0 else 0
        lim = Nmax // nI
        j = start
        while j < npr and pn[j] <= lim:
            norms.append(nI * pn[j])
            parent.append(i)
            last.append(j)
            j += 1
        i += 1
    return IdealList(np.array(norms, dtype=np.int64), np.array(parent, dtype=np.int64), np.array(last, dtype=np.int64))


def ideal_exponents(IL: IdealList, Ep: np.ndarray) -> np.ndarray:
    n = IL.n
    R = Ep.shape[1]
    E = np.empty((n, R), dtype=np.uint8)
    E[0] = 0
    par = IL.parent.tolist()
    lst = IL.last.tolist()
    for i in range(1, n):
        E[i] = MUL[E[par[i]], Ep[lst[i]]]
    return E


# ----------------------------------------------------------------------------------------------
# weights / profiles (smooth, compactly supported)
# ----------------------------------------------------------------------------------------------


def _h(x):
    """C^infty step: 0 for x<=0, 1 for x>=1."""
    x = np.asarray(x, dtype=float)
    out = np.zeros_like(x)
    inside = (x > 0) & (x < 1)
    xi = x[inside]
    out[inside] = 1.0 / (1.0 + np.exp(np.clip(1.0 / xi - 1.0 / (1.0 - xi), -700.0, 700.0)))
    out[x >= 1] = 1.0
    return out


def make_profile(lo: float, hi: float, flat: float = 0.25):
    """Smooth profile supported in [lo, hi], equal to 1 on the middle; 'flat' = fraction used for each smooth edge."""
    def W(y):
        y = np.asarray(y, dtype=float)
        u = (y - lo) / (hi - lo)
        return _h(u / flat) * _h((1.0 - u) / flat)
    return W


def make_poly_profile(lo: float, hi: float, N: int):
    """W(y) = (4 (y-lo)(hi-y)/(hi-lo)^2)^N on [lo, hi]: only C^(N-1) (not Schwartz); used ONLY to display the functional-equation collapse."""
    def W(y):
        y = np.asarray(y, dtype=float)
        u = 4.0 * (y - lo) * (hi - y) / (hi - lo) ** 2
        return np.where((y > lo) & (y < hi), np.clip(u, 0.0, None) ** N, 0.0)
    return W


def phi_taper(x):
    """Phi(x)=1 on [0,1], smooth decay to 0 at 2 (Schwartz-admissible, support in (-inf,2], Re>=0)."""
    x = np.asarray(x, dtype=float)
    return 1.0 - _h(x - 1.0)


# ----------------------------------------------------------------------------------------------
# lattice sampling
# ----------------------------------------------------------------------------------------------


def lattice_rows_count(B: float) -> int:
    """number of z = x + y w with 0 < N(z) <= B."""
    xmax = int(2 * math.sqrt(B / 3.0)) + 2
    xs = np.arange(-xmax, xmax + 1, dtype=np.int64)
    disc = 4.0 * B - 3.0 * xs.astype(float) ** 2
    ok = disc >= 0
    sq = np.sqrt(np.where(ok, disc, 0.0))
    lo = np.ceil((xs - sq) / 2.0 - 1e-9)
    hi = np.floor((xs + sq) / 2.0 + 1e-9)
    cnt = np.where(ok, hi - lo + 1, 0).astype(np.int64)
    return int(cnt.sum()) - 1  # drop z = 0


def sample_rows(B: float, R: int, rng: np.random.Generator):
    """R i.i.d. uniform lattice points with 0 < N(z) <= B."""
    xmax = int(2 * math.sqrt(B / 3.0)) + 2
    xs = np.arange(-xmax, xmax + 1, dtype=np.int64)
    disc = 4.0 * B - 3.0 * xs.astype(float) ** 2
    ok = disc >= 0
    sq = np.sqrt(np.where(ok, disc, 0.0))
    lo = np.ceil((xs - sq) / 2.0 - 1e-9).astype(np.int64)
    hi = np.floor((xs + sq) / 2.0 + 1e-9).astype(np.int64)
    cnt = np.where(ok, hi - lo + 1, 0).astype(np.int64)
    tot = int(cnt.sum())
    out_x = np.empty(0, dtype=np.int64)
    out_y = np.empty(0, dtype=np.int64)
    cum = np.cumsum(cnt)
    while len(out_x) < R:
        idx = rng.integers(0, tot, size=2 * R)
        xi = np.searchsorted(cum, idx, side="right")
        within = idx - (cum[xi] - cnt[xi])
        x = xs[xi]
        y = lo[xi] + within
        keep = norm_eis(x, y) > 0
        out_x = np.concatenate([out_x, x[keep]])
        out_y = np.concatenate([out_y, y[keep]])
    return out_x[:R], out_y[:R]


# ----------------------------------------------------------------------------------------------
# keep predicate: which rows are removed by initialKeep (eta = (c0/.)_6, Q0 = (72))
# ----------------------------------------------------------------------------------------------

_SMALL_PRIMES = sieve_primes(40000).tolist()


def factor_int(n: int) -> dict:
    f = {}
    for p in _SMALL_PRIMES:
        if p * p > n:
            break
        while n % p == 0:
            f[p] = f.get(p, 0) + 1
            n //= p
    if n > 1:
        f[n] = f.get(n, 0) + 1
    return f


def _hensel_roots(p: int, r: int, k: int):
    """r_1..r_k with r_j a root of r^2+r+1 mod p^j lifting r."""
    out = [r % p]
    mod = p
    cur = r % p
    for _ in range(1, k):
        mod2 = mod * p
        f = (cur * cur + cur + 1)
        fp = (2 * cur + 1) % mod2
        cur = (cur - f * pow(fp, -1, mod2)) % mod2
        out.append(cur)
        mod = mod2
    return out


def prime_valuations(x: int, y: int) -> dict:
    """{(p, r_or_-1): v_P(z)} for prime ideals P not above 2,3 dividing z = x + y w."""
    N = norm_eis(x, y)
    vals = {}
    for p, e in factor_int(abs(N)).items():
        if p in (2, 3):
            continue
        if p % 3 == 1:
            r = cube_root_of_unity_mod(p)
            roots = _hensel_roots(p, r, e)
            roots2 = _hensel_roots(p, (r * r) % p, e)
            for rr_list, tag in ((roots, 0), (roots2, 1)):
                v = 0
                for k in range(1, e + 1):
                    if (x + y * rr_list[k - 1]) % (p ** k) == 0:
                        v = k
                    else:
                        break
                if v:
                    vals[(p, tag)] = v
        else:
            vx = 0
            xx = x
            while xx != 0 and xx % p == 0:
                xx //= p
                vx += 1
            vy = 0
            yy = y
            while yy != 0 and yy % p == 0:
                yy //= p
                vy += 1
            v = min(vx if x != 0 else 10 ** 9, vy if y != 0 else 10 ** 9)
            if v:
                vals[(p, -1)] = v
    return vals


def is_removed(x: int, y: int, c0=(1, 0)) -> bool:
    """True iff c0*z has all prime valuations (outside 2, lambda) divisible by 6, i.e. cond(eta*(z/.)_6) | 72."""
    zx, zy = mul_eis((x, y), c0)
    vals = prime_valuations(int(zx), int(zy))
    return all(v % 6 == 0 for v in vals.values())


# ----------------------------------------------------------------------------------------------
# conductor of the row character n -> (z/n)_6  (eta = 1), by local class field theory
# ----------------------------------------------------------------------------------------------
# K = Q(w): p = 2 is inert (N = 4, e = 1), lambda = w-1 has N = 3 and e(lambda/3) = 2.  The sextic character is quadratic x cubic, so the local conductor
# exponent is the max of the two parts:
#   at 2      quadratic part: 3 if v_2(z) odd; else 0 if z/2^v is a square mod 4 (i.e. = 1, w, w^2 mod 4), else 2.   cubic part: tame, 1 iff 3 does not divide v_2(z).
#   at lambda cubic part: 4 if 3 does not divide v_l(z); else, for the unit u = z/lambda^v with level t = max{j<=4: u = cube mod lambda^j}: 0 if t>=3, else 4-t.
#             quadratic part: tame, 1 iff v_l(z) odd.
#   at P not above 6 with 6 not dividing v_P(z): exponent 1.
# Checked against number-field discriminants in selftest.py (z = 2, 3, -1, w).
_SQ4 = {(1, 0), (0, 1), (3, 3)}  # squares in (O/4)^*: mu_3 = {1, w, w^2 = -1-w}


def _v3_norm(wx: int, wy: int) -> int:
    n = norm_eis(wx, wy)
    if n == 0:
        return 99
    v = 0
    while n % 3 == 0:
        n //= 3
        v += 1
    return v  # = v_lambda(w)


def _build_cube_level():
    cubes = [mul_eis(mul_eis((cx, cy), (cx, cy)), (cx, cy)) for cx in range(9) for cy in range(9)]
    tab = {}
    for ux in range(9):
        for uy in range(9):
            t = 0
            for c3 in cubes:
                t = max(t, min(4, _v3_norm(ux - c3[0], uy - c3[1])))
            tab[(ux, uy)] = t
    return tab


_CUBE_LEVEL = _build_cube_level()


def cond_exponents_2_lambda(x: int, y: int):
    """(f2, flam): conductor exponents of the primes 2 and lambda for n -> (z/n)_6, z = x + y w != 0."""
    zx, zy, v2 = x, y, 0
    while zx % 2 == 0 and zy % 2 == 0:
        zx //= 2
        zy //= 2
        v2 += 1
    q2 = 3 if v2 % 2 else (0 if (zx % 4, zy % 4) in _SQ4 else 2)
    f2 = max(q2, 1 if v2 % 3 else 0)
    ux, uy, vl = x, y, 0
    while True:
        px, py = mul_eis((ux, uy), (-2, -1))  # times conj(lambda) = -2 - w
        if px % 3 == 0 and py % 3 == 0:
            ux, uy = px // 3, py // 3
            vl += 1
        else:
            break
    if vl % 3:
        cl = 4
    else:
        t = _CUBE_LEVEL[(ux % 9, uy % 9)]
        cl = 0 if t >= 3 else 4 - t
    return f2, max(vl % 2, cl)


def q6_norm(x: int, y: int) -> float:
    """norm of the part of the conductor at primes not above 2, 3: prod N(P) over P with 6 not dividing v_P(z)."""
    q = 1.0
    for (p, tag), v in prime_valuations(x, y).items():
        if v % 6:
            q *= p if tag in (0, 1) else float(p * p)
    return q


def cond_norm(x: int, y: int) -> float:
    """norm of the full conductor of n -> (z/n)_6 (eta = 1)."""
    f2, fl = cond_exponents_2_lambda(x, y)
    return q6_norm(x, y) * 4.0 ** f2 * 3.0 ** fl


# ----------------------------------------------------------------------------------------------
# context: rows + prime/ideal symbol tables
# ----------------------------------------------------------------------------------------------


@dataclass
class Context:
    Z: float
    K: float
    rows_x: np.ndarray
    rows_y: np.ndarray
    phi: np.ndarray  # Phi(N(z)/K) for each row
    keep: np.ndarray  # bool
    PI: PrimeIdeals
    IL: IdealList
    Ep: np.ndarray
    E: np.ndarray
    random_model: bool = False

    @property
    def Nmax(self) -> int:
        return int(self.IL.norm.max())


def build_context(Z: float, Nmax: int, rows_x, rows_y, K=None, c0=(1, 0), random_model=False,
                  rng=None, PI=None, IL=None, keep=None, phi_fn=phi_taper) -> Context:
    K = Z if K is None else K
    rows_x = np.asarray(rows_x, dtype=np.int64)
    rows_y = np.asarray(rows_y, dtype=np.int64)
    Nm = norm_eis(rows_x, rows_y)
    phi = phi_fn(Nm / K)
    if PI is None:
        PI = build_prime_ideals(Nmax)
    if IL is None:
        IL = build_ideals(PI, Nmax)
    if keep is None:
        keep = np.array([not is_removed(int(a), int(b), c0) for a, b in zip(rows_x, rows_y)])
    # row element entering the character:  c0 * z
    if c0 == (1, 0):
        ex, ey = rows_x, rows_y
    else:
        pr = [mul_eis((int(a), int(b)), c0) for a, b in zip(rows_x, rows_y)]
        ex = np.array([q[0] for q in pr], dtype=np.int64)
        ey = np.array([q[1] for q in pr], dtype=np.int64)
    if random_model:
        rng = rng or np.random.default_rng(1)
        Ep = rng.integers(0, 6, size=(PI.n, len(rows_x)), dtype=np.uint8)
        # a prime divides a random element with probability 1/N(P)
        zero = rng.random((PI.n, len(rows_x))) < (1.0 / PI.norm)[:, None]
        Ep[zero] = 6
    else:
        Ep = prime_symbols(PI, ex, ey)
    E = ideal_exponents(IL, Ep)
    return Context(Z=Z, K=K, rows_x=rows_x, rows_y=rows_y, phi=phi, keep=keep, PI=PI, IL=IL, Ep=Ep, E=E,
                   random_model=random_model)


# ----------------------------------------------------------------------------------------------
# polynomials
# ----------------------------------------------------------------------------------------------


def _chunked_sum(E: np.ndarray, idx: np.ndarray, w: np.ndarray, chunk: int = 4000) -> np.ndarray:
    R = E.shape[1]
    acc = np.zeros(R, dtype=np.complex128)
    for s in range(0, len(idx), chunk):
        sl = idx[s : s + chunk]
        vals = ZETA6[E[sl]]  # (c, R)
        acc += w[s : s + chunk] @ vals
    return acc


def plain_sum(ctx: Context, X: float, W, t: float = 0.0, lo: float = 0.25, hi: float = 2.25) -> np.ndarray:
    """A(z) = sum_I (z/I)_6 N(I)^{it} W(N(I)/X) over all ideals I (coprime to 6)."""
    nrm = ctx.IL.norm.astype(float)
    sel = np.nonzero((nrm >= lo * X) & (nrm <= hi * X))[0]
    if len(sel) == 0:
        return np.zeros(len(ctx.rows_x), dtype=np.complex128)
    w = W(nrm[sel] / X) * np.exp(1j * t * np.log(nrm[sel]))
    return _chunked_sum(ctx.E, sel, w.astype(np.complex128))


def slot_sum(ctx: Context, D: float, W, sigma: float = 0.66, v: float = 0.0, t: float = 0.0,
             lo: float = 1.0, hi: float = 2.0, pool_mask: np.ndarray | None = None) -> np.ndarray:
    """S(z) = sum_P W(N(P)/D) (N(P)/D)^{-sigma + i v} N(P)^{it} (z/P)_6  over prime ideals P."""
    nrm = ctx.PI.norm.astype(float)
    sel_mask = (nrm >= lo * D) & (nrm <= hi * D)
    if pool_mask is not None:
        sel_mask &= pool_mask
    sel = np.nonzero(sel_mask)[0]
    if len(sel) == 0:
        return np.zeros(len(ctx.rows_x), dtype=np.complex128)
    u = nrm[sel] / D
    w = W(u) * u ** (-sigma + 1j * v) * np.exp(1j * t * np.log(nrm[sel]))
    return _chunked_sum(ctx.Ep, sel, w.astype(np.complex128))


@dataclass
class Data:
    """one admissible choice of the adversary's data (the Lean quantifier block)"""
    m1: float
    m2: float
    slots: tuple = ()  # tuple of w_i
    t: float = 0.0
    v: tuple = ()  # per-slot frequency (default 0)
    flat_plain: float = 0.25
    flat_slot: float = 0.25
    x_scale: tuple = (1.0, 1.0)  # X_j = x_scale_j * Z^{m_j}
    sigma: float = 0.66


def row_energies(ctx: Context, d: Data, return_parts=False):
    Z = ctx.Z
    X1 = d.x_scale[0] * Z ** d.m1
    X2 = d.x_scale[1] * Z ** d.m2
    W1 = make_profile(0.25, 2.25, d.flat_plain)
    W2 = make_profile(0.25, 2.25, d.flat_plain * 0.8 + 0.05)  # a different profile for profile 1
    A1 = plain_sum(ctx, X1, W1, d.t)
    A2 = plain_sum(ctx, X2, W2, d.t)
    Ws = make_profile(1.0, 2.0, d.flat_slot)
    e = np.abs(A1) ** 2 * np.abs(A2) ** 2 / (X1 * X2)
    parts = {"A1": np.abs(A1) ** 2 / X1, "A2": np.abs(A2) ** 2 / X2}
    for i, w in enumerate(d.slots):
        D = Z ** w
        vi = d.v[i] if i < len(d.v) else 0.0
        S = slot_sum(ctx, D, Ws, d.sigma, vi, d.t)
        e = e * np.abs(S) ** 2 / D
        parts[f"S{i}"] = np.abs(S) ** 2 / D
    if return_parts:
        return e, parts
    return e


def energy_estimate(ctx: Context, e_rows: np.ndarray, N_total_pts: float, include_removed=False):
    """E_hat = (#points) * mean_over_uniform_sample( Phi * keep * row_energy ); also the weighted mean row energy."""
    mask = np.ones_like(ctx.keep) if include_removed else ctx.keep
    w = ctx.phi * mask
    num = float(np.sum(w * e_rows))
    den = float(np.sum(w))
    R = len(e_rows)
    mean_w = den / R
    wmean = num / den if den > 0 else 0.0
    # standard error of the ratio estimator (delta method)
    if den > 0 and R > 2:
        resid = w * (e_rows - wmean)
        se_w = math.sqrt(float(np.sum(resid ** 2))) / den
    else:
        se_w = float("nan")
    Keff = N_total_pts * mean_w
    live = mask & (ctx.phi > 0)
    return {"E": Keff * wmean, "Keff": Keff, "mean_row": wmean, "se_mean_row": se_w,
            "max_row": float(np.max(e_rows[live])) if np.any(live) else 0.0}
