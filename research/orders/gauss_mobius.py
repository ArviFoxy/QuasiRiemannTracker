"""Which Gauss-sum sums have a theta main term?  Order 3 and 6 over Z[omega], order 4 over Z[i].

Background (research/LOG.md, "Why order 6"; journal 2026-10-31, "One theta for n = 3, two thetas for n = 6").
The baseline's low side needs the Mobius-weighted Gauss sums of the row characters to be coefficients of an
automorphic object with an explicit reflection.  For order 6, Hasse-Davenport turns mu(n)*conj(g6(n)) into a cubic
Gauss sum times unit factors; cubic Gauss sums are the coefficients of Kubota-Patterson's cubic theta, whose
partial sums have the main term X^{5/6} (Heath-Brown-Patterson).  For order 4 the Mobius sign survives as
mu(n)*conj(g4(n)), and no explicit quartic identity is known.

The script builds the n-th order Gauss sums g(c) of all primary squarefree ideals c of norm <= X (split primes and
inert primes, ramified prime excluded) by twisted multiplicativity g(c1 c2) = (c1/c2)(c2/c1) g(c1) g(c2), with the
additive character e(Tr(x/(delta c))), delta = sqrt(-3) for Z[omega] and 2 for Z[i], and normalizes g~ = g/sqrt(N c).
For several weights w(c) it prints the per-class partial sums S(X) = sum_{N c <= X, c in class} w(c) on a grid of X,
and the log-log slope of their RMS over classes.  Square-root cancellation gives slope 1/2; a theta main term gives
1 - 1/n_eff (5/6 cubic, 3/4 quartic, 2/3 sextic).

usage: python3 -I gauss_mobius.py field X        (field: eis | gauss)
"""
import sys, math, time
import numpy as np

FIELD = sys.argv[1]
XMAX = int(sys.argv[2])
t0 = time.time()
if FIELD == 'eis':
    ORD = 6                                    # sextic symbol; the cubic one is its square
else:
    ORD = 4                                    # quartic symbol


# ------------------------------------------------------------------------------------------------- ring arithmetic
def mul(x, y):
    a, b = x; c, d = y
    if FIELD == 'eis':                         # omega^2 = -1 - omega
        return (a * c - b * d, a * d + b * c - b * d)
    return (a * c - b * d, a * d + b * c)      # i^2 = -1


def norm(x):
    a, b = x
    return a * a - a * b + b * b if FIELD == 'eis' else a * a + b * b


UNITS = ([(1, 0), (0, 1), (-1, -1), (-1, 0), (0, -1), (1, 1)] if FIELD == 'eis'
         else [(1, 0), (0, 1), (-1, 0), (0, -1)])


def primary(x):
    """the associate of x that is primary: = 2 mod 3 (Z[omega], the baseline's convention) or = 1 mod 2+2i (Z[i])."""
    for u in UNITS:
        a, b = mul(x, u)
        if FIELD == 'eis':
            if a % 3 == 2 and b % 3 == 0:
                return (a, b)
        else:
            if b % 2 == 0 and (a + b) % 4 == 1:
                return (a, b)
    raise ValueError(x)


# ------------------------------------------------------------------------------------------------- primes
def sieve(n):
    s = np.ones(n + 1, bool); s[:2] = False
    for i in range(2, int(n ** 0.5) + 1):
        if s[i]:
            s[i * i::i] = False
    return np.nonzero(s)[0]


def sqrt_mod(n, p):
    """Tonelli-Shanks."""
    n %= p
    if p % 4 == 3:
        return pow(n, (p + 1) // 4, p)
    q, s = p - 1, 0
    while q % 2 == 0:
        q //= 2; s += 1
    z = 2
    while pow(z, (p - 1) // 2, p) != p - 1:
        z += 1
    m, c, t, r = s, pow(z, q, p), pow(n, q, p), pow(n, (q + 1) // 2, p)
    while t != 1:
        i, tt = 0, t
        while tt != 1:
            tt = tt * tt % p; i += 1
        b = pow(c, 1 << (m - i - 1), p)
        m, c, t, r = i, b * b % p, t * b * b % p, r * b % p
    return r


def factor_small(n):
    fs, d = [], 2
    while d * d <= n:
        if n % d == 0:
            fs.append(d)
            while n % d == 0:
                n //= d
        d += 1
    if n > 1:
        fs.append(n)
    return fs


def primitive_root(p):
    fs = factor_small(p - 1)
    g = 2
    while any(pow(g, (p - 1) // f, p) == 1 for f in fs):
        g += 1
    return g


def reduce_basis(r, p):
    """shortest vector of the lattice {x + y t : x + y r = 0 mod p} (t = omega or i) under the norm form."""
    def nf(v):
        return norm(v)

    def ip(u, v):                              # bilinear form with nf(v) = ip(v, v)
        if FIELD == 'eis':
            return u[0] * v[0] - (u[0] * v[1] + u[1] * v[0]) / 2 + u[1] * v[1]
        return u[0] * v[0] + u[1] * v[1]
    u, v = (p, 0), (-r % p, 1)
    if nf(u) < nf(v):
        u, v = v, u
    while True:
        mu = round(ip(u, v) / nf(v))
        u = (u[0] - mu * v[0], u[1] - mu * v[1])
        if nf(u) >= nf(v):
            break
        u, v = v, u
    assert nf(v) == p, (p, r, v)
    return v


class Split:
    def __init__(self, p, r):
        self.p, self.r, self.N = p, r, p
        self.gen = primary(reduce_basis(r, p))
        a, b = self.gen
        assert (a + b * r) % p == 0
        zeta = (1 + r) % p if FIELD == 'eis' else r          # image of zeta_6 = 1 + omega, or of i
        self.ztab = {pow(zeta, k, p): k for k in range(ORD)}
        self.e = (p - 1) // ORD

    def sym(self, x):
        """(x / P)_ORD as an exponent k, x^((p-1)/ORD) = zeta^k mod P; None if P | x."""
        t = (x[0] + x[1] * self.r) % self.p
        if t == 0:
            return None
        return self.ztab[pow(t, self.e, self.p)]

    def gauss(self):
        p = self.p
        g = primitive_root(p)
        k0 = self.ztab[pow(g, self.e, p)]
        B = int(math.isqrt(p - 1)) + 1
        baby = np.empty(B, np.int64); x = 1
        for i in range(B):
            baby[i] = x; x = x * g % p
        gB = x
        giant = np.empty((p - 1) // B + 1, np.int64); x = 1
        for j in range(len(giant)):
            giant[j] = x; x = x * gB % p
        xs = ((giant[:, None] * baby[None, :]) % p).ravel()[:p - 1]
        m = np.arange(p - 1, dtype=np.int64)
        a, b = self.gen
        c = (-b) % p if FIELD == 'eis' else a % p           # e(Tr(x/(delta P))) = e(c x / p) for x in Z
        W = np.exp(2j * np.pi * np.arange(p) / p)
        add = W[(c * xs) % p]
        z = np.exp(2j * np.pi * np.arange(ORD) / ORD)
        out = {ORD: complex(np.sum(z[(k0 * m) % ORD] * add)) / math.sqrt(p)}
        if FIELD == 'eis':
            out[3] = complex(np.sum(z[(2 * k0 * m) % ORD] * add)) / math.sqrt(p)
        return out


class Inert:
    """the inert prime q, residue field F_q[t] with t = omega (t^2 = -1 - t) or t = i (t^2 = -1)."""
    def __init__(self, q):
        self.q, self.N = q, q * q
        self.gen = primary((q, 0))
        self.e = (q * q - 1) // ORD
        zeta = (1, 1) if FIELD == 'eis' else (0, 1)
        self.ztab = {}
        z = (1, 0)
        for k in range(ORD):
            self.ztab[z] = k
            z = self.fmul(z, zeta)

    def fmul(self, x, y):
        q = self.q
        a, b = mul(x, y)
        return (a % q, b % q)

    def fpow(self, x, n):
        r = (1, 0)
        while n:
            if n & 1:
                r = self.fmul(r, x)
            x = self.fmul(x, x); n >>= 1
        return r

    def sym(self, x):
        t = (x[0] % self.q, x[1] % self.q)
        if t == (0, 0):
            return None
        return self.ztab[self.fpow(t, self.e)]

    def gauss(self):
        q = self.q
        fs = factor_small(q * q - 1)
        gen = None
        for a in range(q):
            for b in range(1, q):
                if all(self.fpow((a, b), (q * q - 1) // f) != (1, 0) for f in fs):
                    gen = (a, b); break
            if gen:
                break
        k0 = self.ztab[self.fpow(gen, self.e)]
        n = q * q - 1
        U = np.empty(n, np.int64); V = np.empty(n, np.int64)
        x = (1, 0)
        for m in range(n):
            U[m], V[m] = x
            x = self.fmul(x, gen)
        m = np.arange(n, dtype=np.int64)
        add = np.exp(2j * np.pi * (V if FIELD == 'eis' else U) / q)   # e(v/q) or e(u/q)
        z = np.exp(2j * np.pi * np.arange(ORD) / ORD)
        out = {ORD: complex(np.sum(z[(k0 * m) % ORD] * add)) / q}
        if FIELD == 'eis':
            out[3] = complex(np.sum(z[(2 * k0 * m) % ORD] * add)) / q
        return out


primes = []
P = sieve(XMAX)
for p in P:
    p = int(p)
    if FIELD == 'eis':
        if p in (2, 3):                        # ideals coprime to 6
            continue
        if p % 3 == 1:
            s = sqrt_mod(-3, p)
            r1 = (-1 + s) * pow(2, -1, p) % p
            for r in (r1, (-1 - r1) % p):
                primes.append(Split(p, r))
        elif p * p <= XMAX:
            primes.append(Inert(p))
    else:
        if p == 2:
            continue
        if p % 4 == 1:
            r1 = sqrt_mod(-1, p)
            for r in (r1, p - r1):
                primes.append(Split(p, r))
        elif p * p <= XMAX:
            primes.append(Inert(p))
primes.sort(key=lambda P_: P_.N)
print('%s, order %d: %d prime ideals of norm <= %d   (%.0fs)' % (FIELD, ORD, len(primes), XMAX, time.time() - t0),
      flush=True)
G = []
for i, Pr in enumerate(primes):
    G.append(Pr.gauss())
ords = [ORD] + ([3] if FIELD == 'eis' else [])
mods = [abs(G[i][o]) for i in range(len(primes)) for o in ords]
print('  prime Gauss sums: |g~| in [%.6f, %.6f]   (%.0fs)' % (min(mods), max(mods), time.time() - t0), flush=True)

# ------------------------------------------------------------------------------------------------- products
recN, recC, recMu, recA = [], [], [], []
recG = {o: [] for o in ords}
zt = np.exp(2j * np.pi * np.arange(ORD) / ORD)
stack = [(-1, 1, (1, 0), (), 1, {o: 1 + 0j for o in ords})]
while stack:
    last, Nn, gen, fac, mu, gs = stack.pop()
    if last >= 0:
        recN.append(Nn); recMu.append(mu)
        a, b = gen
        z = complex(a, 0) + b * (complex(-0.5, math.sqrt(3) / 2) if FIELD == 'eis' else 1j)
        recA.append(z / abs(z))
        recC.append((a % 9, b % 9, a % 4, b % 4) if FIELD == 'eis' else (a % 16, b % 16))
        for o in ords:
            recG[o].append(gs[o])
    for j in range(last + 1, len(primes)):
        Pj = primes[j]
        if Nn * Pj.N > XMAX:
            break
        k = Pj.sym(gen) if fac else 0
        if k is None:
            continue
        for i in fac:
            k += primes[i].sym(Pj.gen)
        ng = {}
        for o in ords:
            tw = zt[k % ORD] if o == ORD else zt[(2 * k) % ORD]
            ng[o] = gs[o] * G[j][o] * tw
        prod = mul(gen, Pj.gen)
        newgen = primary(prod)
        if newgen != prod:                     # newgen = u * prod: g changes by conj (u / c)
            u = next(v for v in UNITS if mul(prod, v) == newgen)
            ku = sum(primes[i].sym(u) for i in fac + (j,))
            for o in ords:
                ng[o] = ng[o] * (np.conj(zt[ku % ORD]) if o == ORD else np.conj(zt[(2 * ku) % ORD]))
        stack.append((j, Nn * Pj.N, newgen, fac + (j,), -mu, ng))
recN = np.array(recN); recMu = np.array(recMu); recA = np.array(recA)
cls_keys = {c: i for i, c in enumerate(sorted(set(recC)))}
recCl = np.array([cls_keys[c] for c in recC])
for o in ords:
    recG[o] = np.array(recG[o])
print('  %d squarefree primary ideals, %d classes   (%.0fs)' % (len(recN), len(cls_keys), time.time() - t0),
      flush=True)

# ------------------------------------------------------------------------------------------------- brute-force check
# twisted multiplicativity against the definition, on products of two and three split primes (squarefree norms,
# so O/c = Z/N(c) and the integers 0..N(c)-1 are a complete residue system)
def gauss_brute(fs):
    gen = (1, 0)
    for Pr in fs:
        gen = mul(gen, Pr.gen)
    Nn = norm(gen)
    a, b = gen
    c = (-b) % Nn if FIELD == 'eis' else a % Nn
    tot = 0j
    for x in range(1, Nn):
        ks = [Pr.sym((x, 0)) for Pr in fs]
        if any(k is None for k in ks):
            continue
        tot += zt[sum(ks) % ORD] * np.exp(2j * np.pi * (c * x % Nn) / Nn)
    return tot / math.sqrt(Nn)


def gauss_twisted(fs):
    g = 1 + 0j; gen = (1, 0); k = 0
    for j, Pr in enumerate(fs):
        if j:
            k += Pr.sym(gen)
            for Q in fs[:j]:
                k += Q.sym(Pr.gen)
        g *= G[primes.index(Pr)][ORD]
        gen = mul(gen, Pr.gen)
    return g * zt[k % ORD]


sp = [Pr for Pr in primes if isinstance(Pr, Split)]
worst = 0.0
for combo in ([sp[0], sp[2]], [sp[1], sp[4]], [sp[0], sp[3], sp[6]], [sp[2], sp[5]]):
    if len({Pr.p for Pr in combo}) < len(combo):
        continue
    gb, gt = gauss_brute(combo), gauss_twisted(combo)
    worst = max(worst, abs(gb - gt))
print('  twisted multiplicativity against the definition (squarefree norms): max |diff| = %.2e' % worst, flush=True)

# ------------------------------------------------------------------------------------------------- growth
mu = recMu.astype(float)
al = recA
weights = {}
if FIELD == 'eis':
    g6, g3 = recG[6], recG[3]
    weights = {'g3 (cubic theta)': g3, 'g6': g6, 'mu g6': mu * g6, 'mu conj g6': mu * np.conj(g6),
               'mu conj g6 * a': mu * np.conj(g6) * al, 'mu conj g6 * conj a': mu * np.conj(g6) * np.conj(al),
               'mu g3': mu * g3, 'random phases': np.exp(2j * np.pi * np.random.default_rng(83).random(len(g3)))}
    # the order-6 identity mu conj g6 = g3 conj(a) conj(G) (Lean: localGamma_one_two_full_signal at primes):
    # the ratio rho = mu conj g6 * a / g3 should depend on the class of c only
    rho = mu * np.conj(g6) * al / g3
    for name, sel in (('primes', recMu < 0), ('all', np.ones(len(rho), bool))):
        cl_ = recCl[sel]; r_ = rho[sel]
        m = np.zeros(len(cls_keys), complex); np.add.at(m, cl_, r_)
        c = np.bincount(cl_, minlength=len(cls_keys))
        within = np.abs(r_ - (m / np.maximum(c, 1))[cl_]) ** 2
        print('  identity check on %-6s: |rho| = 1 (%.2e); mean within-class |rho - class mean|^2 = %.4f '
              '(2 for unrelated phases); classes used %d' % (name, np.max(np.abs(np.abs(r_) - 1)), within.mean(),
                                                             int(np.sum(c > 0))), flush=True)
else:
    g4 = recG[4]
    weights = {'g4': g4, 'mu g4': mu * g4, 'mu conj g4': mu * np.conj(g4)}
    for kk in (1, 2, 3):
        weights['mu conj g4 * a^%d' % kk] = mu * np.conj(g4) * al ** kk
        weights['mu g4 * a^%d' % kk] = mu * g4 * al ** kk
    weights['g4^2 * conj a'] = g4 ** 2 * np.conj(al)
    weights['random phases'] = np.exp(2j * np.pi * np.random.default_rng(83).random(len(g4)))
    # the quartic analogue: g4(p)^2 = J(chi, chi) g2(p) with J ~ p and g2 trivial, so mu conj g4 * a / g4 should
    # depend on the class only (the Mobius sign is absorbed into the quartic Gauss sum itself)
    rho = mu * np.conj(g4) * al / g4
    for name, sel in (('primes', recMu < 0), ('all', np.ones(len(rho), bool))):
        cl_ = recCl[sel]; r_ = rho[sel]
        m = np.zeros(len(cls_keys), complex); np.add.at(m, cl_, r_)
        c = np.bincount(cl_, minlength=len(cls_keys))
        within = np.abs(r_ - (m / np.maximum(c, 1))[cl_]) ** 2
        print('  identity check on %-6s: |rho| = 1 (%.2e); mean within-class |rho - class mean|^2 = %.4f '
              '(2 for unrelated phases); classes used %d' % (name, np.max(np.abs(np.abs(r_) - 1)), within.mean(),
                                                             int(np.sum(c > 0))), flush=True)
def class_constant(name, rho):
    """is rho (unimodular) a function of the class only?  prints the mean within-class squared deviation."""
    for nm, sel in (('primes', recMu < 0), ('all', np.ones(len(rho), bool))):
        cl_ = recCl[sel]; r_ = rho[sel]
        m = np.zeros(len(cls_keys), complex); np.add.at(m, cl_, r_)
        c = np.bincount(cl_, minlength=len(cls_keys))
        within = np.abs(r_ - (m / np.maximum(c, 1))[cl_]) ** 2
        print('  %-34s on %-6s: within-class |rho - mean|^2 = %.4f (2 for unrelated phases)'
              % (name, nm, within.mean()), flush=True)


print('  signal identities (the baseline uses gamma1 = gamma2^2 G and gamma2^3 = mu alpha):')
if FIELD == 'eis':
    class_constant('g3^3 / (mu a)', recG[3] ** 3 / (mu * al))
    class_constant('g6 / g3^2', recG[6] / recG[3] ** 2)
else:
    class_constant('g4^2 / (mu a)', recG[4] ** 2 / (mu * al))
    class_constant('g4^4 / a^2', recG[4] ** 4 / al ** 2)
o = np.argsort(recN)
Ns = recN[o]; cl = recCl[o]
ncl = len(cls_keys)
grid = np.unique(np.round(np.geomspace(XMAX / 300, XMAX, 25)).astype(int))
print('  counts: %d terms up to X (%.3f X)' % (len(Ns), len(Ns) / XMAX))
print('  %-12s  %s   slope(RMS)  slope(max)  max_c |S_c(X)|/sqrt(#terms in c)' % ('weight', 'RMS_c |S_c| at X/100, X/10, X'))
for name, w in weights.items():
    w = w[o]
    rms, mx = [], []
    for X in grid:
        k = np.searchsorted(Ns, X, side='right')
        S = np.zeros(ncl, complex); np.add.at(S, cl[:k], w[:k])
        cnt = np.bincount(cl[:k], minlength=ncl)
        rms.append(math.sqrt(np.mean(np.abs(S) ** 2))); mx.append(np.max(np.abs(S)))
    rms, mx = np.array(rms), np.array(mx)
    sel = grid >= XMAX / 30
    s1 = np.polyfit(np.log(grid[sel]), np.log(rms[sel]), 1)[0]
    s2 = np.polyfit(np.log(grid[sel]), np.log(mx[sel]), 1)[0]
    k = len(Ns)
    S = np.zeros(ncl, complex); np.add.at(S, cl, w)
    cnt = np.bincount(cl, minlength=ncl)
    ratio = np.max(np.abs(S) / np.sqrt(np.maximum(cnt, 1)))
    i100 = np.searchsorted(grid, XMAX / 100); i10 = np.searchsorted(grid, XMAX / 10)
    print('  %-12s  %9.1f %9.1f %9.1f   %6.3f      %6.3f      %7.2f'
          % (name, rms[min(i100, len(grid) - 1)], rms[min(i10, len(grid) - 1)], rms[-1], s1, s2, ratio), flush=True)
print('done in %.0fs' % (time.time() - t0))
