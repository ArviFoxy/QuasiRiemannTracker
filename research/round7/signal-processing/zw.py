# Core arithmetic over Z[omega] for the P1 experiments (fresh7c).
# Model (as in research/atom1/toy): primary elements a + b*omega with a = 2 mod 3, b = 0 mod 3,
# gcd(a,b) = 1, norm squarefree with all prime factors p = 1 mod 3 ("split-squarefree").
# For such n, O/n = Z/N(n), so residues are rational integers 0..N(n)-1.
import numpy as np, math

W = np.exp(2j * np.pi / 3)

def sieve(m):
    s = np.ones(m + 1, bool); s[:2] = False
    for i in range(2, int(m ** 0.5) + 1):
        if s[i]: s[i * i::i] = False
    return s

def powmod(x, e, p):
    """vectorized x^e mod p for int64 arrays, p < 2^31"""
    x = np.asarray(x, dtype=np.int64) % p
    res = np.ones_like(x)
    while e > 0:
        if e & 1: res = (res * x) % p
        x = (x * x) % p
        e >>= 1
    return res

class Arith:
    def __init__(self, LIM):
        self.LIM = LIM
        self.isp = sieve(LIM)
        spf = np.zeros(LIM + 1, dtype=np.int64)
        for p in np.nonzero(self.isp)[0]:
            blk = spf[p::p]
            blk[blk == 0] = p
        self.spf = spf
        self._cub = {}
        self._leg = {}

    def factor(self, m):
        fs = []
        while m > 1:
            p = int(self.spf[m]); e = 0
            while m % p == 0: m //= p; e += 1
            fs.append((p, e))
        return fs

    def elems(self, lo, hi, primes_only=False):
        """primary split-squarefree elements with lo < N <= hi.
        returns list of dicts: a, b, N, ps (rational primes), rs (omega mod the prime above p)."""
        out = []
        B = int(math.isqrt(4 * hi // 3)) + 3
        for b in range(-B, B + 1):
            if b % 3: continue
            disc = 4 * hi - 3 * b * b
            if disc < 0: continue
            r = math.isqrt(disc)
            for a in range((b - r) // 2 - 1, (b + r) // 2 + 2):
                if a % 3 != 2: continue
                nn = a * a - a * b + b * b
                if nn <= lo or nn > hi or nn <= 1: continue
                if math.gcd(a, b) != 1: continue
                fs = self.factor(nn)
                if any(e > 1 or p % 3 != 1 for p, e in fs): continue
                if primes_only and len(fs) != 1: continue
                ps = [p for p, _ in fs]
                rs = [(-a * pow(b, -1, p)) % p for p in ps]
                out.append(dict(a=a, b=b, N=nn, ps=ps, rs=rs))
        out.sort(key=lambda e: (e['N'], e['a'], e['b']))
        return out

    def cubtab(self, p, r):
        """exponent table t[x] in {0,1,2} with (x/pi)_3 = omega^t, -1 at 0; pi = prime above p with omega = r mod pi"""
        key = (p, r)
        if key not in self._cub:
            v = powmod(np.arange(p, dtype=np.int64), (p - 1) // 3, p)
            tab = np.full(p, -1, dtype=np.int64)
            tab[v == 1] = 0; tab[v == r % p] = 1; tab[v == (r * r) % p] = 2
            tab[0] = -1
            self._cub[key] = tab
        return self._cub[key]

    def legtab(self, q):
        if q not in self._leg:
            t = np.full(q, -1, dtype=np.int8)
            t[(np.arange(1, q, dtype=np.int64) ** 2) % q] = 1
            t[0] = 0
            self._leg[q] = t
        return self._leg[q]

# ---------- characters evaluated on a column set ----------
def col_arrays(cols):
    A = np.array([c['a'] for c in cols], dtype=np.int64)
    B = np.array([c['b'] for c in cols], dtype=np.int64)
    return A, B

def quad_row(ar, A, B, k):
    """(n/k)_2 for all columns n = A + B omega, k split-squarefree element"""
    v = np.ones(len(A), dtype=np.int8)
    for q, r in zip(k['ps'], k['rs']):
        v = v * ar.legtab(q)[(A + B * r) % q]
    return v

def cubic_exp(ar, A, B, P):
    """exponent e with (n/P)_3 = omega^e (P prime, split); -1 where P | n"""
    q, r = P['ps'][0], P['rs'][0]
    return ar.cubtab(q, r)[(A + B * r) % q]

def cubic_val(ar, A, B, P, power=1):
    e = cubic_exp(ar, A, B, P)
    out = np.where(e < 0, 0, W ** ((power * np.where(e < 0, 0, e)) % 3))
    return out

# ---------- Gauss sums ----------
def gauss_direct(ar, n):
    """g(n) = sum_{x mod n} (x/n)_3 e(Tr(x/(n sqrt-3))) = sum_x chi(x) exp(-2 pi i x b / N(n))"""
    nn = n['N']; x = np.arange(nn, dtype=np.int64)
    kk = np.zeros(nn, dtype=np.int64); zero = np.zeros(nn, bool)
    for p, r in zip(n['ps'], n['rs']):
        t = ar.cubtab(p, r)[x % p]
        zero |= (t < 0); kk += np.where(t < 0, 0, t)
    chi = np.where(zero, 0, W ** (kk % 3))
    return np.sum(chi * np.exp(-2j * np.pi * ((x * n['b']) % nn) / nn))

def cubic_sym_elem(ar, c, d, p, r):
    """(c + d omega / pi)_3 for pi above p with omega = r mod pi, as complex"""
    t = ar.cubtab(p, r)[(c + d * r) % p]
    return 0 if t < 0 else W ** t

class GaussTable:
    """g~(n) via twisted multiplicativity g(c1 c2) = conj((c1/c2)_3) g(c1) g(c2) from prime Gauss sums."""
    def __init__(self, ar, primes):
        self.ar = ar
        self.prime = {}   # (p, r) -> (a, b, g~)
        for P in primes:
            p, r = P['ps'][0], P['rs'][0]
            g = gauss_direct(ar, P) / math.sqrt(p)
            self.prime[(p, r)] = (P['a'], P['b'], g)

    def gt(self, n):
        facs = [self.prime[(p, r)] for p, r in zip(n['ps'], n['rs'])]
        keys = list(zip(n['ps'], n['rs']))
        val = 1 + 0j
        for (a, b, g) in facs: val *= g
        for i in range(len(facs)):
            for j in range(i + 1, len(facs)):
                ai, bi, _ = facs[i]; pj, rj = keys[j]
                val *= np.conj(cubic_sym_elem(self.ar, ai, bi, pj, rj))
        return val
