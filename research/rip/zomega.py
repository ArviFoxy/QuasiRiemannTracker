"""Sextic residue symbols over Z[w] (w = e^{2 pi i/3}) for RIP numerics.
Elements a + b w as integer pairs.  Primary: a = 2 mod 3, b = 0 mod 3.  Rows: squarefree ideals of norm in
[B, 2B] coprime to 6 (one generator each).  Sources: primary elements of norm <= L, coprime to 6, sixth-power-free
in the ideal sense.  chi_z(I) = (I / z)_6 = prod_{pi | z} (I / pi)_6, (x/pi)_6 = x^{(N pi - 1)/6} mod pi."""
import numpy as np, math
def norm(a, b): return a*a - a*b + b*b
def mul(x, y):
    a, b = x; c, d = y   # (a + b w)(c + d w) = ac + (ad + bc) w + bd w^2,  w^2 = -1 - w
    return (a*c - b*d, a*d + b*c - b*d)
def rat_primes(n):
    s = np.ones(n+1, bool); s[:2] = False
    for i in range(2, int(n**.5)+1):
        if s[i]: s[i*i::i] = False
    return [int(p) for p in np.nonzero(s)[0]]
class Prime:
    """a prime ideal of Z[w] coprime to 6: split (p = 1 mod 3, generator pi) or inert (q = 2 mod 3)."""
    def __init__(self, p, gen=None):
        self.p = p; self.split = (p % 3 == 1)
        if self.split:
            a, b = gen; self.N = p
            self.r = (-a * pow(b, -1, p)) % p          # image of w in Z[w]/pi = F_p
            self.e = (p - 1) // 6
            # images of the six roots of unity +-w^j
            self.roots = {}
            for j in range(3):
                wj = pow(self.r, j, p)
                self.roots[wj % p] = j            # w^j  -> exponent 2j in mu_6 (w = zeta6^2)
                self.roots[(-wj) % p] = (j, 'neg')
        else:
            self.N = p * p; self.e = (p * p - 1) // 6
    def sym(self, x):
        """(x / pi)_6 as an exponent k in Z/6 (zeta6^k), or None if pi | x."""
        a, b = x
        if self.split:
            p = self.p; v = (a + b * self.r) % p
            if v == 0: return None
            t = pow(v, self.e, p)
            j = self.roots[t]
            return (2 * j) % 6 if not isinstance(j, tuple) else (2 * j[0] + 3) % 6
        q = self.p
        a %= q; b %= q
        if a == 0 and b == 0: return None
        # power in F_q[w]/(w^2 + w + 1)
        res = (1, 0); base = (a, b); e = self.e
        while e:
            if e & 1: res = ((res[0]*base[0] - res[1]*base[1]) % q, (res[0]*base[1] + res[1]*base[0] - res[1]*base[1]) % q)
            base = ((base[0]*base[0] - base[1]*base[1]) % q, (2*base[0]*base[1] - base[1]*base[1]) % q)
            e >>= 1
        # identify res among +-w^j : w^0 = (1,0), w = (0,1), w^2 = (-1,-1)
        cand = {(1, 0): 0, (0, 1): 2, ((-1) % q, (-1) % q): 4, ((-1) % q, 0): 3, (0, (-1) % q): 5, (1, 1): 1}
        return cand[res]
def split_generator(p):
    """a generator a + b w of a prime above p = 1 mod 3 (norm p)."""
    m = int(math.isqrt(4 * p)) + 2
    for a in range(-m, m + 1):
        for b in range(-m, m + 1):
            if norm(a, b) == p: return (a, b)
def primes_list(maxN):
    out = []
    for p in rat_primes(maxN):
        if p in (2, 3): continue
        if p % 3 == 1:
            a, b = split_generator(p)
            out.append(Prime(p, (a, b))); out.append(Prime(p, (a + 0 - b, -b) if False else conj(a, b)))
        elif p * p <= maxN:
            out.append(Prime(p))
    return out
def conj(a, b):   # conjugate of a + b w is a + b w^2 = (a - b) - b w
    return (a - b, -b)
