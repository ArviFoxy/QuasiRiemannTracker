"""Does the dyadic sextic family have a Gauss-sum bias? (test of statement (A), round 11)

Rows: primary primes pi of Z[w] with N(pi) = p in [U, 2U], p = 1 mod 36 (so the unit symbols
(w/pi)_6 and (-1/pi)_6 are 1 and sextic reciprocity has no sign between rows).
Columns: primary n with N(n) in [N, 2N], coprime to 6.
Dual form F(b) = sum_n |sum_pi b_pi (pi/n)_6|^2 / (#n ||b||^2), for
  b = conj(gt(pi)) * (c/pi)_6 (gt = normalized sextic Gauss sum, c a fixed twist), against random
  unimodular b. Prediction from Poisson in n: the sixth-power dual frequencies h = e a^6 give the
  Gauss vectors an excess of order (U^2/N)^(1/6)/log U over the random ones.
usage: python3 gauss_bias.py U N1,N2,...
"""
import sys, cmath, math, random
import numpy as np

def primes_upto(n):
    s = bytearray([1]) * (n + 1); s[0] = s[1] = 0
    for i in range(2, int(n ** 0.5) + 1):
        if s[i]: s[i * i::i] = bytearray(len(s[i * i::i]))
    return [i for i in range(n + 1) if s[i]]

def norm(a, b): return a * a - a * b + b * b

def mul(x, y):  # (a + b w)(c + d w), w^2 = -1 - w
    a, b = x; c, d = y
    return (a * c - b * d, a * d + b * c - b * d)

UNITS = [(1, 0), (-1, 0), (0, 1), (0, -1), (1, 1), (-1, -1)]   # 1, -1, w, -w, -w^2 = 1 + w, w^2

def primary(x):
    for u in UNITS:
        a, b = mul(x, u)
        if a % 3 == 2 and b % 3 == 0: return (a, b)
    return None

def split_prime(p):
    """a primary pi with N(pi) = p (p = 1 mod 3)"""
    m = int(math.isqrt(4 * p)) + 2
    for b in range(1, m):
        # a^2 - a b + b^2 = p  ->  a = (b +- sqrt(4p - 3b^2))/2
        D = 4 * p - 3 * b * b
        if D < 0: break
        r = math.isqrt(D)
        if r * r == D and (b + r) % 2 == 0:
            return primary(((b + r) // 2, b))
    raise ValueError(p)

def omega_root(pi, p):
    """the image r of w in Z[w]/pi = F_p: a + b r = 0 mod p"""
    a, b = pi
    return (-a * pow(b, -1, p)) % p

def mu6_index(z, p, r):
    """z in F_p^*: return k with z^((p-1)/6) = zeta^k, zeta = -w^2 (a primitive 6th root: zeta = 1 + w)"""
    t = pow(z, (p - 1) // 6, p)
    zeta = (1 + r) % p
    v = 1
    for k in range(6):
        if v == t: return k
        v = v * zeta % p
    raise ValueError

ZETA = [cmath.exp(2j * math.pi * k / 6) for k in range(6)]   # zeta = e(1/6) = 1 + w

def symbol_prime(x, q):
    """(x/q)_6 for a prime ideal q given as ('s', p, r) (split) or ('i', p) (inert); x = (a, b)"""
    a, b = x
    if q[0] == 's':
        _, p, r = q
        z = (a + b * r) % p
        if z == 0: return 0
        return ZETA[mu6_index(z, p, r)]
    _, p = q   # inert: F_{p^2} = F_p[w], w^2 = -1 - w; x^((p^2-1)/6)
    def fmul(u, v):
        c, d = u; e, f = v
        return ((c * e - d * f) % p, (c * f + d * e - d * f) % p)
    base = (a % p, b % p)
    if base == (0, 0): return 0
    res = (1, 0); e = (p * p - 1) // 6
    while e:
        if e & 1: res = fmul(res, base)
        base = fmul(base, base); e >>= 1
    # res is a 6th root of unity in F_p[w]: match against zeta^k = (1 + w)^k
    v = (1, 0)
    for k in range(6):
        if v == res: return ZETA[k]
        v = fmul(v, (1, 1))
    raise ValueError

def gauss(pi):
    a, b = pi; p = norm(a, b); r = omega_root(pi, p)
    s = 0
    for x in range(1, p):
        s += ZETA[mu6_index(x, p, r)] * cmath.exp(-2j * math.pi * (b * x % p) / p)
    return s / math.sqrt(p)

TW2 = bool(__import__('os').environ.get('TW2'))


def main():
    U = int(sys.argv[1]); Ns = [int(x) for x in sys.argv[2].split(',')]
    random.seed(1)
    ps = [p for p in primes_upto(2 * U) if p >= U and p % 36 == 1]
    rows = []
    for p in ps:
        pi = split_prime(p)
        rows += [pi, primary((pi[0] - pi[1], -pi[1]))]   # pi and its conjugate a + b w^2 = (a - b) - b w
    rows = [x for x in rows if x is not None]
    g = np.array([gauss(pi) for pi in rows])
    print(f"U={U}: {len(rows)} rows, |g|: {np.abs(g).min():.3f}..{np.abs(g).max():.3f}")
    # twists (c/pi)_6 for c = (sqrt(-3))^k = (1 + 2w)^k
    s3 = (1, 2)
    tw = np.array([symbol_prime(s3, ('s', norm(*pi), omega_root(pi, norm(*pi)))) for pi in rows])
    tw2 = np.array([ZETA[mu6_index(2, norm(*pi), omega_root(pi, norm(*pi)))] for pi in rows])
    vecs = {}
    for k in range(6):
        for l in range(6 if TW2 else 1):
            vecs[f"conj(g)·s3^{k}·2^{l}"] = np.conj(g) * tw ** k * tw2 ** l
            vecs[f"g·s3^{k}·2^{l}"] = g * tw ** k * tw2 ** l
    for t in range(6):
        vecs[f"random{t}"] = np.exp(2j * math.pi * np.random.default_rng(t).random(len(rows)))
    allp = primes_upto(2 * max(Ns))
    split_roots = {}
    for p in allp:
        if p % 3 == 1:
            r = [x for x in range(p) if (x * x + x + 1) % p == 0]
            split_roots[p] = r
    for N in Ns:
        cols = []
        m = int(math.isqrt(4 * 2 * N // 3)) + 3
        for c in range(-m, m + 1):
            for d in range(-m, m + 1):
                if c % 3 != 2 or d % 3 != 0: continue
                nn = norm(c, d)
                if nn < N or nn >= 2 * N or nn % 2 == 0 or nn % 3 == 0: continue
                cols.append((c, d))
        # factor each column into prime ideals
        M = np.ones((len(rows), len(cols)), dtype=complex)
        for j, n in enumerate(cols):
            nn = norm(*n); rem = nn
            for p in allp:
                if p * p > rem and rem > 1 and p > rem: break
                if rem % p: continue
                e = 0
                while rem % p == 0: rem //= p; e += 1
                if p % 3 == 2:
                    q = ('i', p); k = e // 2
                    col = np.array([symbol_prime(pi, q) for pi in rows]) ** k
                    M[:, j] *= col
                else:
                    for r in split_roots[p]:
                        # multiplicity of (p, w - r) in n
                        x = n; k = 0
                        while (x[0] + x[1] * r) % p == 0 and k < e:
                            # divide x by the prime pi_r = generator of (p, w - r)
                            k += 1
                            x = None if k == e else x
                            if x is None: break
                        # simpler: the exponent of each split prime ideal; split evenly by checking n mod pi_r^k
                        kk = 0; a, b = n
                        pk = p
                        while kk < e and (a + b * r) % p == 0:
                            # test divisibility by pi_r^(kk+1) via the p-adic root r_k of x^2+x+1 mod p^(kk+1)
                            kk += 1
                            break
                        k = mult_split(n, p, r, e)
                        if k:
                            q = ('s', p, r)
                            col = np.array([symbol_prime(pi, q) for pi in rows]) ** k
                            M[:, j] *= col
            if rem > 1:
                p = rem
                if p % 3 == 2:
                    raise ValueError("inert prime with odd exponent")
                for r in [x for x in range(p) if (x * x + x + 1) % p == 0]:
                    k = mult_split(n, p, r, 1)
                    if k:
                        M[:, j] *= np.array([symbol_prime(pi, ('s', p, r)) for pi in rows]) ** k
        out = []
        for name, b in vecs.items():
            v = b @ M
            F = np.sum(np.abs(v) ** 2) / (len(cols) * np.sum(np.abs(b) ** 2))
            out.append((name, F))
        rnd = [F for name, F in out if name.startswith('random')]
        print(f" N={N}: {len(cols)} columns; random {np.mean(rnd):.3f} ± {np.std(rnd):.3f}; "
              f"top singular^2/#cols {np.linalg.norm(M, 2) ** 2 / len(cols):.2f}")
        for name, F in out:
            if not name.startswith('random'): print(f"    {name:14s} {F:.3f}")

def mult_split(n, p, r, e):
    """exponent of the prime ideal (p, w - r) in n (e = exponent of p in N(n))"""
    # lift r to a root of x^2 + x + 1 mod p^e (Hensel), then n = 0 mod (p^k, w - r_k)
    a, b = n; k = 0; rk = r; pk = p
    while k < e:
        if (a + b * rk) % pk != 0: break
        k += 1
        if k == e: break
        # lift to mod p^(k+1)
        pk1 = pk * p
        f = (rk * rk + rk + 1) % pk1; df = (2 * rk + 1) % pk1
        rk = (rk - f * pow(df, -1, pk1)) % pk1
        pk = pk1
    return k

if __name__ == "__main__":
    main()
