# Column-branch alignment test over Z[omega]:
#   S = sum_{R: N(R)<=K} | sum_{n: N/2<N(n)<=N} c_n (n/R)_2 |^2
# vs Diag = sum_R sum_n |c_n|^2 1_{(n,R)=1}  (generic size)
# and the large-sieve column term ~ (#n) * ||c||^2 (attained only by aligned c).
import numpy as np, math, sys, random
K = int(sys.argv[1]); N = int(sys.argv[2]); seed = 1
rng = np.random.default_rng(seed)

def sieve(m):
    s = np.ones(m+1, bool); s[:2] = False
    for i in range(2, int(m**0.5)+1):
        if s[i]: s[i*i::i] = False
    return s
LIM = N + 10
isp = sieve(LIM)
# smallest prime factor table for factoring norms
spf = np.zeros(LIM+1, dtype=np.int64)
for p in range(2, LIM+1):
    if isp[p]:
        spf[p::p] = np.where(spf[p::p] == 0, p, spf[p::p])
def factor(m):
    fs = []
    while m > 1:
        p = int(spf[m]); e = 0
        while m % p == 0: m //= p; e += 1
        fs.append((p, e))
    return fs

def primary_elems(lo, hi):
    # primary: a = 2 mod 3, b = 0 mod 3; primitive gcd(a,b)=1; norm squarefree, all p = 1 mod 3
    out = []
    B = int(math.isqrt(4*hi//3)) + 3
    for b in range(-B, B+1):
        if b % 3: continue
        # a^2 - a b + b^2 <= hi
        disc = 4*hi - 3*b*b
        if disc < 0: continue
        r = math.isqrt(disc)
        for a in range((b - r)//2 - 1, (b + r)//2 + 2):
            if a % 3 != 2: continue
            nn = a*a - a*b + b*b
            if nn <= lo or nn > hi or nn == 1 and lo >= 1: continue
            if math.gcd(a, b) != 1: continue
            fs = factor(nn)
            if any(e > 1 or p % 3 != 1 for p, e in fs): continue
            out.append((a, b, nn, [p for p, _ in fs]))
    return out

rows = primary_elems(1, K)            # excludes the unit-norm element
cols = primary_elems(N//2, N)
print(f"#rows={len(rows)}  #cols={len(cols)}  K={K} N={N}")

# cube-root tables: for prime p = 1 mod 3, discrete-log mod 3 of x via x^((p-1)/3)
def cubic_char_table(p, r):
    # returns k[x] in {0,1,2} with x^((p-1)/3) = r^k mod p, -1 for x=0
    x = np.arange(p, dtype=np.int64)
    v = np.array([pow(int(t), (p-1)//3, p) for t in x], dtype=np.int64)
    tab = np.full(p, -1, dtype=np.int64)
    tab[v == 1] = 0
    tab[v == r % p] = 1
    tab[v == (r*r) % p] = 2
    tab[0] = -1
    return tab
cache = {}
w = np.exp(2j*np.pi/3)
def gauss_tilde(a, b, nn, ps):
    x = np.arange(nn, dtype=np.int64)
    kk = np.zeros(nn, dtype=np.int64); zero = np.zeros(nn, bool)
    for p in ps:
        r = (-a * pow(b, -1, p)) % p          # omega mod the prime of n above p
        key = (p, r)
        if key not in cache: cache[key] = cubic_char_table(p, r)
        t = cache[key][x % p]
        zero |= (t < 0); kk += np.where(t < 0, 0, t)
    chi = np.where(zero, 0, w ** (kk % 3))
    g = np.sum(chi * np.exp(-2j*np.pi * ((x * b) % nn) / nn))
    return g / math.sqrt(nn)

gt = np.array([gauss_tilde(a, b, nn, ps) for (a, b, nn, ps) in cols])
print("|g~| range:", np.abs(gt).min(), np.abs(gt).max())

# quadratic symbols (n/R)_2
def legendre(x, q):
    x %= q
    if x == 0: return 0
    return 1 if pow(x, (q-1)//2, q) == 1 else -1
M = np.zeros((len(rows), len(cols)))
for i, (c, d, nr, qs) in enumerate(rows):
    svals = [((-c * pow(d, -1, q)) % q, q) for q in qs]
    for j, (a, b, nn, ps) in enumerate(cols):
        val = 1
        for s, q in svals:
            val *= legendre(a + b*s, q)
            if val == 0: break
        M[i, j] = val

def test(cvec, name):
    D = M @ cvec
    S = np.sum(np.abs(D)**2)
    diag = np.sum((M**2) @ (np.abs(cvec)**2))
    nc = np.sum(np.abs(cvec)**2)
    print(f"{name:28s} S/Diag = {S/diag:7.3f}   (LS column bound/Diag ~ {(len(rows)+len(cols))*nc/diag:6.2f})  max_R|D|^2/mean = {np.max(np.abs(D)**2)/np.mean(np.abs(D)**2):7.2f}")

test(gt, "cubic Gauss g~(n)")
test(np.exp(2j*np.pi*rng.random(len(cols))), "random phases")
test(M[len(rows)//2].astype(complex), "aligned (n/R0)_2")
test(gt * M[len(rows)//3], "g~(n)*(n/R0)_2")
# real part / sign-only variants
test(np.real(gt), "Re g~(n)")

# Marked variant: c_n = g~(n) * sum_{pi: P0 < N(pi) <= 2 P0} conj((n/pi)_3)^2 / sqrt(N(pi))   (cubic mark sum, chi_P(n)^{-2})
P0 = int(sys.argv[3]) if len(sys.argv) > 3 else 40
marks = [m for m in primary_elems(P0, 2*P0) if len(m[3]) == 1]   # primary primes (split)
def cubic_sym(a, b, pa, pb, p):
    r = (-pa * pow(pb, -1, p)) % p           # omega mod pi
    v = pow((a + b*r) % p, (p-1)//3, p)
    if v == 0: return 0
    if v == 1: return 1
    return w if v == r % p else w*w
Mk = np.array([sum(np.conj(cubic_sym(a, b, pa, pb, pn))**2 / math.sqrt(pn) for (pa, pb, pn, _) in marks)
               for (a, b, nn, ps) in cols])
print(f"#marks={len(marks)} (norms in ({P0},{2*P0}]),  mean|M(n)|^2 = {np.mean(np.abs(Mk)**2):.3f}")
test(gt * Mk, "g~(n)*marksum(n)")
test(Mk.astype(complex), "marksum(n) alone")
