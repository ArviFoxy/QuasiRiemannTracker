import sys, math, numpy as np
sys.path.insert(0, '.')
from zomega import *
rng = np.random.default_rng(7)
B = int(sys.argv[1]); L = int(sys.argv[2]); P0 = int(sys.argv[3]) if len(sys.argv) > 3 else 30
zeta6 = np.exp(2j * np.pi * np.arange(6) / 6)
PR = primes_list(max(2 * B, L))
PR.sort(key=lambda x: x.N)
# rows: squarefree products of distinct prime ideals, norm in [B, 2B]
rows = []
def build(start, N, facs):
    if B <= N <= 2 * B: rows.append(tuple(facs))
    for j in range(start, len(PR)):
        pr = PR[j]
        if N * pr.N > 2 * B: break
        build(j + 1, N * pr.N, facs + [j])
build(0, 1, [])
# sources: primary a + b w (a = 2 mod 3, b = 0 mod 3), norm <= L, squarefree odd norm, coprime to 3
src = []
m = int(math.isqrt(4 * L)) + 3
def sqfree(n):
    d = 2
    while d * d <= n:
        if n % (d * d) == 0: return False
        d += 1
    return True
for a in range(-m, m + 1):
    if a % 3 != 2: continue
    for b in range(-m, m + 1, 1):
        if b % 3: continue
        n = norm(a, b)
        if 1 < n <= L and n % 2 and n % 3 and sqfree(n): src.append((a, b))
R, S = len(rows), len(src)
# symbol table: sym[j][s] for each prime ideal j used and each source s
used = sorted({j for r in rows for j in r})
symtab = {}
for j in used:
    pr = PR[j]; arr = np.empty(S, int)
    for s, x in enumerate(src):
        k = pr.sym(x); arr[s] = -1 if k is None else k
    symtab[j] = arr
E = np.zeros((R, S), complex)
for r, facs in enumerate(rows):
    tot = np.zeros(S, int); zero = np.zeros(S, bool)
    for j in facs:
        a = symtab[j]; zero |= a < 0; tot = (tot + np.maximum(a, 0)) % 6
    E[r] = np.where(zero, 0, zeta6[tot])
G = E @ E.conj().T
d = np.real(np.diag(G)); dm = d.mean()
def top(idx):
    idx = np.asarray(idx)
    return float(np.linalg.eigvalsh(G[np.ix_(idx, idx)])[-1]) if len(idx) else 0.0
w, V = np.linalg.eigh(G); v1 = V[:, -1]
print('B=%d L=%d  rows R=%d  sources S=%d  mean diag %.0f  full top/diag = %.3f   (R/diag = %.3f)' % (B, L, R, S, dm, w[-1] / dm, R / dm))
print('  top 5 eigenvalues / diag:', np.round(w[-5:][::-1] / dm, 3), '  median eig/diag %.3f' % (np.median(w) / dm))
# slot polynomial over split primes of norm in [P0, 2 P0]
slot = [x for x in primes_list(2 * P0 + 2) if x.split and P0 <= x.N <= 2 * P0]
# T(chi_z) = sum over slot primes pi (as elements) of chi_z(pi): need the generator of each slot prime as a source element
def gen_of(pr):
    # primary generator of the split prime: search norm = p, primary, with matching residue map
    p = pr.p; mm = int(math.isqrt(4 * p)) + 3
    for a in range(-mm, mm + 1):
        for b in range(-mm, mm + 1):
            if norm(a, b) == p and a % 3 == 2 and b % 3 == 0 and (a + b * pr.r) % p == 0: return (a, b)
gens = [gen_of(pr) for pr in slot]
Tz = np.zeros(R, complex)
for r, facs in enumerate(rows):
    for g in gens:
        tot = 0; z = False
        for j in facs:
            k = PR[j].sym(g)
            if k is None: z = True; break
            tot += k
        if not z: Tz[r] += zeta6[tot % 6]
absT = np.abs(Tz) / math.sqrt(max(1, len(gens)))
print('  slot: %d split primes of norm in [%d, %d]' % (len(gens), P0, 2 * P0))
for rho in (0.5, 0.25, 0.1, 0.05):
    k = max(3, int(rho * R))
    rnd = np.mean([top(rng.choice(R, k, replace=False)) for _ in range(8)]) / dm
    bias = top(np.argsort(-np.abs(v1))[:k]) / dm
    lv = top(np.argsort(-absT)[:k]) / dm
    print('  rho=%.2f |W|=%4d  random %.3f   large-value(slot) %.3f   bias-aligned %.3f   [full %.3f]' % (rho, k, rnd, lv, bias, w[-1] / dm), flush=True)
