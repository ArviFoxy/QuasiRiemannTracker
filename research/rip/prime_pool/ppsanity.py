"""ppsanity.py -- correctness checks of the machinery (run first).   python3 -I ppsanity.py [B]

1. vectorised symbols == zomega.Prime.sym (split and inert), multiplicativity in n and in z;
2. primary_generator: norm p, primary, lies in the right ideal;
3. rows (squarefree, coprime to 6, N in [B,2B]) == brute-force enumeration by distinct prime ideals (zfamily-style);
4. X1 X2 Q(z) == sum_m c_m chi_z(m) (collected over ideals, chi_z(m) computed from the product element by zomega.Prime.sym);
   a triple product of primary elements is primary;
5. the coprimality factor rho_m vs the exact fraction of rows coprime to m;
6. Gauss sums: |g~| = 1; canon = conj((c/P)_6) * simple with c = -b.
"""
import os, sys, math, time
import numpy as np
sys.dont_write_bytecode = True
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from ppcore import *

B = int(sys.argv[1]) if len(sys.argv) > 1 else 3000
rng = np.random.default_rng(1)
ok = True
def check(name, cond, extra=''):
    global ok
    ok &= bool(cond)
    print(('PASS ' if cond else 'FAIL ') + name + (' ' + extra if extra else ''), flush=True)

ID = Ideals(2 * B)
# ---------------------------------------------------------------- 1. symbols vs zomega
pl = zo.primes_list(400)
bad = 0; cnt = 0
for pr in pl:
    if pr.split:
        for _ in range(30):
            x = (int(rng.integers(-300, 300)), int(rng.integers(-300, 300)))
            ref = pr.sym(x)
            c = int(sym_codes(np.array([pr.p]), np.array([pr.r]), np.array([x[0]]), np.array([x[1]]))[0, 0])
            cnt += 1
            bad += (ZCODE if ref is None else ref) != c
check('vectorised symbols == zomega.Prime.sym on %d random (split ideal, element) pairs' % cnt, bad == 0)
# inert via symbol_table
uid = np.array([ID.ns + 0, ID.ns + 1])
xs = [(int(rng.integers(-50, 50)), int(rng.integers(-50, 50))) for _ in range(20)]
Tt = symbol_table(ID, uid, [x[0] for x in xs], [x[1] for x in xs])
q0, q1 = int(ID.inert_q[0]), int(ID.inert_q[1])
ref = [[ZCODE if (c := zo.Prime(q).sym(x)) is None else c for x in xs] for q in (q0, q1)]
check('inert symbol table == zomega.Prime(q).sym (q=%d,%d)' % (q0, q1), (Tt == np.array(ref)).all())

# multiplicativity in n:  (n1 n2 / pi)_6 = (n1/pi)_6 (n2/pi)_6 on elements
bad = 0
for pr in pl:
    if not pr.split: continue
    for _ in range(10):
        x = (int(rng.integers(-60, 60)), int(rng.integers(-60, 60))); y = (int(rng.integers(-60, 60)), int(rng.integers(-60, 60)))
        a, b, c = pr.sym(x), pr.sym(y), pr.sym(zo.mul(x, y))
        if None in (a, b, c): continue
        bad += (a + b) % 6 != c
check('multiplicativity (n1 n2 / pi)_6', bad == 0)

# ---------------------------------------------------------------- 2. primary generators
badg = 0
for k in range(0, len(ID.split_p), max(1, len(ID.split_p) // 60)):
    p = int(ID.split_p[k])
    for w in (0, 1):
        r = int(ID.split_r[k]) if w == 0 else p - 1 - int(ID.split_r[k])
        a, b = primary_generator(p, r)
        badg += not (a * a - a * b + b * b == p and a % 3 == 2 and b % 3 == 0 and (a + b * r) % p == 0)
check('primary_generator: norm p, primary, in the right ideal', badg == 0)

# ---------------------------------------------------------------- 3. rows vs brute force
t0 = time.time()
rows = enumerate_rows(B, ID)
R = rows['R']
PR = zo.primes_list(2 * B)
PR.sort(key=lambda x: x.N)
brute = []
def build(start, N, facs):
    if B <= N <= 2 * B: brute.append(N)
    for j in range(start, len(PR)):
        if N * PR[j].N > 2 * B: break
        build(j + 1, N * PR[j].N, facs + [j])
build(0, 1, [])
mine = np.sort(rows['N'])
check('rows: count %d == brute-force count %d (zfamily-style enumeration of distinct prime ideals)' % (R, len(brute)), R == len(brute))
check('rows: multiset of norms identical', np.array_equal(mine, np.sort(np.array(brute))))
# product of the prime-ideal norms in PID equals the norm of the row element
PIDm = rows['PID']
pn = np.ones(R, I64)
for j in range(rows['J']):
    ids = PIDm[:, j]
    nrm = np.ones(R, I64)
    sp = (ids >= 0) & (ids < ID.ns)
    nrm[sp] = ID.split_p[ids[sp] // 2]
    it = ids >= ID.ns
    nrm[it] = ID.inert_q[ids[it] - ID.ns] ** 2
    pn *= nrm
check('rows: product of prime-ideal norms == N(row element)', np.array_equal(pn, rows['N']))
print('     (R=%d, R/B=%.4f; enumeration %.1fs)' % (R, R / B, time.time() - t0))

# ---------------------------------------------------------------- 4. Dirichlet series identity
m, s = 0.3, 0.4
Lplain = B ** max(m, s)
PA, PB, PN = primary_elements(Lplain)
pool = split_prime_sources(ID, B ** s, 2 * B ** s)
TA = np.array([P['a'] for P in pool], I64); TB = np.array([P['b'] for P in pool], I64)
SA = np.concatenate([PA, TA]); SB = np.concatenate([PB, TB])      # duplicates allowed here
uid = np.unique(PIDm[PIDm >= 0])
LOC = local_index(PIDm, uid)
T = symbol_table(ID, uid, SA, SB)
Sp = len(PA)
w = weight_vector(PN, B ** m, 'smooth')
rngp = np.random.default_rng(5)
aP = np.exp(2j * np.pi * rngp.random(len(pool)))
chi = chi_chunk(LOC, T, 0, R)
X = chi[:, :Sp] @ w
Q = chi[:, Sp:] @ aP
lhs = X * X * Q
ka, kb, d = self_convolution(PA, PB, w)
Am, ca, cb = conv_matrix(ka, kb, d, TA, TB)
cvec = Am.T @ aP
check('triple products primary (asserted inside conv_matrix); %d distinct ideals m' % len(ca), True)
# direct evaluation of sum_m c_m chi_z(m) on a few rows with zomega symbols
# factor the row generator into zomega.Prime objects via PID
def zprimes_of_row(i):
    out = []
    for j in range(rows['J']):
        idv = int(PIDm[i, j])
        if idv < 0: continue
        if idv < ID.ns:
            p, r = ID.split_pr(np.array([idv]))
            p = int(p[0]); r = int(r[0])
            g = primary_generator(p, r)
            out.append(zo.Prime(p, g))
        else:
            out.append(zo.Prime(int(ID.inert_q[idv - ID.ns])))
    return out
maxerr = 0
for i in rng.choice(R, 12, replace=False):
    prs = zprimes_of_row(i)
    # check the symbols of the row against Prime objects: the primary generator of the ideal is the row element itself
    tot = 0
    for ci in rng.choice(len(ca), min(len(ca), 400), replace=False):
        pass
    val = 0j
    for ci in range(len(ca)):
        mm = (int(ca[ci]), int(cb[ci]))
        ks = [pr.sym(mm) for pr in prs]
        if None in ks: continue
        val += cvec[ci] * ZETA6[sum(ks) % 6]
    maxerr = max(maxerr, abs(val - lhs[i]))
check('X1 X2 Q(z) == sum_m c_m chi_z(m)  (12 random rows, chi_z(m) from zomega.Prime.sym of the product element); max err %.2e' % maxerr, maxerr < 1e-8)
# the Parseval/diagonal identity at the level of numbers: sum_m |c_m|^2 vs sum d^2 * |pool| when no collisions
print('     sum|c|^2 = %.4f ; sum d^2 * sum|a|^2 = %.4f (equal up to P | k collisions)' % (np.sum(np.abs(cvec) ** 2), np.sum(d ** 2) * len(pool)))

# ---------------------------------------------------------------- 5. rho vs exact coprime fractions
pmax = int(max(Lplain, 2 * B ** s + 1))
rho = rho_elements(ID, ca, cb, pmax)
# exact: fraction of rows coprime to m = rows whose PID set misses the support of m
def support_ids(a, b):
    ids = set()
    Nm = a * a - a * b + b * b
    for p in ID.split_p[ID.split_p <= pmax]:
        p = int(p)
        if Nm % p: continue
        k = int(ID.pidx[p]); r1 = int(ID.split_r[k]); r2 = p - 1 - r1
        if (a + b * r1) % p == 0: ids.add(2 * k)
        if (a + b * r2) % p == 0: ids.add(2 * k + 1)
    for q in ID.inert_q[ID.inert_q <= math.isqrt(pmax)]:
        q = int(q)
        if a % q == 0 and b % q == 0: ids.add(ID.ns + ID.qidx[q])
    return ids
rowsets = [set(int(x) for x in PIDm[i] if x >= 0) for i in range(R)]
idx = rng.choice(len(ca), min(len(ca), 120), replace=False)
dev = []
for ci in idx:
    sup = support_ids(int(ca[ci]), int(cb[ci]))
    ex = sum(1 for rs in rowsets if not (rs & sup)) / R
    dev.append(ex / rho[ci])
check('rho_m analytic vs exact coprime fraction: ratio exact/rho in [%.4f, %.4f], mean %.4f' % (min(dev), max(dev), np.mean(dev)), 0.9 < min(dev) and max(dev) < 1.1)
# weighted D vs Dcop vs exact coprimality-weighted diagonal
D = R * np.sum(np.abs(cvec) ** 2)
Dcop_an = R * np.sum(rho * np.abs(cvec) ** 2)
Dcop_ex = 0.0
for ci in range(len(ca)):
    pass
print('     D = %.5g ; Dcop (analytic rho) = %.5g ; ratio %.4f' % (D, Dcop_an, Dcop_an / D))
# exact Dcop via signature grouping (all m)
from collections import Counter
sigs = Counter()
Uset = set()
supports = [support_ids(int(ca[ci]), int(cb[ci])) for ci in range(len(ca))]
for sp_ in supports: Uset |= sp_
sigc = Counter(frozenset(rs & Uset) for rs in rowsets)
Dex = 0.0
absc2 = np.abs(cvec) ** 2
for sg, cn in sigc.items():
    msk = np.array([not (sp_ & sg) for sp_ in supports])
    Dex += cn * absc2[msk].sum()
check('Dcop exact (signature grouping) %.5g vs analytic %.5g: ratio %.4f' % (Dex, Dcop_an, Dex / Dcop_an), abs(Dex / Dcop_an - 1) < 0.02)

# ---------------------------------------------------------------- 6. Gauss sums
maxd = 0; maxt = 0
for P in pool[:12]:
    gs, gc = gauss_sums(P)
    maxd = max(maxd, abs(abs(gs) - 1), abs(abs(gc) - 1))
    p, r, b = P['p'], P['r'], P['b']
    cb_ = (-b) % p
    ch = ZETA6[sym_codes(np.array([p]), np.array([r]), np.array([cb_]), np.array([0]))[0, 0]]
    maxt = max(maxt, abs(gc - np.conj(ch) * gs))
check('Gauss sums |g~|=1 (err %.1e) and canon = conj((c/P)_6) simple with c=-b (err %.1e)' % (maxd, maxt), maxd < 1e-8 and maxt < 1e-8)
print('ALL PASS' if ok else 'SOME CHECK FAILED')
