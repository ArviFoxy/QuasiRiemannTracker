"""Validation of probeB.py against the reference conventions of research/rip/zomega.py and zfamily.py.

usage: python3 -I test_probeB.py [B]       (default B = 1500)
 1. rows: the DFS of probeB.build_rows reproduces the rows of zfamily.py (same set of squarefree ideals of norm in [B,2B]);
 2. symbols: vectorised sextic_table == zomega.Prime.sym on every (prime ideal, source) pair;
 3. moments: run() 'actual' M4, M6 == brute-force sums of |S_u|^4, |S_u|^6 with S_u computed from zomega.Prime.sym only;
 4. multiplicativity of the symbol on primary sources: chi_u(n1 n2 n3) = chi_u(n1) chi_u(n2) chi_u(n3) (product of three
    primaries is primary), checked on random triples.
"""
import sys, os, math, time
sys.dont_write_bytecode = True
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import numpy as np
import probeB as pb
import zomega
from zw import Arith

B = int(sys.argv[1]) if len(sys.argv) > 1 else 1500
ms = [0.35, 0.5]
t0 = time.time()

# ---- zfamily-style reference rows (prime ideals via zomega.primes_list)
PR = zomega.primes_list(max(2 * B, 100))
PR.sort(key=lambda x: x.N)
ref_rows = []


def build(start, N, facs):
    if B <= N <= 2 * B:
        ref_rows.append(tuple(facs))
    for j in range(start, len(PR)):
        if N * PR[j].N > 2 * B:
            break
        build(j + 1, N * PR[j].N, facs + [j])


build(0, 1, [])
ref_norms = sorted(int(np.prod([PR[j].N for j in r])) for r in ref_rows)

ar = Arith(2 * B + 10)
PI = pb.prime_ideals(ar, 2 * B)
rows = pb.build_rows(PI['norm'], B, 2 * B)
my_norms = sorted(int(np.prod([PI['norm'][j] for j in r])) for r in rows)
print(f'1. rows: zfamily {len(ref_rows)}  probeB {len(rows)}  identical norm multisets: {ref_norms == my_norms}')
# the prime-ideal lists agree as multisets of norms (split ideals counted per ideal)
print(f'   prime ideals: zomega.primes_list {len(PR)} vs probeB {len(PI["norm"])}: {sorted(int(x.N) for x in PR) == sorted(int(x) for x in PI["norm"])}')

# ---- symbols
SA, SB, SN = pb.primary_window(20, 120)
E, Z = pb.sextic_table(PI, SA, SB)
# map probeB ideals to zomega primes through (norm, sym signature)
bad = 0
for i in range(len(PI['norm'])):
    if PI['kind'][i] == 0:
        p, r = int(PI['p'][i]), int(PI['r'][i])
        a, b = int(PI['a'][i]), int(PI['b'][i])
        pr = zomega.Prime(p, (a, b))
        assert pr.r == r, (p, a, b, pr.r, r)
    else:
        pr = zomega.Prime(int(PI['p'][i]))
    for j in range(len(SA)):
        s = pr.sym((int(SA[j]), int(SB[j])))
        mine = None if Z[i, j] else int(E[i, j])
        if s != mine:
            bad += 1
print(f'2. symbols: {len(PI["norm"])} prime ideals x {len(SA)} sources; mismatches: {bad}')

# ---- brute-force moments from zomega.Prime.sym only
zeta = np.exp(2j * np.pi * np.arange(6) / 6)
res = pb.run(B, ms, 1, 'all', np.random.default_rng(5))
nbad = 0
for rec in res:
    N = rec['N']
    A_, B_, N_ = pb.primary_window(N, 2 * N)
    S = np.zeros(len(rows), dtype=complex)
    for ri, r in enumerate(rows):
        tot = 0
        for j in range(len(A_)):
            e = 0; z = False
            for i in r:
                pr = zomega.Prime(int(PI['p'][i]), (int(PI['a'][i]), int(PI['b'][i]))) if PI['kind'][i] == 0 else zomega.Prime(int(PI['p'][i]))
                s = pr.sym((int(A_[j]), int(B_[j])))
                if s is None:
                    z = True; break
                e += s
            if not z:
                tot += zeta[e % 6]
        S[ri] = tot
        if ri >= 200:           # a subset of rows is enough for the check below
            break
    # compare with run(): recompute the same subset through the pipeline
    nsub = ri + 1
    S = S[:nsub]
    Esub, Zsub = pb.sextic_table(PI, A_, B_)
    S2 = np.zeros(nsub, dtype=complex)
    for rr in range(nsub):
        idx = list(rows[rr])
        EE = Esub[idx].astype(int).sum(0) % 6
        ZZ = Zsub[idx].any(0)
        S2[rr] = np.sum(np.where(ZZ, 0, zeta[EE]))
    d = np.max(np.abs(S - S2))
    nbad += d > 1e-9
    print(f'3. m={rec["m"]}: N={N:.1f} C={rec["C"]}: direct-vs-pipeline S_u max diff over {nsub} rows = {d:.1e};'
          f'  run(): M4={rec["actual"]["M4"]:.4f} M6={rec["actual"]["M6"]:.4f}')
# full moments check on the whole family with the incidence/sparse path vs direct (small window only)
rec = res[0]
N = rec['N']
A_, B_, N_ = pb.primary_window(N, 2 * N)
Esub, Zsub = pb.sextic_table(PI, A_, B_)
S_all = np.zeros(len(rows), dtype=complex)
for rr, r in enumerate(rows):
    idx = list(r)
    EE = Esub[idx].astype(int).sum(0) % 6
    ZZ = Zsub[idx].any(0)
    S_all[rr] = np.sum(np.where(ZZ, 0, zeta[EE]))
M4 = np.sum(np.abs(S_all) ** 4) / (len(rows) * N ** 2)
M6 = np.sum(np.abs(S_all) ** 6) / (len(rows) * N ** 3)
print(f'   whole family, m={rec["m"]}: brute M4={M4:.6f} M6={M6:.6f};  run(): M4={rec["actual"]["M4"]:.6f} M6={rec["actual"]["M6"]:.6f}')

# ---- multiplicativity on primary triples
rng = np.random.default_rng(3)
SA3, SB3, SN3 = pb.primary_window(8, 60)
idxs = rng.integers(0, len(SA3), (300, 3))
okc = 0
tot = 0
for r in rows[:30]:
    prs = [(zomega.Prime(int(PI['p'][i]), (int(PI['a'][i]), int(PI['b'][i]))) if PI['kind'][i] == 0 else zomega.Prime(int(PI['p'][i]))) for i in r]
    for (i1, i2, i3) in idxs[:20]:
        x = [(int(SA3[i]), int(SB3[i])) for i in (i1, i2, i3)]
        prod = zomega.mul(zomega.mul(x[0], x[1]), x[2])
        assert prod[0] % 3 == 2 and prod[1] % 3 == 0       # product of three primaries is primary
        ev = []
        for y in (prod, x[0], x[1], x[2]):
            e = 0; z = False
            for pr in prs:
                s = pr.sym(y)
                if s is None:
                    z = True; break
                e += s
            ev.append(None if z else e % 6)
        if None in ev:
            continue
        tot += 1
        okc += (ev[0] == (ev[1] + ev[2] + ev[3]) % 6)
print(f'4. chi_u(n1 n2 n3) = chi_u(n1)chi_u(n2)chi_u(n3) for primary triples: {okc}/{tot}')
# ---- exact diagonal counts T4, T6 against brute-force enumeration (python dict over ideal products)
from collections import Counter
for (lo, hi) in ((10, 25), (30, 80)):
    A_, B_, N_ = pb.primary_window(lo, hi)
    el = list(zip(A_.tolist(), B_.tolist()))
    c2 = Counter(); c3 = Counter()
    for x in el:
        for y in el:
            p2 = zomega.mul(x, y)
            c2[p2] += 1
            for z in el:
                c3[zomega.mul(p2, z)] += 1
    T4b = sum(v * v for v in c2.values()); T6b = sum(v * v for v in c3.values())
    T4, T6 = pb.diag_counts(A_, B_)
    print(f'6. window norms [{lo},{hi}): C={len(el)}  T4 brute {T4b} vs {T4};  T6 brute {T6b} vs {T6}')
print(f'total {time.time()-t0:.1f}s')
