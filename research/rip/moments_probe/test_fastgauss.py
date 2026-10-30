"""Validation of fastgauss.py against the reference implementation in research/round7/signal-processing/zw.py.

usage: python3 -I test_fastgauss.py [LIM]      (default LIM = 6000; the slow reference is O(p) numpy per prime)
Checks (all differences should be ~1e-12 or smaller):
  1. fast prime Gauss sums (every conjugate summed directly) vs zw.gauss_direct;
  2. the conjugation shortcut g~(conj pi) = conj g~(pi) vs direct;
  3. composite g~ by FastGaussTable vs zw.GaussTable.gt and vs zw.gauss_direct on composite columns;
  4. g~^3 = pi/|pi| for the raw (unsnapped) C output, and the size of the snap.
"""
import sys, os, math, time
sys.dont_write_bytecode = True
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import numpy as np
import fastgauss as fg
from zw import Arith, GaussTable, gauss_direct

LIM = int(sys.argv[1]) if len(sys.argv) > 1 else 6000
t0 = time.time()
ar = Arith(LIM + 10)
cols = ar.elems(1, LIM)
primes = [c for c in cols if len(c['ps']) == 1]
comps = [c for c in cols if len(c['ps']) >= 2]
print(f'LIM={LIM}: {len(cols)} columns, {len(primes)} prime ideals, {len(comps)} composite')

# reference
ref = GaussTable(ar, primes)
print(f'reference GaussTable built in {time.time()-t0:.1f}s', flush=True)

# 1. every conjugate summed directly
tab_full, worst_full = fg.prime_table(primes, ar.spf, use_conj_symmetry=False)
d1 = max(abs(tab_full[k][2] - ref.prime[k][2]) for k in ref.prime)
print(f'1. prime g~: max |fast(all summed) - direct| = {d1:.3e}   (max snap distance {worst_full:.3e})')

# raw check: g~_raw^3 = lambda, |g~_raw| = 1
ps = np.array([e['ps'][0] for e in primes]); rs = np.array([e['rs'][0] for e in primes]); bs = np.array([e['b'] for e in primes])
graw = fg.raw_gauss(ps, rs, bs, ar.spf) / np.sqrt(ps.astype(float))
lam = np.array([fg.lam_of(e['a'], e['b']) for e in primes])
print(f'4. raw C output: max ||g~|-1| = {np.max(np.abs(np.abs(graw)-1)):.2e},  max |g~^3 - lambda| = {np.max(np.abs(graw**3 - lam)):.2e}')
dd = max(abs(graw[i] - ref.prime[(int(ps[i]), int(rs[i]))][2]) for i in range(len(primes)))
print(f'   raw (unsnapped) vs direct: max diff = {dd:.3e}')

# 2. conjugation shortcut
tab_sym, worst_sym = fg.prime_table(primes, ar.spf, use_conj_symmetry=True)
d2 = max(abs(tab_sym[k][2] - ref.prime[k][2]) for k in ref.prime)
print(f'2. prime g~: max |fast(conj shortcut) - direct| = {d2:.3e}')

# 3. composite columns
ft = fg.FastGaussTable(tab_sym)
t1 = time.time()
gfast = np.array([ft.gt(c) for c in cols])
tf = time.time() - t1
t1 = time.time()
gslow = np.array([ref.gt(c) for c in cols])
ts = time.time() - t1
print(f'3. all columns: max |FastGaussTable.gt - GaussTable.gt| = {np.max(np.abs(gfast-gslow)):.3e}  (fast {tf:.2f}s, slow {ts:.2f}s)')
sub = [c for c in comps if c['N'] <= 2500][:300]
dm = 0.0
for c in sub:
    dm = max(dm, abs(ft.gt(c) - gauss_direct(ar, c) / math.sqrt(c['N'])))
print(f'   composite n (N<=2500, {len(sub)} of them): max |FastGaussTable.gt - gauss_direct/sqrt(N)| = {dm:.3e}')
print(f'   |g~(n)| range over columns: [{np.abs(gfast).min():.12f}, {np.abs(gfast).max():.12f}]')
# 5. conjugation symmetry g~(conj n) = conj g~(n) (used for the 'sym' surrogates and the conj-pair class of probe A)
pos = {(c['a'], c['b']): i for i, c in enumerate(cols)}
dsym = max(abs(gfast[pos[(c['a'] - c['b'], -c['b'])]] - np.conj(gfast[i])) for i, c in enumerate(cols))
print(f'5. columns: max |g~(conj n) - conj g~(n)| = {dsym:.3e}')
print(f'total {time.time()-t0:.1f}s')
