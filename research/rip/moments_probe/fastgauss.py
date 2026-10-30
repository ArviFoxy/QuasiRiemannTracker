"""Fast normalised cubic Gauss sums g~(n) over Z[omega] for the moments probe.

This reuses the existing model of research/round7/signal-processing (zw.py: Arith, GaussTable, gauss_direct,
cubic tables) and only replaces the two parts that do not scale:

 * the prime Gauss sums g~(pi) = g(pi)/sqrt(p), computed in O(p) by gauss_prime.c (compiled on first use)
   instead of numpy tables, then snapped to the exact cube root of lambda(pi) = pi/|pi| (g~^3 = lambda);
 * the composite sums by twisted multiplicativity g(c1 c2) = conj((c1/c2)_3) g(c1) g(c2), exactly the formula of
   GaussTable.gt, but with the cubic symbol evaluated by one modular exponentiation (GaussTable caches a table of
   size p for every larger prime factor, which is O(X^2) memory at X = 10^6).

`python3 -I test_fastgauss.py` validates every piece against zw.gauss_direct / zw.GaussTable.
"""
import sys, os, math, ctypes, hashlib, subprocess, tempfile
sys.dont_write_bytecode = True
import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
SP_DIR = os.path.normpath(os.path.join(HERE, '..', '..', 'round7', 'signal-processing'))
RIP_DIR = os.path.normpath(os.path.join(HERE, '..'))
for _d in (SP_DIR, RIP_DIR):
    if _d not in sys.path:
        sys.path.insert(0, _d)
import zw                      # Arith, GaussTable, gauss_direct, quad_row, col_arrays, cubic_exp, W
from zw import Arith, GaussTable, gauss_direct, quad_row, col_arrays, cubic_exp

W3 = zw.W                       # e^{2 pi i / 3}
W3POW = np.array([1, W3, W3 * W3])


# ---------------------------------------------------------------- C library
_LIB = None


def load_lib():
    global _LIB
    if _LIB is not None:
        return _LIB
    src = os.path.join(HERE, 'gauss_prime.c')
    code = open(src, 'rb').read()
    tag = hashlib.sha1(code).hexdigest()[:12]
    bdir = os.environ.get('MP_BUILD', os.path.join(tempfile.gettempdir(), 'moments_probe_build'))
    os.makedirs(bdir, exist_ok=True)
    so = os.path.join(bdir, f'libgaussprime_{tag}.so')
    if not os.path.exists(so):
        cmd = ['gcc', '-O3', '-march=native', '-fopenmp', '-shared', '-fPIC', src, '-o', so, '-lm']
        subprocess.run(cmd, check=True)
    lib = ctypes.CDLL(so)
    lib.gauss_primes.restype = None
    lib.gauss_primes.argtypes = [ctypes.c_int64] + [ctypes.c_void_p] * 4 + [ctypes.c_void_p] * 2 + [ctypes.c_int]
    _LIB = lib
    return lib


def primitive_root(p, spf):
    """smallest primitive root mod prime p; spf = smallest-prime-factor sieve up to >= p."""
    m = p - 1
    qs = set()
    while m > 1:
        q = int(spf[m])
        qs.add(q)
        while m % q == 0:
            m //= q
    g = 2
    while True:
        if all(pow(g, (p - 1) // q, p) != 1 for q in qs):
            return g
        g += 1


def raw_gauss(ps, rs, bs, spf, nthreads=4):
    """unnormalised G = sum_x chi(x) exp(-2 pi i x b/p) for arrays of (p, r, b)."""
    lib = load_lib()
    n = len(ps)
    p_arr = np.ascontiguousarray(ps, dtype=np.int64)
    r_arr = np.ascontiguousarray(rs, dtype=np.int64)
    b_arr = np.ascontiguousarray(bs, dtype=np.int64)
    g_arr = np.array([primitive_root(int(p), spf) for p in p_arr], dtype=np.int64)
    re = np.zeros(n)
    im = np.zeros(n)
    lib.gauss_primes(n, p_arr.ctypes.data, g_arr.ctypes.data, r_arr.ctypes.data, b_arr.ctypes.data,
                     re.ctypes.data, im.ctypes.data, nthreads)
    return re + 1j * im


def lam_of(a, b):
    z = complex(a - b / 2.0, b * math.sqrt(3.0) / 2.0)      # a + b*omega
    return z / abs(z)


def snap_cube_root(graw, lam):
    """nearest of the three cube roots of lam to graw; returns (value, distance, index)."""
    base = np.angle(lam) / 3.0
    cands = np.exp(1j * (base + 2.0 * np.pi * np.arange(3) / 3.0))
    d = np.abs(cands - graw)
    j = int(np.argmin(d))
    return cands[j], float(d[j]), j


def prime_table(prime_elems, spf, nthreads=4, use_conj_symmetry=True, verbose=False):
    """dict (p, r) -> (a, b, g~) for the given prime elements (dicts from Arith.elems(primes_only=True)).

    With use_conj_symmetry only the conjugate with the smaller r is summed; the other gets conj(g~)
    (g(conj n) = conj g(n); verified in test_fastgauss.py)."""
    byp = {}
    for e in prime_elems:
        byp.setdefault(e['ps'][0], []).append(e)
    todo = []
    for p, lst in byp.items():
        if use_conj_symmetry and len(lst) == 2:
            lst = [min(lst, key=lambda e: e['rs'][0])]
        todo.extend(lst)
    ps = np.array([e['ps'][0] for e in todo])
    rs = np.array([e['rs'][0] for e in todo])
    bs = np.array([e['b'] for e in todo])
    G = raw_gauss(ps, rs, bs, spf, nthreads) / np.sqrt(ps.astype(float))
    table = {}
    worst = 0.0
    for e, g in zip(todo, G):
        lam = lam_of(e['a'], e['b'])
        gs, dist, _ = snap_cube_root(g, lam)
        worst = max(worst, dist)
        table[(e['ps'][0], e['rs'][0])] = (e['a'], e['b'], gs)
    if use_conj_symmetry:
        for p, lst in byp.items():
            if len(lst) == 2:
                lo = min(lst, key=lambda e: e['rs'][0])
                hi = max(lst, key=lambda e: e['rs'][0])
                table[(p, hi['rs'][0])] = (hi['a'], hi['b'], np.conj(table[(p, lo['rs'][0])][2]))
    if verbose:
        print(f'  prime Gauss sums: {len(todo)} summed, {len(table)} total, max |g~_raw - snapped| = {worst:.2e}', flush=True)
    return table, worst


# ------------------------------------------------------------- composite g~
def cubic_exp_scalar(a, b, p, r):
    """exponent e in {0,1,2} with ((a + b*omega)/pi)_3 = omega^e, pi above p with omega = r mod pi; -1 if pi | a+b*omega."""
    v = (a + b * r) % p
    if v == 0:
        return -1
    t = pow(v, (p - 1) // 3, p)
    if t == 1:
        return 0
    if t == r % p:
        return 1
    return 2


class FastGaussTable:
    """g~(n) for split-squarefree n by twisted multiplicativity; same formula as zw.GaussTable.gt."""

    def __init__(self, prime_tab):
        self.prime = prime_tab

    def gt(self, n):
        ps, rs = n['ps'], n['rs']
        facs = [self.prime[(p, r)] for p, r in zip(ps, rs)]
        val = 1 + 0j
        for (_, _, g) in facs:
            val *= g
        E = 0
        for i in range(len(facs)):
            ai, bi, _ = facs[i]
            for j in range(i + 1, len(facs)):
                e = cubic_exp_scalar(ai, bi, ps[j], rs[j])
                E -= e                        # conj(omega^e) = omega^{-e}
        return val * W3POW[E % 3]


def gt_array(cols, prime_tab):
    ft = FastGaussTable(prime_tab)
    return np.array([ft.gt(c) for c in cols])
