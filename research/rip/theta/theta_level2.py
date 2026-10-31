"""Are there source-side spikes besides the theta?  Powers of the Gauss sum times angular characters, best class phases.

The off-spike recursion (journal 2026-10-31, "de Faveri's recursion, run off the spikes") needs the dual problem's own
thetas, pulled back through the Poisson map, to be spike-free or harmless.  Pulled back, they are directions of the
form u^j (x/|x|)^l N(x)^{-s} times a class function of x, with u = conj g~(x) the source theta's Gauss sum and
s = 1/2 - 1/q.  Davenport-Hasse predicts that j >= 2 carries an angular Hecke character (no Kubota pole, no spike).

For each (j, l) the script restricts v = u^j (x/|x|)^l N^{-s} to the classes of x (12 classes mod 4, x the parity of
the number of prime factors, x the cube-root class mod 9: up to 72 columns), maps them to the rows, and prints the top
eigenvalue of the normalized class-compressed source Gram (the best class-phase combination) for the matrix of order
q (6: E, kernel mode 0; 3: E^2, mode 2) divided by the same for the masked random matrix (mode 1, mean of two seeds).
A ratio near 1 means no spike in that family.  Gauss sums come from theta_twosided_grow.py's cache ($SCRATCH).

usage: python3 -I theta_level2.py B order [threads]
"""
import os, sys, time
sys.dont_write_bytecode = True
os.environ.setdefault('OMP_NUM_THREADS', '1')
os.environ.setdefault('OPENBLAS_NUM_THREADS', '1')
import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import theta_core as tc          # noqa: E402
import theta_ckernel as ck       # noqa: E402
import theta_util as tu          # noqa: E402

B = L = int(sys.argv[1]); q = int(sys.argv[2])
nth = int(sys.argv[3]) if len(sys.argv) > 3 else 2
modeE = 0 if q == 6 else 2
t0 = time.time()
Tb = tc.build_tables(B, L, verbose=False)
R, S = Tb.R, Tb.S
key = tu.scratch_path('gauss_B%d_L%d.npz' % (B, L) if q == 6 else 'gauss_B%d_L%d_q%d.npz' % (B, L, q))
key2 = tu.scratch_path('srcgauss_q%d_L%d.npz' % (q, L))
if os.path.exists(key) or os.path.exists(key2):
    d = np.load(key if os.path.exists(key) else key2)
    Gsrc, nprime = d['Gsrc'], d['nprime']
else:
    # source Gauss sums of chi^(6/q) (sources have squarefree norm, so every prime factor is split), as in
    # theta_twosided_grow.prime_gauss / gauss_product
    import math
    Ff = tu.free_namespace(Tb)
    ID, pc, zo, sym = Tb.ID, tc.pc, tc.zo, tc.sym
    kk = 6 // q
    Z6 = np.exp(2j * np.pi * np.arange(6) / 6)
    pg = {}

    def prime_gauss(i):
        if i not in pg:
            p, r = ID.split_pr(np.array([i]))
            p = int(p[0]); r = int(r[0])
            a, b = pc.primary_generator(p, r)
            xx = np.arange(1, p, dtype=np.int64)
            code = pc.sym_codes(np.array([p]), np.array([r]), xx, np.zeros_like(xx))[0]
            G = np.sum(Z6[(kk * code.astype(np.int64)) % 6] * np.exp(-2j * np.pi * ((b * xx) % p) / p)) / math.sqrt(p)
            pg[i] = dict(a=a, b=b, G=G, prime=zo.Prime(p, (a, b)))
        return pg[i]
    Gsrc = np.zeros(S, complex); nprime = np.zeros(S, int)
    for j, (a, b, nn) in enumerate(zip(Tb.SA, Tb.SB, Tb.SN)):
        gens = [prime_gauss(int(i)) for i in tu.source_prime_ids(Ff, a, b, nn)]
        g = 1 + 0j
        for gi in gens:
            g *= gi['G']
        for a_ in range(len(gens)):
            for b_ in range(a_ + 1, len(gens)):
                g *= (sym(gens[b_]['prime'], (gens[a_]['a'], gens[a_]['b'])) *
                      sym(gens[a_]['prime'], (gens[b_]['a'], gens[b_]['b']))) ** kk
        Gsrc[j] = g; nprime[j] = len(gens)
    np.savez(key2, Gsrc=Gsrc, nprime=nprime)
    print('  source Gauss sums of order %d computed (%.0fs)' % (q, time.time() - t0), flush=True)
K = ck.Kernel(Tb.T, Tb.LOC, nthreads=nth)
SA, SB = Tb.SA.astype(np.int64), Tb.SB.astype(np.int64)
SN = Tb.SN.astype(float)
x = SA + SB * np.exp(2j * np.pi / 3)
ang = x / np.abs(x)
u = np.conj(Gsrc)
u = np.where(np.abs(u) > 1e-9, u / np.where(np.abs(u) > 1e-9, np.abs(u), 1), 0)
c4 = (SA % 4) * 4 + (SB % 4)
t3 = (SB % 9) // 3
cls = (c4 * 2 + nprime % 2) * 3 + t3
prof = SN ** (-(0.5 - 1.0 / q))


def top_ratio(v):
    X = tu.class_span(cls, v)
    X = X[:, np.linalg.norm(X, axis=0) > 1e-12]
    X = X / np.linalg.norm(X, axis=0, keepdims=True)
    out = []
    for mode, seed in ((modeE, 0), (1, 3), (1, 4)):
        EX = np.zeros((R, X.shape[1]), complex)
        for st in range(0, X.shape[1], 8):
            EX[:, st:st + 8] = K.forward(X[:, st:st + 8], mode=mode, seed=seed)
        G = EX.conj().T @ EX
        out.append(np.linalg.eigvalsh((G + G.conj().T) / 2)[-1])
    return out[0] / np.mean(out[1:]), X.shape[1]


js = range(6) if q == 6 else range(3)
print('order %d, B = L = %d: R=%d S=%d; top of the class-compressed Gram of u^j (x/|x|)^l N^-%.3f over the masked null'
      % (q, B, R, S, 0.5 - 1.0 / q), flush=True)
print('   j \\ l ' + ''.join('%8d' % l for l in range(-3, 4)), flush=True)
for j in js:
    row = []
    for l in range(-3, 4):
        r, ncol = top_ratio(u ** j * ang ** l * prof)
        row.append(r)
    print('   %3d   ' % j + ''.join('%8.3f' % r for r in row) + '   (%d classes, %.0fs)' % (ncol, time.time() - t0),
          flush=True)
print('done in %.0fs' % (time.time() - t0))
